module

public import Veir.IR.Simp
public import Veir.IR.OpInfo
public import Veir.Verifier.Basic
public import Veir.Dialects.ModArith.Properties
public import Veir.ConstantMaterialization
public import Veir.Interpreter.RuntimeValue.Basic
public import Veir.Interpreter.Interp
meta import Veir.Meta.OpCode

open Veir.Data

namespace Veir

public section

/--
The `mod_arith` dialect. `add`, `sub`, `mul` and `constant` are the ops HEIR and
prime-ir share, with the same generic form; the remaining ones are prime-ir's
(`ModArithOps.td` at fractalyze/prime-ir `fc4261887`).
-/
@[opcodes]
inductive Mod_Arith where
| add
| constant
| mul
| sub
| bitcast
| mont_reduce
| to_mont
| from_mont
| cmp
| negate
| square
| mont_square
| inverse
| double
| mont_inverse
| mont_mul
| barrett_mul
deriving Inhabited, Repr, Hashable, DecidableEq

@[expose, properties_of]
def Mod_Arith.propertiesOf (op : Mod_Arith) : Type :=
match op with
| .constant => ModArithConstantProperties
| .cmp => CmpPredicateProperties
| .add | .sub | .mul | .bitcast | .mont_reduce | .to_mont | .from_mont | .negate | .square
| .mont_square | .inverse | .double | .mont_inverse | .mont_mul | .barrett_mul => Unit

def Mod_Arith.fromAttrDict
    (op : Mod_Arith) (attrDict : Std.HashMap ByteArray Attribute) :
    Except String (Mod_Arith.propertiesOf op) := by
  cases op
  case constant => exact ModArithConstantProperties.fromAttrDict attrDict
  case cmp => exact CmpPredicateProperties.fromAttrDict "mod_arith.cmp" attrDict
  all_goals exact .ok ()

def Mod_Arith.toAttrDict
    (op : Mod_Arith) (props : Mod_Arith.propertiesOf op) :
    Std.HashMap ByteArray Attribute :=
  match op with
  | .constant =>
    (Std.HashMap.emptyWithCapacity 2).insert
      "value".toUTF8 (Attribute.integerAttr props.value)
  | .cmp => CmpPredicateProperties.toAttrDict props
  | _ => Std.HashMap.emptyWithCapacity 0

@[get_effects]
def Mod_Arith.getEffects
    (_op : Mod_Arith) (_props : Mod_Arith.propertiesOf _op) : MemoryEffects :=
  .none

def Mod_Arith.isConstantLike (op : Mod_Arith) : Bool :=
  match op with
  | .constant => true
  | _ => false

def Mod_Arith.hasSSADominance (_op : Mod_Arith) (_index : Nat) : Bool :=
  true

#generate_dialect Mod_Arith

instance : IsOpCode Mod_Arith where
  fromName := Mod_Arith.fromName
  name := Mod_Arith.name
  propertiesOf := Mod_Arith.propertiesOf
  fromAttrDict := Mod_Arith.fromAttrDict
  toAttrDict := Mod_Arith.toAttrDict

/--
Materialize concrete modular-integer fold results.
-/
def Mod_Arith.materializeConstant {OpInfo : Type} [HasOpInfo OpInfo] [HasDialect OpInfo Mod_Arith]
    (_op : Mod_Arith) (value : RuntimeValue) (type : TypeAttr) : Option (Materialized OpInfo) :=
  match value, type.val with
  | .int bw (.val value), .modArithType modType =>
    if bw = modType.modulus.type.bitwidth then
      some (.of Mod_Arith.constant
        (ModArithConstantProperties.mk
          (IntegerAttr.mk (Int.ofNat value.toNat) modType.modulus.type)))
    else none
  | _, _ => none

def TypeAttr.verifyModArithType (ty : TypeAttr) (msg : String) : Except String ModArithType :=
  match ty.val with
  | .modArithType type => do
    let modulus := type.modulus.value
    let bitWidth := type.modulus.type.bitwidth
    if modulus ≤ 0 then
      throw s!"{msg} but found invalid ModArithType type: modulus {modulus} must be positive."
    if modulus ≥ (2 ^ bitWidth) then
      throw s!"{msg} but found invalid ModArithType type: modulus {modulus} does not fit into the underlying storage type 'i{bitWidth}'."
    pure type
  | type => throw s!"{msg} but found {type} instead."

def OperationPtr.verifyModArithBinOp {OpInfo : Type} [IsOpCode OpInfo]
    (op : OperationPtr) (ctx : WfIRContext OpInfo)
    (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  op.verifyPlainOpCounts ctx opIn 2 1
  let instrName := String.fromUTF8! (IsOpCode.name (op.getOpType ctx.raw opIn))
  let operandType ← op.verifyOperandTypesMatch ctx 0 1
    s!"{instrName}: Expected operands to have the same type"
  op.verifyResultTypeMatches ctx operandType
    s!"{instrName}: Expected result type to match operand type"
  let _ ← operandType.verifyModArithType s!"{instrName}: Expected ModArithType"

def OperationPtr.verifyModArithConstantOp {OpInfo : Type} [IsOpCode OpInfo]
    [HasDialect OpInfo Mod_Arith] (op : OperationPtr) (ctx : WfIRContext OpInfo)
    (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  op.verifyPlainOpCounts ctx opIn 0 1
  let instrName := String.fromUTF8! (IsOpCode.name (op.getOpType ctx.raw opIn))
  let mat ← ((op.getResult 0).getType! ctx.raw).verifyModArithType
    s!"{instrName}: Expected result to have ModArithType"
  let value := (op.getProperties! ctx.raw Mod_Arith.constant).value.value
  let bw := mat.modulus.type.bitwidth
  -- Slightly odd range because the storage type is signless.
  if value < -(2 ^ (bw - 1) : Int) ∨ (2 ^ bw : Int) ≤ value then
    throw s!"{instrName}: constant value {value} does not fit in storage type 'i{bw}'."

/--
The element type of a shaped type (`tensor`, `vector`, `memref`), or the type
itself when it is not shaped.
-/
def Attribute.shapedElementType (ty : Attribute) : Attribute :=
  match ty with
  | .rankedTensorType t => t.elementType
  | .vectorType t => t.elementType
  | .memrefType t => t.elementType
  | t => t

/-- The shape of a shaped type, or `none` for a scalar type. -/
def Attribute.shapedShape (ty : Attribute) : Option (Array Nat) :=
  match ty with
  | .rankedTensorType t => some t.shape
  | .vectorType t => some t.shape
  | .memrefType t => some t.shape
  | _ => none

def ModArithType.verifyWellFormed (type : ModArithType) (msg : String) :
    Except String ModArithType := do
  let modulus := type.modulus.value
  let bitWidth := type.modulus.type.bitwidth
  if modulus ≤ 0 then
    throw s!"{msg} but found invalid ModArithType type: modulus {modulus} must be positive."
  if modulus ≥ (2 ^ bitWidth) then
    throw s!"{msg} but found invalid ModArithType type: modulus {modulus} does not fit into the underlying storage type 'i{bitWidth}'."
  pure type

/--
Check that `ty` is `ModArithLike`: a `!mod_arith.int` or a shaped container of one.
Returns the element type.
-/
def Attribute.verifyModArithLike (ty : Attribute) (msg : String) : Except String ModArithType :=
  match ty.shapedElementType with
  | .modArithType type => type.verifyWellFormed msg
  | _ => throw s!"{msg} but found {ty} instead."

/-- The storage width of an integer or `mod_arith` element type. -/
def Attribute.modArithOrIntegerWidth? (ty : Attribute) : Option Nat :=
  match ty.shapedElementType with
  | .modArithType type => some type.bitwidth
  | .integerType type => some type.bitwidth
  | _ => none

def OperationPtr.verifyModArithLikeUnaryOp {OpInfo : Type} [IsOpCode OpInfo]
    (op : OperationPtr) (ctx : WfIRContext OpInfo)
    (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  op.verifyPlainOpCounts ctx opIn 1 1
  let instrName := String.fromUTF8! (IsOpCode.name (op.getOpType ctx.raw opIn))
  let operandType := (op.getOperand! ctx.raw 0).getType! ctx.raw
  op.verifyResultTypeMatches ctx operandType
    s!"{instrName}: Expected result type to match operand type"
  let _ ← operandType.val.verifyModArithLike s!"{instrName}: Expected mod_arith-like operand"

def OperationPtr.verifyModArithLikeBinOp {OpInfo : Type} [IsOpCode OpInfo]
    (op : OperationPtr) (ctx : WfIRContext OpInfo)
    (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  op.verifyPlainOpCounts ctx opIn 2 1
  let instrName := String.fromUTF8! (IsOpCode.name (op.getOpType ctx.raw opIn))
  let operandType ← op.verifyOperandTypesMatch ctx 0 1
    s!"{instrName}: Expected operands to have the same type"
  op.verifyResultTypeMatches ctx operandType
    s!"{instrName}: Expected result type to match operand type"
  let _ ← operandType.val.verifyModArithLike s!"{instrName}: Expected mod_arith-like operands"

/--
`to_mont` (`toMont = true`) and `from_mont`: the operand and result have the same
modulus and shape, and the result flips the Montgomery flag of the operand.
-/
def OperationPtr.verifyModArithMontConversion {OpInfo : Type} [IsOpCode OpInfo]
    (op : OperationPtr) (ctx : WfIRContext OpInfo)
    (opIn : op.InBounds ctx.raw) (toMont : Bool) : Except String PUnit := do
  op.verifyPlainOpCounts ctx opIn 1 1
  let instrName := String.fromUTF8! (IsOpCode.name (op.getOpType ctx.raw opIn))
  let inType := ((op.getOperand! ctx.raw 0).getType! ctx.raw).val
  let outType := ((op.getResult 0).getType! ctx.raw).val
  let input ← inType.verifyModArithLike s!"{instrName}: Expected mod_arith-like operand"
  let output ← outType.verifyModArithLike s!"{instrName}: Expected mod_arith-like result"
  if input.modulus ≠ output.modulus then
    throw s!"{instrName}: Expected operand and result to have the same modulus"
  if inType.shapedShape ≠ outType.shapedShape then
    throw s!"{instrName}: Expected operand and result to have the same shape"
  if input.isMontgomery = toMont ∨ output.isMontgomery ≠ toMont then
    throw s!"{instrName}: Expected the result to flip the operand's Montgomery flag"

/--
`bitcast`: each side is `ModArithLike` or a signless integer (container), with equal
storage width and shape.
-/
def OperationPtr.verifyModArithBitcast {OpInfo : Type} [IsOpCode OpInfo]
    (op : OperationPtr) (ctx : WfIRContext OpInfo)
    (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  op.verifyPlainOpCounts ctx opIn 1 1
  let instrName := String.fromUTF8! (IsOpCode.name (op.getOpType ctx.raw opIn))
  let inType := ((op.getOperand! ctx.raw 0).getType! ctx.raw).val
  let outType := ((op.getResult 0).getType! ctx.raw).val
  let some inWidth := inType.modArithOrIntegerWidth?
    | throw s!"{instrName}: Expected a mod_arith-like or integer operand"
  let some outWidth := outType.modArithOrIntegerWidth?
    | throw s!"{instrName}: Expected a mod_arith-like or integer result"
  if inWidth ≠ outWidth then
    throw s!"{instrName}: Expected operand and result storage widths to agree"
  if inType.shapedShape ≠ outType.shapedShape then
    throw s!"{instrName}: Expected operand and result to have the same shape"

/-- `mont_reduce`: two integer operands of one type, and a `ModArithLike` result. -/
def OperationPtr.verifyModArithMontReduce {OpInfo : Type} [IsOpCode OpInfo]
    (op : OperationPtr) (ctx : WfIRContext OpInfo)
    (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  op.verifyPlainOpCounts ctx opIn 2 1
  let instrName := String.fromUTF8! (IsOpCode.name (op.getOpType ctx.raw opIn))
  let operandType ← op.verifyOperandTypesMatch ctx 0 1
    s!"{instrName}: Expected operands to have the same type"
  let .integerType _ := operandType.val.shapedElementType
    | throw s!"{instrName}: Expected integer operands"
  let _ ← ((op.getResult 0).getType! ctx.raw).val.verifyModArithLike
    s!"{instrName}: Expected mod_arith-like result"

/-- `cmp`: two `ModArithLike` operands of one type and an `i1` (container) result. -/
def OperationPtr.verifyModArithCmp {OpInfo : Type} [IsOpCode OpInfo]
    (op : OperationPtr) (ctx : WfIRContext OpInfo)
    (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  op.verifyPlainOpCounts ctx opIn 2 1
  let instrName := String.fromUTF8! (IsOpCode.name (op.getOpType ctx.raw opIn))
  let operandType ← op.verifyOperandTypesMatch ctx 0 1
    s!"{instrName}: Expected operands to have the same type"
  let _ ← operandType.val.verifyModArithLike s!"{instrName}: Expected mod_arith-like operands"
  let resultType := ((op.getResult 0).getType! ctx.raw).val
  let .integerType ⟨1⟩ := resultType.shapedElementType
    | throw s!"{instrName}: Expected i1 result"
  if resultType.shapedShape ≠ operandType.val.shapedShape then
    throw s!"{instrName}: Expected result to have the shape of the operands"

/--
Verify the local invariants of a `mod_arith` operation in any operation-info
type containing the `mod_arith` dialect.
-/
def Mod_Arith.verifyLocalInvariants {OpInfo : Type} [IsOpCode OpInfo]
    [HasDialect OpInfo Mod_Arith] (opType : Mod_Arith) (op : OperationPtr)
    (ctx : WfIRContext OpInfo) (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  match opType with
  | .add | .mul | .sub => do
    op.verifyModArithBinOp ctx opIn
    pure ()
  | .constant => do
    op.verifyModArithConstantOp ctx opIn
    pure ()
  | .negate | .square | .mont_square | .inverse | .double | .mont_inverse =>
    op.verifyModArithLikeUnaryOp ctx opIn
  | .mont_mul | .barrett_mul =>
    op.verifyModArithLikeBinOp ctx opIn
  | .to_mont => op.verifyModArithMontConversion ctx opIn true
  | .from_mont => op.verifyModArithMontConversion ctx opIn false
  | .bitcast => op.verifyModArithBitcast ctx opIn
  | .mont_reduce => op.verifyModArithMontReduce ctx opIn
  | .cmp => op.verifyModArithCmp ctx opIn

/-- Matches two integer operands and casts them to the expected bitwidth `bw`. -/
private def ModArith.binaryOperands (bw : Nat) (operands : Array RuntimeValue) :
    Option (LLVM.Int bw × LLVM.Int bw) := do
  let [RuntimeValue.int bw' lhs, RuntimeValue.int bw'' rhs] := operands.toList | none
  if h : bw' = bw ∧ bw'' = bw then
    return (lhs.cast h.left, rhs.cast h.right)
  else
    none

def ModArith.interpretOp' (opType : Veir.Mod_Arith) (properties : propertiesOf opType)
    (resultTypes : Array TypeAttr) (operands : Array RuntimeValue) (_blockOperands : Array BlockPtr)
    : Interp ((Array RuntimeValue) × Option ControlFlowAction) :=
  match opType with
  | .constant => do
    let some resType := resultTypes[0]? | none
    let .modArithType ⟨⟨mod, ⟨bw, _⟩⟩, false⟩ := resType.val | none
    let res := LLVM.Int.constant bw (properties.value.value % mod)
    return (#[RuntimeValue.int bw res], none)
  | .add => do
    let some resType := resultTypes[0]? | none
    let .modArithType ⟨⟨mod, ⟨bw, _⟩⟩, false⟩ := resType.val | none
    let some (lhs, rhs) := ModArith.binaryOperands bw operands | none
    let res :=
      match lhs.toNat?, rhs.toNat? with
      | some lhs, some rhs => LLVM.Int.constant bw ((lhs + rhs) % mod)
      | _, _ => LLVM.Int.poison
    return (#[RuntimeValue.int bw res], none)
  | .sub => do
    let some resType := resultTypes[0]? | none
    let .modArithType ⟨⟨mod, ⟨bw, _⟩⟩, false⟩ := resType.val | none
    let some (lhs, rhs) := ModArith.binaryOperands bw operands | none
    let res :=
      match lhs.toNat?, rhs.toNat? with
      | some lhs, some rhs => LLVM.Int.constant bw ((Int.ofNat lhs - rhs) % mod)
      | _, _ => LLVM.Int.poison
    return (#[RuntimeValue.int bw res], none)
  | .mul => do
    let some resType := resultTypes[0]? | none
    let .modArithType ⟨⟨mod, ⟨bw, _⟩⟩, false⟩ := resType.val | none
    let some (lhs, rhs) := ModArith.binaryOperands bw operands | none
    let res :=
      match lhs.toNat?, rhs.toNat? with
      | some lhs, some rhs => LLVM.Int.constant bw ((lhs * rhs) % mod)
      | _, _ => LLVM.Int.poison
    return (#[RuntimeValue.int bw res], none)
  -- The prime-ir ops and Montgomery-flagged types have no semantics yet.
  | _ => none

instance : HasOpInfo Mod_Arith where
  verifyLocalInvariants := Mod_Arith.verifyLocalInvariants
  getEffects := Mod_Arith.getEffects
  isConstantLike := Mod_Arith.isConstantLike
  hasSSADominance := Mod_Arith.hasSSADominance
