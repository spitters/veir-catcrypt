module

public import Veir.IR.Simp
public import Veir.IR.OpInfo
public import Veir.Verifier.Basic
public import Veir.Dialects.Field.Properties
public import Veir.Dialects.ModArith.OpInfo
meta import Veir.Meta.OpCode

namespace Veir

public section

/--
The prime-ir `field` dialect over prime fields `!field.pf` and extension fields
`!field.ef` (`FieldOps.td` at fractalyze/prime-ir `fc4261887`). Binary fields
(`!field.bf`) are not modelled.
-/
@[opcodes]
inductive Field where
| constant
| bitcast
| cmp
| to_mont
| from_mont
| inverse
| double
| square
| negate
| add
| sub
| mul
| powui
| ext_to_coeffs
| ext_from_coeffs
deriving Inhabited, Repr, Hashable, DecidableEq

@[expose, properties_of]
def Field.propertiesOf (op : Field) : Type :=
match op with
| .constant => FieldConstantProperties
| .cmp => CmpPredicateProperties
| .powui => FieldPowUIProperties
| .bitcast | .to_mont | .from_mont | .inverse | .double | .square | .negate
| .add | .sub | .mul | .ext_to_coeffs | .ext_from_coeffs => Unit

def Field.fromAttrDict
    (op : Field) (attrDict : Std.HashMap ByteArray Attribute) :
    Except String (Field.propertiesOf op) := by
  cases op
  case constant => exact FieldConstantProperties.fromAttrDict attrDict
  case cmp => exact CmpPredicateProperties.fromAttrDict "field.cmp" attrDict
  case powui => exact FieldPowUIProperties.fromAttrDict attrDict
  all_goals exact .ok ()

def Field.toAttrDict
    (op : Field) (props : Field.propertiesOf op) :
    Std.HashMap ByteArray Attribute :=
  match op with
  | .constant =>
    (Std.HashMap.emptyWithCapacity 1).insert "value".toUTF8 props.value
  | .cmp => CmpPredicateProperties.toAttrDict props
  | .powui => FieldPowUIProperties.toAttrDict props
  | _ => Std.HashMap.emptyWithCapacity 0

@[get_effects]
def Field.getEffects
    (_op : Field) (_props : Field.propertiesOf _op) : MemoryEffects :=
  .none

def Field.isConstantLike (op : Field) : Bool :=
  match op with
  | .constant => true
  | _ => false

def Field.hasSSADominance (_op : Field) (_index : Nat) : Bool :=
  true

#generate_dialect Field

instance : IsOpCode Field where
  fromName := Field.fromName
  name := Field.name
  propertiesOf := Field.propertiesOf
  fromAttrDict := Field.fromAttrDict
  toAttrDict := Field.toAttrDict

/--
The base fields below an extension field type, innermost last; empty for any other
type. Towers deeper than eight levels are truncated.
-/
def Attribute.fieldTowerBases (ty : Attribute) : List Attribute :=
  go 8 ty
where
  go : Nat → Attribute → List Attribute
  | 0, _ => []
  | n + 1, .extensionFieldType t => t.base :: go n t.base
  | _, _ => []

def PrimeFieldType.verifyWellFormed (type : PrimeFieldType) (msg : String) :
    Except String PUnit := do
  let modulus := type.modulus.value
  let bitWidth := type.modulus.type.bitwidth
  if modulus ≤ 0 then
    throw s!"{msg} but found invalid prime field type: modulus {modulus} must be positive."
  if modulus ≥ (2 ^ bitWidth) then
    throw s!"{msg} but found invalid prime field type: modulus {modulus} does not fit into the underlying storage type 'i{bitWidth}'."

/--
Check that `ty` is `FieldLike`: a `!field.pf` or `!field.ef` element, or a shaped
container of one. Returns the element type.
-/
def Attribute.verifyFieldLike (ty : Attribute) (msg : String) : Except String Attribute :=
  match ty.shapedElementType with
  | .primeFieldType type => do
    type.verifyWellFormed msg
    pure (.primeFieldType type)
  | .extensionFieldType type => do
    if type.degree < 2 then
      throw s!"{msg} but found extension field degree {type.degree}, expected at least 2."
    match type.base with
    | .primeFieldType _ | .extensionFieldType _ => pure (.extensionFieldType type)
    | base => throw s!"{msg} but found extension field over {base}, expected a field base."
  | _ => throw s!"{msg} but found {ty} instead."

def OperationPtr.verifyFieldUnaryOp {OpInfo : Type} [IsOpCode OpInfo]
    (op : OperationPtr) (ctx : WfIRContext OpInfo)
    (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  op.verifyPlainOpCounts ctx opIn 1 1
  let instrName := String.fromUTF8! (IsOpCode.name (op.getOpType ctx.raw opIn))
  let operandType := (op.getOperand! ctx.raw 0).getType! ctx.raw
  op.verifyResultTypeMatches ctx operandType
    s!"{instrName}: Expected result type to match operand type"
  let _ ← operandType.val.verifyFieldLike s!"{instrName}: Expected field-like operand"

/--
`add`, `sub`, `mul`: the result has the type of one operand; the other operand has
the same type or is a base field of it (`field.add %ext, %base`).
-/
def OperationPtr.verifyFieldBinOp {OpInfo : Type} [IsOpCode OpInfo]
    (op : OperationPtr) (ctx : WfIRContext OpInfo)
    (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  op.verifyPlainOpCounts ctx opIn 2 1
  let instrName := String.fromUTF8! (IsOpCode.name (op.getOpType ctx.raw opIn))
  let lhs := ((op.getOperand! ctx.raw 0).getType! ctx.raw).val
  let rhs := ((op.getOperand! ctx.raw 1).getType! ctx.raw).val
  let result := ((op.getResult 0).getType! ctx.raw).val
  let _ ← lhs.verifyFieldLike s!"{instrName}: Expected field-like lhs"
  let _ ← rhs.verifyFieldLike s!"{instrName}: Expected field-like rhs"
  if lhs = rhs then
    if result ≠ lhs then
      throw s!"{instrName}: Expected result type to match operand type"
  else
    let other ←
      if result = lhs then pure rhs
      else if result = rhs then pure lhs
      else throw s!"{instrName}: Expected result type to match one operand type"
    let bases := result.shapedElementType.fieldTowerBases
    unless bases.contains other.shapedElementType do
      throw s!"{instrName}: Expected {other} to be a base field of {result}"

def OperationPtr.verifyFieldConstant {OpInfo : Type} [IsOpCode OpInfo]
    [HasDialect OpInfo Field] (op : OperationPtr) (ctx : WfIRContext OpInfo)
    (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  op.verifyPlainOpCounts ctx opIn 0 1
  let instrName := String.fromUTF8! (IsOpCode.name (op.getOpType ctx.raw opIn))
  let resultType := ((op.getResult 0).getType! ctx.raw).val
  let element ← resultType.verifyFieldLike s!"{instrName}: Expected field-like result"
  match (op.getProperties! ctx.raw Field.constant).value, element, resultType.shapedShape with
  | .integerAttr value, .primeFieldType pf, none =>
    if value.type ≠ pf.modulus.type then
      throw s!"{instrName}: Expected value of the storage type {pf.modulus.type}"
  | .integerAttr _, _, _ =>
    throw s!"{instrName}: an integer value requires a scalar prime field result"
  | .denseElementsAttr _, _, _ => pure ()
  | value, _, _ => throw s!"{instrName}: unexpected value {value}"

def OperationPtr.verifyFieldCmp {OpInfo : Type} [IsOpCode OpInfo]
    (op : OperationPtr) (ctx : WfIRContext OpInfo)
    (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  op.verifyPlainOpCounts ctx opIn 2 1
  let instrName := String.fromUTF8! (IsOpCode.name (op.getOpType ctx.raw opIn))
  let operandType ← op.verifyOperandTypesMatch ctx 0 1
    s!"{instrName}: Expected operands to have the same type"
  let _ ← operandType.val.verifyFieldLike s!"{instrName}: Expected field-like operands"
  let resultType := ((op.getResult 0).getType! ctx.raw).val
  let .integerType ⟨1⟩ := resultType.shapedElementType
    | throw s!"{instrName}: Expected i1 result"
  if resultType.shapedShape ≠ operandType.val.shapedShape then
    throw s!"{instrName}: Expected result to have the shape of the operands"

/--
`to_mont` (`toMont = true`) and `from_mont`: field-like operand and result of the
same shape; on prime fields, the same modulus with the Montgomery flag flipped.
-/
def OperationPtr.verifyFieldMontConversion {OpInfo : Type} [IsOpCode OpInfo]
    (op : OperationPtr) (ctx : WfIRContext OpInfo)
    (opIn : op.InBounds ctx.raw) (toMont : Bool) : Except String PUnit := do
  op.verifyPlainOpCounts ctx opIn 1 1
  let instrName := String.fromUTF8! (IsOpCode.name (op.getOpType ctx.raw opIn))
  let inType := ((op.getOperand! ctx.raw 0).getType! ctx.raw).val
  let outType := ((op.getResult 0).getType! ctx.raw).val
  let input ← inType.verifyFieldLike s!"{instrName}: Expected field-like operand"
  let output ← outType.verifyFieldLike s!"{instrName}: Expected field-like result"
  if inType.shapedShape ≠ outType.shapedShape then
    throw s!"{instrName}: Expected operand and result to have the same shape"
  match input, output with
  | .primeFieldType i, .primeFieldType o =>
    if i.modulus ≠ o.modulus then
      throw s!"{instrName}: Expected operand and result to have the same modulus"
    if i.isMontgomery = toMont ∨ o.isMontgomery ≠ toMont then
      throw s!"{instrName}: Expected the result to flip the operand's Montgomery flag"
  | .extensionFieldType i, .extensionFieldType o =>
    if i.degree ≠ o.degree then
      throw s!"{instrName}: Expected operand and result to have the same degree"
  | _, _ => throw s!"{instrName}: Expected operand and result of the same field kind"

/-- `powui`: a field-like base, an integer exponent, and a result of the base type. -/
def OperationPtr.verifyFieldPowUI {OpInfo : Type} [IsOpCode OpInfo]
    (op : OperationPtr) (ctx : WfIRContext OpInfo)
    (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  op.verifyPlainOpCounts ctx opIn 2 1
  let instrName := String.fromUTF8! (IsOpCode.name (op.getOpType ctx.raw opIn))
  let baseType := (op.getOperand! ctx.raw 0).getType! ctx.raw
  let _ ← baseType.val.verifyFieldLike s!"{instrName}: Expected field-like base"
  let .integerType _ := ((op.getOperand! ctx.raw 1).getType! ctx.raw).val.shapedElementType
    | throw s!"{instrName}: Expected an integer exponent"
  op.verifyResultTypeMatches ctx baseType
    s!"{instrName}: Expected result type to match base type"

/-- `ext_to_coeffs`: one extension field operand and one result per coefficient. -/
def OperationPtr.verifyFieldExtToCoeffs {OpInfo : Type} [IsOpCode OpInfo]
    (op : OperationPtr) (ctx : WfIRContext OpInfo)
    (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  let instrName := String.fromUTF8! (IsOpCode.name (op.getOpType ctx.raw opIn))
  if op.getNumOperands ctx.raw opIn ≠ 1 then
    throw s!"{instrName}: Expected 1 operand(s)"
  let .extensionFieldType ef := ((op.getOperand! ctx.raw 0).getType! ctx.raw).val
    | throw s!"{instrName}: Expected an extension field operand"
  op.verifyPlainOpCounts ctx opIn 1 ef.degree

/-- `ext_from_coeffs`: one operand per coefficient and one extension field result. -/
def OperationPtr.verifyFieldExtFromCoeffs {OpInfo : Type} [IsOpCode OpInfo]
    (op : OperationPtr) (ctx : WfIRContext OpInfo)
    (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  let instrName := String.fromUTF8! (IsOpCode.name (op.getOpType ctx.raw opIn))
  if op.getNumResults ctx.raw opIn ≠ 1 then
    throw s!"{instrName}: Expected 1 result(s)"
  let .extensionFieldType ef := ((op.getResult 0).getType! ctx.raw).val
    | throw s!"{instrName}: Expected an extension field result"
  op.verifyPlainOpCounts ctx opIn ef.degree 1

/--
Verify the local invariants of a `field` operation in any operation-info type
containing the `field` dialect.
-/
def Field.verifyLocalInvariants {OpInfo : Type} [IsOpCode OpInfo]
    [HasDialect OpInfo Field] (opType : Field) (op : OperationPtr)
    (ctx : WfIRContext OpInfo) (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  match opType with
  | .constant => op.verifyFieldConstant ctx opIn
  | .bitcast => op.verifyPlainOpCounts ctx opIn 1 1
  | .cmp => op.verifyFieldCmp ctx opIn
  | .to_mont => op.verifyFieldMontConversion ctx opIn true
  | .from_mont => op.verifyFieldMontConversion ctx opIn false
  | .inverse | .double | .square | .negate => op.verifyFieldUnaryOp ctx opIn
  | .add | .sub | .mul => op.verifyFieldBinOp ctx opIn
  | .powui => op.verifyFieldPowUI ctx opIn
  | .ext_to_coeffs => op.verifyFieldExtToCoeffs ctx opIn
  | .ext_from_coeffs => op.verifyFieldExtFromCoeffs ctx opIn

instance : HasOpInfo Field where
  verifyLocalInvariants := Field.verifyLocalInvariants
  getEffects := Field.getEffects
  isConstantLike := Field.isConstantLike
  hasSSADominance := Field.hasSSADominance

end

end Veir
