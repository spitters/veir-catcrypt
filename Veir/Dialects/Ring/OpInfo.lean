module

public import Veir.IR.Simp
public import Veir.IR.OpInfo
public import Veir.Verifier.Basic
public import Veir.Dialects.Ring.Properties
meta import Veir.Meta.OpCode

namespace Veir

public section

/--
The prime-ir `ring` dialect over the quotient rings `!ring.rq` in RNS form
(`RingOps.td` at fractalyze/prime-ir `fc4261887`).
-/
@[opcodes]
inductive Ring where
| from_tensor
| to_tensor
| from_limbs
| to_limbs
| automorphism
| rescale
| add
| sub
| negate
| mul
| base_convert
deriving Inhabited, Repr, Hashable, DecidableEq

@[expose, properties_of]
def Ring.propertiesOf (op : Ring) : Type :=
match op with
| .automorphism => RingAutomorphismProperties
| .from_tensor | .to_tensor | .from_limbs | .to_limbs | .rescale | .add | .sub | .negate
| .mul | .base_convert => Unit

def Ring.fromAttrDict
    (op : Ring) (attrDict : Std.HashMap ByteArray Attribute) :
    Except String (Ring.propertiesOf op) := by
  cases op
  case automorphism => exact RingAutomorphismProperties.fromAttrDict attrDict
  all_goals exact .ok ()

def Ring.toAttrDict
    (op : Ring) (props : Ring.propertiesOf op) :
    Std.HashMap ByteArray Attribute :=
  match op with
  | .automorphism => RingAutomorphismProperties.toAttrDict props
  | _ => Std.HashMap.emptyWithCapacity 0

@[get_effects]
def Ring.getEffects
    (_op : Ring) (_props : Ring.propertiesOf _op) : MemoryEffects :=
  .none

def Ring.isConstantLike (_op : Ring) : Bool :=
  false

def Ring.hasSSADominance (_op : Ring) (_index : Nat) : Bool :=
  true

#generate_dialect Ring

instance : IsOpCode Ring where
  fromName := Ring.fromName
  name := Ring.name
  propertiesOf := Ring.propertiesOf
  fromAttrDict := Ring.fromAttrDict
  toAttrDict := Ring.toAttrDict

/-- The `!ring.rq` type `ty`, or an error naming `msg`. -/
def Attribute.verifyRqType (ty : Attribute) (msg : String) : Except String RqType :=
  match ty with
  | .rqType type => pure type
  | _ => throw s!"{msg} but found {ty} instead."

/-- The ring degree `N` of a `!ring.rq` type. -/
def RqType.degree (type : RqType) : Nat :=
  type.ringDegree.value.toNat

/--
`add`, `sub`, `mul` (`evalOnly = true`) and `negate` (`arity = 1`): operands and
result of one `!ring.rq` type. `mul` requires the evaluation basis, where the product
is pointwise.
-/
def OperationPtr.verifyRingElementwiseOp {OpInfo : Type} [IsOpCode OpInfo]
    (op : OperationPtr) (ctx : WfIRContext OpInfo)
    (opIn : op.InBounds ctx.raw) (arity : Nat) (evalOnly : Bool := false) :
    Except String PUnit := do
  op.verifyPlainOpCounts ctx opIn arity 1
  let instrName := String.fromUTF8! (IsOpCode.name (op.getOpType ctx.raw opIn))
  let operandType := (op.getOperand! ctx.raw 0).getType! ctx.raw
  if arity = 2 then
    discard <| op.verifyOperandTypesMatch ctx 0 1
      s!"{instrName}: Expected operands to have the same type"
  op.verifyResultTypeMatches ctx operandType
    s!"{instrName}: Expected result type to match operand type"
  let ring ← operandType.val.verifyRqType s!"{instrName}: Expected a !ring.rq operand"
  if evalOnly ∧ ring.domain ≠ .eval then
    throw s!"{instrName}: operands must be in the eval basis"

/-- `automorphism`: `negate`'s typing, and a positive odd exponent. -/
def OperationPtr.verifyRingAutomorphism {OpInfo : Type} [IsOpCode OpInfo]
    [HasDialect OpInfo Ring] (op : OperationPtr) (ctx : WfIRContext OpInfo)
    (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  op.verifyRingElementwiseOp ctx opIn 1
  let instrName := String.fromUTF8! (IsOpCode.name (op.getOpType ctx.raw opIn))
  let g := (op.getProperties! ctx.raw Ring.automorphism).exponent.value
  if g ≤ 0 ∨ g % 2 = 0 then
    throw s!"{instrName}: exponent must be a positive odd integer, got {g}"

/--
`from_tensor` (`fromTensor = true`) and `to_tensor`: a `!ring.rq` value and its
`L × N` residue tensor of the ring's storage type, `L` the number of moduli.
-/
def OperationPtr.verifyRingResidueTensor {OpInfo : Type} [IsOpCode OpInfo]
    (op : OperationPtr) (ctx : WfIRContext OpInfo)
    (opIn : op.InBounds ctx.raw) (fromTensor : Bool) : Except String PUnit := do
  op.verifyPlainOpCounts ctx opIn 1 1
  let instrName := String.fromUTF8! (IsOpCode.name (op.getOpType ctx.raw opIn))
  let input := ((op.getOperand! ctx.raw 0).getType! ctx.raw).val
  let output := ((op.getResult 0).getType! ctx.raw).val
  let (ringTy, tensorTy) := if fromTensor then (output, input) else (input, output)
  let ring ← ringTy.verifyRqType s!"{instrName}: Expected a !ring.rq type"
  let .rankedTensorType tensor := tensorTy
    | throw s!"{instrName}: Expected a ranked tensor but found {tensorTy} instead."
  if tensor.shape ≠ #[ring.moduli.size, ring.degree] then
    throw s!"{instrName}: residue tensor must be {ring.moduli.size}x{ring.degree}, but got {tensorTy}"
  if tensor.elementType ≠ .integerType ring.storageType then
    throw s!"{instrName}: residue tensor element must be the ring's storage type {ring.storageType}"

/--
`from_limbs` (`fromLimbs = true`) and `to_limbs`: a `!ring.rq` value and one 1-D
tensor of `N` prime field elements per modulus, with modulus `qᵢ`, no Montgomery
flag and the ring's storage width.
-/
def OperationPtr.verifyRingLimbs {OpInfo : Type} [IsOpCode OpInfo]
    (op : OperationPtr) (ctx : WfIRContext OpInfo)
    (opIn : op.InBounds ctx.raw) (fromLimbs : Bool) : Except String PUnit := do
  let instrName := String.fromUTF8! (IsOpCode.name (op.getOpType ctx.raw opIn))
  let ringTy ←
    if fromLimbs then do
      if op.getNumResults ctx.raw opIn ≠ 1 then
        throw s!"{instrName}: Expected 1 result(s)"
      pure ((op.getResult 0).getType! ctx.raw).val
    else do
      if op.getNumOperands ctx.raw opIn ≠ 1 then
        throw s!"{instrName}: Expected 1 operand(s)"
      pure ((op.getOperand! ctx.raw 0).getType! ctx.raw).val
  let ring ← ringTy.verifyRqType s!"{instrName}: Expected a !ring.rq type"
  let numLimbs := ring.moduli.size
  let limbs : Array Attribute ←
    if fromLimbs then do
      op.verifyPlainOpCounts ctx opIn numLimbs 1
      pure ((List.range numLimbs).toArray.map fun i =>
        ((op.getOperand! ctx.raw i).getType! ctx.raw).val)
    else do
      op.verifyPlainOpCounts ctx opIn 1 numLimbs
      pure ((List.range numLimbs).toArray.map fun i =>
        ((op.getResult i).getType! ctx.raw).val)
  for i in [0:numLimbs] do
    let limbTy := limbs[i]!
    let .rankedTensorType tensor := limbTy
      | throw s!"{instrName}: limb {i} must be a prime field tensor, but got {limbTy}"
    let .primeFieldType field := tensor.elementType
      | throw s!"{instrName}: limb {i} must be a prime field tensor, but got {limbTy}"
    if field.modulus.value ≠ ring.moduli[i]! then
      throw s!"{instrName}: limb {i} has modulus {field.modulus.value}, but the ring's is {ring.moduli[i]!}"
    if field.isMontgomery then
      throw s!"{instrName}: limb {i} is in Montgomery form, but the ring's residues are canonical"
    if field.modulus.type.bitwidth ≠ ring.storageType.bitwidth then
      throw s!"{instrName}: limb {i} is stored in i{field.modulus.type.bitwidth}, but the ring's residues are i{ring.storageType.bitwidth}"
    if tensor.shape ≠ #[ring.degree] then
      throw s!"{instrName}: limb {i} must be 1-D with {ring.degree} elements, but got {limbTy}"

/--
`rescale` (`rescale = true`) and `base_convert`: input and output rings of the same
degree and storage type, both in the coefficient basis. `rescale` drops exactly the
last modulus.
-/
def OperationPtr.verifyRingCrossLimb {OpInfo : Type} [IsOpCode OpInfo]
    (op : OperationPtr) (ctx : WfIRContext OpInfo)
    (opIn : op.InBounds ctx.raw) (rescale : Bool) : Except String PUnit := do
  op.verifyPlainOpCounts ctx opIn 1 1
  let instrName := String.fromUTF8! (IsOpCode.name (op.getOpType ctx.raw opIn))
  let input ← ((op.getOperand! ctx.raw 0).getType! ctx.raw).val.verifyRqType
    s!"{instrName}: Expected a !ring.rq operand"
  let output ← ((op.getResult 0).getType! ctx.raw).val.verifyRqType
    s!"{instrName}: Expected a !ring.rq result"
  if input.ringDegree ≠ output.ringDegree then
    throw s!"{instrName}: input and output rings must share the degree N"
  if input.storageType ≠ output.storageType then
    throw s!"{instrName}: input and output rings must share the residue storage type"
  if input.domain ≠ .coeff ∨ output.domain ≠ .coeff then
    throw s!"{instrName}: combines residues across limbs, which only the coefficient basis relates"
  if rescale then
    if output.moduli.size + 1 ≠ input.moduli.size then
      throw s!"{instrName}: rescale drops exactly one modulus"
    if input.moduli.extract 0 output.moduli.size ≠ output.moduli then
      throw s!"{instrName}: output basis must be the input basis without its last modulus"

/--
Verify the local invariants of a `ring` operation in any operation-info type
containing the `ring` dialect. prime-ir's check that a bridge does not relabel the
basis of a value coming straight back from the opposite bridge is not modelled.
-/
def Ring.verifyLocalInvariants {OpInfo : Type} [IsOpCode OpInfo]
    [HasDialect OpInfo Ring] (opType : Ring) (op : OperationPtr)
    (ctx : WfIRContext OpInfo) (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  match opType with
  | .from_tensor => op.verifyRingResidueTensor ctx opIn true
  | .to_tensor => op.verifyRingResidueTensor ctx opIn false
  | .from_limbs => op.verifyRingLimbs ctx opIn true
  | .to_limbs => op.verifyRingLimbs ctx opIn false
  | .automorphism => op.verifyRingAutomorphism ctx opIn
  | .rescale => op.verifyRingCrossLimb ctx opIn true
  | .base_convert => op.verifyRingCrossLimb ctx opIn false
  | .add | .sub => op.verifyRingElementwiseOp ctx opIn 2
  | .mul => op.verifyRingElementwiseOp ctx opIn 2 (evalOnly := true)
  | .negate => op.verifyRingElementwiseOp ctx opIn 1

instance : HasOpInfo Ring where
  verifyLocalInvariants := Ring.verifyLocalInvariants
  getEffects := Ring.getEffects
  isConstantLike := Ring.isConstantLike
  hasSSADominance := Ring.hasSSADominance

end

end Veir
