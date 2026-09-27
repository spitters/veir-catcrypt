module

public import Veir.IR.Simp
public import Veir.IR.OpInfo
public import Veir.Verifier.Basic
meta import Veir.Meta.OpCode

namespace Veir

public section

/--
The prime-ir `poly` dialect over `!poly.polynomial<F, maxDegree>` (`PolyOps.td` at
fractalyze/prime-ir `fc4261887`). At that commit it has the two tensor bridges only;
the arithmetic on quotient rings is in the `ring` dialect.
-/
@[opcodes]
inductive Poly where
| to_tensor
| from_tensor
deriving Inhabited, Repr, Hashable, DecidableEq

@[expose, properties_of]
def Poly.propertiesOf (op : Poly) : Type :=
match op with
| .to_tensor | .from_tensor => Unit

def Poly.fromAttrDict
    (op : Poly) (_attrDict : Std.HashMap ByteArray Attribute) :
    Except String (Poly.propertiesOf op) := by
  cases op
  all_goals exact .ok ()

def Poly.toAttrDict
    (_op : Poly) (_props : Poly.propertiesOf _op) :
    Std.HashMap ByteArray Attribute :=
  Std.HashMap.emptyWithCapacity 0

@[get_effects]
def Poly.getEffects
    (_op : Poly) (_props : Poly.propertiesOf _op) : MemoryEffects :=
  .none

def Poly.isConstantLike (_op : Poly) : Bool :=
  false

def Poly.hasSSADominance (_op : Poly) (_index : Nat) : Bool :=
  true

#generate_dialect Poly

instance : IsOpCode Poly where
  fromName := Poly.fromName
  name := Poly.name
  propertiesOf := Poly.propertiesOf
  fromAttrDict := Poly.fromAttrDict
  toAttrDict := Poly.toAttrDict

/--
`to_tensor` (`toTensor = true`) and `from_tensor`: a polynomial on one side and a
1-D coefficient tensor of at most `maxDegree + 1` elements on the other.
-/
def OperationPtr.verifyPolyTensorBridge {OpInfo : Type} [IsOpCode OpInfo]
    (op : OperationPtr) (ctx : WfIRContext OpInfo)
    (opIn : op.InBounds ctx.raw) (toTensor : Bool) : Except String PUnit := do
  op.verifyPlainOpCounts ctx opIn 1 1
  let instrName := String.fromUTF8! (IsOpCode.name (op.getOpType ctx.raw opIn))
  let input := ((op.getOperand! ctx.raw 0).getType! ctx.raw).val
  let output := ((op.getResult 0).get! ctx.raw).type.val
  let (polyTy, tensorTy) := if toTensor then (input, output) else (output, input)
  let .polyType poly := polyTy
    | throw s!"{instrName}: Expected a polynomial type but found {polyTy} instead."
  let .primeFieldType _ := poly.baseField
    | throw s!"{instrName}: Expected a polynomial over a prime field but found {polyTy}."
  let .rankedTensorType tensor := tensorTy
    | throw s!"{instrName}: Expected a ranked tensor but found {tensorTy} instead."
  if tensor.shape.size ≠ 1 then
    throw s!"{instrName}: Expected a 1-D coefficient tensor but found {tensorTy}."
  let size := tensor.shape[0]!
  if (size : Int) > poly.maxDegree.value + 1 then
    throw s!"{instrName}: Expected at most {poly.maxDegree.value + 1} coefficients but found {size}."

/--
Verify the local invariants of a `poly` operation in any operation-info type
containing the `poly` dialect.
-/
def Poly.verifyLocalInvariants {OpInfo : Type} [IsOpCode OpInfo]
    [HasDialect OpInfo Poly] (opType : Poly) (op : OperationPtr)
    (ctx : WfIRContext OpInfo) (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  match opType with
  | .to_tensor => op.verifyPolyTensorBridge ctx opIn true
  | .from_tensor => op.verifyPolyTensorBridge ctx opIn false

instance : HasOpInfo Poly where
  verifyLocalInvariants := Poly.verifyLocalInvariants
  getEffects := Poly.getEffects
  isConstantLike := Poly.isConstantLike
  hasSSADominance := Poly.hasSSADominance

end

end Veir
