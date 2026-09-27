module

public import Veir.IR.Simp
public import Veir.IR.OpInfo
public import Veir.Verifier.Basic
public import Veir.Dialects.TensorExt.Properties
meta import Veir.Meta.OpCode

namespace Veir

public section

/--
The prime-ir `tensor_ext` dialect (`TensorExtOps.td` at fractalyze/prime-ir
`fc4261887`): `bit_reverse`, destination-style on builtin ranked tensors.
-/
@[opcodes]
inductive Tensor_Ext where
| bit_reverse
deriving Inhabited, Repr, Hashable, DecidableEq

@[expose, properties_of]
def Tensor_Ext.propertiesOf (op : Tensor_Ext) : Type :=
match op with
| .bit_reverse => TensorExtBitReverseProperties

def Tensor_Ext.fromAttrDict
    (op : Tensor_Ext) (attrDict : Std.HashMap ByteArray Attribute) :
    Except String (Tensor_Ext.propertiesOf op) := by
  cases op
  case bit_reverse => exact TensorExtBitReverseProperties.fromAttrDict attrDict

def Tensor_Ext.toAttrDict
    (op : Tensor_Ext) (props : Tensor_Ext.propertiesOf op) :
    Std.HashMap ByteArray Attribute :=
  match op with
  | .bit_reverse => TensorExtBitReverseProperties.toAttrDict props

@[get_effects]
def Tensor_Ext.getEffects
    (_op : Tensor_Ext) (_props : Tensor_Ext.propertiesOf _op) : MemoryEffects :=
  .none

def Tensor_Ext.isConstantLike (_op : Tensor_Ext) : Bool :=
  false

def Tensor_Ext.hasSSADominance (_op : Tensor_Ext) (_index : Nat) : Bool :=
  true

#generate_dialect Tensor_Ext

instance : IsOpCode Tensor_Ext where
  fromName := Tensor_Ext.fromName
  name := Tensor_Ext.name
  propertiesOf := Tensor_Ext.propertiesOf
  fromAttrDict := Tensor_Ext.fromAttrDict
  toAttrDict := Tensor_Ext.toAttrDict

/--
`bit_reverse`: source, destination and result of one ranked tensor type; `dimension`
indexes a dimension whose size is a power of two.
-/
def OperationPtr.verifyTensorExtBitReverse {OpInfo : Type} [IsOpCode OpInfo]
    [HasDialect OpInfo Tensor_Ext] (op : OperationPtr) (ctx : WfIRContext OpInfo)
    (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  op.verifyPlainOpCounts ctx opIn 2 1
  let instrName := String.fromUTF8! (IsOpCode.name (op.getOpType ctx.raw opIn))
  let sourceType ← op.verifyOperandTypesMatch ctx 0 1
    s!"{instrName}: Expected source and destination to have the same type"
  op.verifyResultTypeMatches ctx sourceType
    s!"{instrName}: Expected result type to match operand type"
  let .rankedTensorType tensor := sourceType.val
    | throw s!"{instrName}: Expected a ranked tensor but found {sourceType.val} instead."
  let dimension := (op.getProperties! ctx.raw Tensor_Ext.bit_reverse).dimension.value
  if dimension < 0 ∨ dimension ≥ tensor.shape.size then
    throw s!"{instrName}: dimension {dimension} is out of range for rank {tensor.shape.size}"
  let size := tensor.shape[dimension.toNat]!
  if size ≠ 2 ^ (Nat.log2 size) then
    throw s!"{instrName}: dimension {dimension} has size {size}, which is not a power of two"

/--
Verify the local invariants of a `tensor_ext` operation in any operation-info type
containing the `tensor_ext` dialect.
-/
def Tensor_Ext.verifyLocalInvariants {OpInfo : Type} [IsOpCode OpInfo]
    [HasDialect OpInfo Tensor_Ext] (opType : Tensor_Ext) (op : OperationPtr)
    (ctx : WfIRContext OpInfo) (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  match opType with
  | .bit_reverse => op.verifyTensorExtBitReverse ctx opIn

instance : HasOpInfo Tensor_Ext where
  verifyLocalInvariants := Tensor_Ext.verifyLocalInvariants
  getEffects := Tensor_Ext.getEffects
  isConstantLike := Tensor_Ext.isConstantLike
  hasSSADominance := Tensor_Ext.hasSSADominance

end

end Veir
