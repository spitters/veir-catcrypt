module

public import Veir.IR.Simp
public import Veir.IR.OpInfo
meta import Veir.Meta.OpCode

namespace Veir

public section

/--
MLIR `memref` dialect (buffers and memory references). The CatCrypt
`memref{Zero,Get,Set}` operations lower to these registered operations.
-/
@[opcodes]
inductive Memref where
| alloc
| alloca
| dealloc
| load
| store
| get_global
| global
| copy
| subview
| dim
deriving Inhabited, Repr, Hashable, DecidableEq

@[expose, properties_of]
def Memref.propertiesOf (_op : Memref) : Type :=
  Unit

def Memref.fromAttrDict
    (_op : Memref) (_attrDict : Std.HashMap ByteArray Attribute) :
    Except String (Memref.propertiesOf _op) :=
  .ok ()

def Memref.toAttrDict
    (_op : Memref) (_props : Memref.propertiesOf _op) :
    Std.HashMap ByteArray Attribute :=
  Std.HashMap.emptyWithCapacity 0

@[get_effects]
def Memref.getEffects
    (op : Memref) (_props : Memref.propertiesOf op) : MemoryEffects :=
  match op with
  | .alloc | .alloca => .allocate
  | .dealloc => .unknown
  | .load => .read
  | .store => .write
  | .copy => .readWrite
  | .get_global | .global | .subview | .dim => .none

def Memref.isConstantLike (_op : Memref) : Bool :=
  false

def Memref.hasSSADominance (_op : Memref) (_index : Nat) : Bool :=
  true

#generate_dialect Memref

instance : IsOpCode Memref where
  fromName := Memref.fromName
  name := Memref.name
  propertiesOf := Memref.propertiesOf
  fromAttrDict := Memref.fromAttrDict
  toAttrDict := Memref.toAttrDict

/--
The verifier accepts every `memref` operation: operand, result and region
counts are not checked for this dialect.
-/
@[expose]
def Memref.verifyLocalInvariants {OpInfo : Type} [IsOpCode OpInfo]
    [HasDialect OpInfo Memref] (_opType : Memref) (_op : OperationPtr)
    (_ctx : WfIRContext OpInfo) (_opIn : _op.InBounds _ctx.raw) : Except String PUnit :=
  pure ()

instance : HasOpInfo Memref where
  verifyLocalInvariants := Memref.verifyLocalInvariants
  getEffects := Memref.getEffects
  isConstantLike := Memref.isConstantLike
  hasSSADominance := Memref.hasSSADominance

end

end Veir
