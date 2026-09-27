module

public import Veir.IR.Simp
public import Veir.IR.OpInfo
meta import Veir.Meta.OpCode

namespace Veir

public section

/--
MLIR `vector` dialect. Target of the packed `stackArr w n` operations that the
Jasmin, Frodo, GF, MAYO and qruov emitters use for SIMD-shaped arithmetic.
-/
@[opcodes]
inductive Vector where
| broadcast
| extract
| insert
| extractelement
| insertelement
| fma
| reduction
| splat
| load
| store
| transfer_read
| transfer_write
| shuffle
deriving Inhabited, Repr, Hashable, DecidableEq

@[expose, properties_of]
def Vector.propertiesOf (_op : Vector) : Type :=
  Unit

def Vector.fromAttrDict
    (_op : Vector) (_attrDict : Std.HashMap ByteArray Attribute) :
    Except String (Vector.propertiesOf _op) :=
  .ok ()

def Vector.toAttrDict
    (_op : Vector) (_props : Vector.propertiesOf _op) :
    Std.HashMap ByteArray Attribute :=
  Std.HashMap.emptyWithCapacity 0

@[get_effects]
def Vector.getEffects
    (op : Vector) (_props : Vector.propertiesOf op) : MemoryEffects :=
  match op with
  | .load | .transfer_read => .read
  | .store | .transfer_write => .write
  | _ => .none

def Vector.isConstantLike (_op : Vector) : Bool :=
  false

def Vector.hasSSADominance (_op : Vector) (_index : Nat) : Bool :=
  true

#generate_dialect Vector

instance : IsOpCode Vector where
  fromName := Vector.fromName
  name := Vector.name
  propertiesOf := Vector.propertiesOf
  fromAttrDict := Vector.fromAttrDict
  toAttrDict := Vector.toAttrDict

/--
The verifier accepts every `vector` operation: operand, result and region
counts are not checked for this dialect.
-/
@[expose]
def Vector.verifyLocalInvariants {OpInfo : Type} [IsOpCode OpInfo]
    [HasDialect OpInfo Vector] (_opType : Vector) (_op : OperationPtr)
    (_ctx : WfIRContext OpInfo) (_opIn : _op.InBounds _ctx.raw) : Except String PUnit :=
  pure ()

instance : HasOpInfo Vector where
  verifyLocalInvariants := Vector.verifyLocalInvariants
  getEffects := Vector.getEffects
  isConstantLike := Vector.isConstantLike
  hasSSADominance := Vector.hasSSADominance

end

end Veir
