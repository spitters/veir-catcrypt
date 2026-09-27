module

public import Veir.IR.Simp
public import Veir.IR.OpInfo
meta import Veir.Meta.OpCode

namespace Veir

public section

/--
CatCrypt dialect: a holding pen for CatCrypt operations with no registered MLIR
counterpart (pair and sum construction and similar). Lowered operations print as
`catcrypt.unknown`, which `mlir-opt` accepts under `--allow-unregistered-dialect`.
-/
@[opcodes]
inductive Catcrypt where
| unknown
deriving Inhabited, Repr, Hashable, DecidableEq

@[expose, properties_of]
def Catcrypt.propertiesOf (_op : Catcrypt) : Type :=
  Unit

def Catcrypt.fromAttrDict
    (_op : Catcrypt) (_attrDict : Std.HashMap ByteArray Attribute) :
    Except String (Catcrypt.propertiesOf _op) :=
  .ok ()

def Catcrypt.toAttrDict
    (_op : Catcrypt) (_props : Catcrypt.propertiesOf _op) :
    Std.HashMap ByteArray Attribute :=
  Std.HashMap.emptyWithCapacity 0

@[get_effects]
def Catcrypt.getEffects
    (op : Catcrypt) (_props : Catcrypt.propertiesOf op) : MemoryEffects :=
  match op with
  | .unknown => .unknown

def Catcrypt.isConstantLike (_op : Catcrypt) : Bool :=
  false

def Catcrypt.hasSSADominance (_op : Catcrypt) (_index : Nat) : Bool :=
  true

#generate_dialect Catcrypt

instance : IsOpCode Catcrypt where
  fromName := Catcrypt.fromName
  name := Catcrypt.name
  propertiesOf := Catcrypt.propertiesOf
  fromAttrDict := Catcrypt.fromAttrDict
  toAttrDict := Catcrypt.toAttrDict

/--
The verifier accepts every `catcrypt` operation: operand, result and region
counts are not checked for this dialect.
-/
@[expose]
def Catcrypt.verifyLocalInvariants {OpInfo : Type} [IsOpCode OpInfo]
    [HasDialect OpInfo Catcrypt] (_opType : Catcrypt) (_op : OperationPtr)
    (_ctx : WfIRContext OpInfo) (_opIn : _op.InBounds _ctx.raw) : Except String PUnit :=
  pure ()

instance : HasOpInfo Catcrypt where
  verifyLocalInvariants := Catcrypt.verifyLocalInvariants
  getEffects := Catcrypt.getEffects
  isConstantLike := Catcrypt.isConstantLike
  hasSSADominance := Catcrypt.hasSSADominance

end

end Veir
