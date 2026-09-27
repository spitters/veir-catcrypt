module

public import Veir.IR.Simp
public import Veir.IR.OpInfo
meta import Veir.Meta.OpCode

namespace Veir

public section

/--
MLIR `polynomial` dialect (arithmetic over `Z_q[X]/(f)`). Target of the CatCrypt
lattice dialect (`ntt`, `invntt`, `basemul`, `polyAddN`, `polyMulC`).
-/
@[opcodes]
inductive Polynomial where
| add
| sub
| mul
| mul_scalar
| ntt
| intt
| constant
| from_tensor
| to_tensor
deriving Inhabited, Repr, Hashable, DecidableEq

@[expose, properties_of]
def Polynomial.propertiesOf (_op : Polynomial) : Type :=
  Unit

def Polynomial.fromAttrDict
    (_op : Polynomial) (_attrDict : Std.HashMap ByteArray Attribute) :
    Except String (Polynomial.propertiesOf _op) :=
  .ok ()

def Polynomial.toAttrDict
    (_op : Polynomial) (_props : Polynomial.propertiesOf _op) :
    Std.HashMap ByteArray Attribute :=
  Std.HashMap.emptyWithCapacity 0

@[get_effects]
def Polynomial.getEffects
    (op : Polynomial) (_props : Polynomial.propertiesOf op) : MemoryEffects :=
  match op with
  | _ => .none

def Polynomial.isConstantLike (_op : Polynomial) : Bool :=
  false

def Polynomial.hasSSADominance (_op : Polynomial) (_index : Nat) : Bool :=
  true

#generate_dialect Polynomial

instance : IsOpCode Polynomial where
  fromName := Polynomial.fromName
  name := Polynomial.name
  propertiesOf := Polynomial.propertiesOf
  fromAttrDict := Polynomial.fromAttrDict
  toAttrDict := Polynomial.toAttrDict

/--
The verifier accepts every `polynomial` operation: operand, result and region
counts are not checked for this dialect.
-/
@[expose]
def Polynomial.verifyLocalInvariants {OpInfo : Type} [IsOpCode OpInfo]
    [HasDialect OpInfo Polynomial] (_opType : Polynomial) (_op : OperationPtr)
    (_ctx : WfIRContext OpInfo) (_opIn : _op.InBounds _ctx.raw) : Except String PUnit :=
  pure ()

instance : HasOpInfo Polynomial where
  verifyLocalInvariants := Polynomial.verifyLocalInvariants
  getEffects := Polynomial.getEffects
  isConstantLike := Polynomial.isConstantLike
  hasSSADominance := Polynomial.hasSSADominance

end

end Veir
