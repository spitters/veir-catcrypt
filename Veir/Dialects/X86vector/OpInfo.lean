module

public import Veir.IR.Simp
public import Veir.IR.OpInfo
meta import Veir.Meta.OpCode

namespace Veir

public section

/--
MLIR `x86vector` dialect. Target of the x86 intrinsics that Jasmin `extCall`
leaves carry to assembly: PCLMULQDQ (carry-less multiply for GCM and GF
arithmetic), AES-NI rounds and key-generation assist, and VPSHUFB (byte shuffle).
-/
@[opcodes]
inductive X86vector where
| pclmulqdq
| aesenc
| aesenclast
| aesdec
| aesdeclast
| aeskeygenassist
| vpshufb
| mask_compress
| mask_rndscale
| rsqrt
deriving Inhabited, Repr, Hashable, DecidableEq

@[expose, properties_of]
def X86vector.propertiesOf (_op : X86vector) : Type :=
  Unit

def X86vector.fromAttrDict
    (_op : X86vector) (_attrDict : Std.HashMap ByteArray Attribute) :
    Except String (X86vector.propertiesOf _op) :=
  .ok ()

def X86vector.toAttrDict
    (_op : X86vector) (_props : X86vector.propertiesOf _op) :
    Std.HashMap ByteArray Attribute :=
  Std.HashMap.emptyWithCapacity 0

@[get_effects]
def X86vector.getEffects
    (op : X86vector) (_props : X86vector.propertiesOf op) : MemoryEffects :=
  match op with
  | _ => .none

def X86vector.isConstantLike (_op : X86vector) : Bool :=
  false

def X86vector.hasSSADominance (_op : X86vector) (_index : Nat) : Bool :=
  true

#generate_dialect X86vector

instance : IsOpCode X86vector where
  fromName := X86vector.fromName
  name := X86vector.name
  propertiesOf := X86vector.propertiesOf
  fromAttrDict := X86vector.fromAttrDict
  toAttrDict := X86vector.toAttrDict

/--
The verifier accepts every `x86vector` operation: operand, result and region
counts are not checked for this dialect.
-/
@[expose]
def X86vector.verifyLocalInvariants {OpInfo : Type} [IsOpCode OpInfo]
    [HasDialect OpInfo X86vector] (_opType : X86vector) (_op : OperationPtr)
    (_ctx : WfIRContext OpInfo) (_opIn : _op.InBounds _ctx.raw) : Except String PUnit :=
  pure ()

instance : HasOpInfo X86vector where
  verifyLocalInvariants := X86vector.verifyLocalInvariants
  getEffects := X86vector.getEffects
  isConstantLike := X86vector.isConstantLike
  hasSSADominance := X86vector.hasSSADominance

end

end Veir
