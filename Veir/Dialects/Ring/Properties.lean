module

public import Veir.IR.Attribute
public import Std.Data.HashMap

namespace Veir

public section

/--
  Properties of the `ring.automorphism` operation: the Galois exponent `g` of
  `X ↦ X^g`, an `I64Attr`.
-/
structure RingAutomorphismProperties where
  exponent : IntegerAttr
deriving Inhabited, Repr, Hashable, DecidableEq

def RingAutomorphismProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String RingAutomorphismProperties := do
  if attrDict.size > 1 then
    throw s!"ring.automorphism: expected only 'exponent' property, but got {attrDict.size} properties"
  let some attr := attrDict["exponent".toUTF8]?
    | throw "ring.automorphism: missing 'exponent' property"
  let .integerAttr exponent := attr
    | throw s!"ring.automorphism: expected 'exponent' to be an integer attribute, but got {attr}"
  return { exponent }

def RingAutomorphismProperties.toAttrDict (props : RingAutomorphismProperties) :
    Std.HashMap ByteArray Attribute :=
  (Std.HashMap.emptyWithCapacity 1).insert "exponent".toUTF8 (Attribute.integerAttr props.exponent)

end

end Veir
