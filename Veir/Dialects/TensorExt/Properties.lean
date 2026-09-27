module

public import Veir.IR.Attribute
public import Std.Data.HashMap

namespace Veir

public section

/--
  Properties of the `tensor_ext.bit_reverse` operation: the `dimension` along which
  the order is bit-reversed, an `I64Attr`.
-/
structure TensorExtBitReverseProperties where
  dimension : IntegerAttr
deriving Inhabited, Repr, Hashable, DecidableEq

def TensorExtBitReverseProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String TensorExtBitReverseProperties := do
  if attrDict.size > 1 then
    throw s!"tensor_ext.bit_reverse: expected only 'dimension' property, but got {attrDict.size} properties"
  let some attr := attrDict["dimension".toUTF8]?
    | throw "tensor_ext.bit_reverse: missing 'dimension' property"
  let .integerAttr dimension := attr
    | throw s!"tensor_ext.bit_reverse: expected 'dimension' to be an integer attribute, but got {attr}"
  return { dimension }

def TensorExtBitReverseProperties.toAttrDict (props : TensorExtBitReverseProperties) :
    Std.HashMap ByteArray Attribute :=
  (Std.HashMap.emptyWithCapacity 1).insert "dimension".toUTF8 (Attribute.integerAttr props.dimension)

end

end Veir
