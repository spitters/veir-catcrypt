module

public import Veir.IR.Attribute
public import Std.Data.HashMap

namespace Veir

public section

/--
  Properties of the `field.constant` operation. `value` is an integer attribute
  of the storage type for a `!field.pf` result, or a dense elements attribute
  for a `!field.ef` or container result.
-/
structure FieldConstantProperties where
  value : Attribute
deriving Inhabited, Repr, Hashable, DecidableEq

def FieldConstantProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String FieldConstantProperties := do
  if attrDict.size > 1 then
    throw s!"field.constant: expected only 'value' property, but got {attrDict.size} properties"
  let some attr := attrDict["value".toUTF8]?
    | throw "field.constant: missing 'value' property"
  match attr with
  | .integerAttr _ | .denseElementsAttr _ => return { value := attr }
  | _ => throw s!"field.constant: expected 'value' to be an integer or dense elements attribute, but got {attr}"

/--
  Properties of the `field.powui` operation. `unroll` is a `BoolAttr` (an `i1`
  integer attribute) that prime-ir defaults to true when it is absent; absence is
  kept so that the op prints back as it was parsed.
-/
structure FieldPowUIProperties where
  unroll : Option IntegerAttr
deriving Inhabited, Repr, Hashable, DecidableEq

def FieldPowUIProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String FieldPowUIProperties := do
  if attrDict.size > 1 then
    throw s!"field.powui: expected only the 'unroll' property, but got {attrDict.size} properties"
  match attrDict["unroll".toUTF8]? with
  | none => return { unroll := none }
  | some (.integerAttr intAttr) =>
    if intAttr.type.bitwidth ≠ 1 then
      throw s!"field.powui: expected 'unroll' to be a boolean, but got {intAttr}"
    return { unroll := some intAttr }
  | some attr => throw s!"field.powui: expected 'unroll' to be a boolean, but got {attr}"

def FieldPowUIProperties.toAttrDict (props : FieldPowUIProperties) :
    Std.HashMap ByteArray Attribute :=
  match props.unroll with
  | none => Std.HashMap.emptyWithCapacity 0
  | some unroll =>
    (Std.HashMap.emptyWithCapacity 1).insert "unroll".toUTF8 (Attribute.integerAttr unroll)

end

end Veir
