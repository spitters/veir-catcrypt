module

public import Veir.IR.Attribute
public import Std.Data.HashMap

namespace Veir

public section

/--
  Properties of the `mod_arith.constant` operation.
-/
structure ModArithConstantProperties where
  value : IntegerAttr
deriving Inhabited, Repr, Hashable, DecidableEq

def ModArithConstantProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String ModArithConstantProperties := do
  if attrDict.size > 1 then
    throw s!"mod_arith.constant: expected only 'value' property, but got {attrDict.size} properties"
  let some attr := attrDict["value".toUTF8]?
    | throw "mod_arith.constant: missing 'value' property"
  let .integerAttr intAttr := attr
    | throw s!"mod_arith.constant: expected 'value' to be an integer attribute, but got {attr}"
  return { value := intAttr }

/--
  Properties of a comparison operation whose `predicate` is an `arith.cmpi`
  predicate, e.g. `mod_arith.cmp` and `field.cmp` in prime-ir. The predicate is
  kept as the integer attribute of its generic form (`0 : i64` for `eq`).
-/
structure CmpPredicateProperties where
  predicate : IntegerAttr
deriving Inhabited, Repr, Hashable, DecidableEq

def CmpPredicateProperties.fromAttrDict (opName : String)
    (attrDict : Std.HashMap ByteArray Attribute) :
    Except String CmpPredicateProperties := do
  if attrDict.size > 1 then
    throw s!"{opName}: expected only 'predicate' property, but got {attrDict.size} properties"
  let some attr := attrDict["predicate".toUTF8]?
    | throw s!"{opName}: missing 'predicate' property"
  let .integerAttr intAttr := attr
    | throw s!"{opName}: expected 'predicate' to be an integer attribute, but got {attr}"
  return { predicate := intAttr }

def CmpPredicateProperties.toAttrDict (props : CmpPredicateProperties) :
    Std.HashMap ByteArray Attribute :=
  (Std.HashMap.emptyWithCapacity 1).insert "predicate".toUTF8 (Attribute.integerAttr props.predicate)

end

end Veir
