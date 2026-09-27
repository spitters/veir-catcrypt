module

public import Veir.IR.Attribute
public import Veir.Dialects.Builtin.Properties
public import Std.Data.HashMap

namespace Veir

public section

/--
  Properties of the `elliptic_curve.constant` operation. `coords` is an array with
  one entry per point (one for a scalar point type), each entry an array of the
  point's coordinates, e.g. `[[1 : i32, 2 : i32]]` for an affine point.
-/
structure EllipticCurveConstantProperties where
  coords : ArrayAttr
deriving Inhabited, Repr, Hashable, DecidableEq

def EllipticCurveConstantProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String EllipticCurveConstantProperties := do
  if attrDict.size > 1 then
    throw s!"elliptic_curve.constant: expected only 'coords' property, but got {attrDict.size} properties"
  let some attr := attrDict["coords".toUTF8]?
    | throw "elliptic_curve.constant: missing 'coords' property"
  let .arrayAttr coords := attr
    | throw s!"elliptic_curve.constant: expected 'coords' to be an array attribute, but got {attr}"
  return { coords }

def EllipticCurveConstantProperties.toAttrDict (props : EllipticCurveConstantProperties) :
    Std.HashMap ByteArray Attribute :=
  (Std.HashMap.emptyWithCapacity 1).insert "coords".toUTF8 (Attribute.arrayAttr props.coords)

/--
  Properties of the `elliptic_curve.msm` operation: `degree` (`I32Attr`),
  `windowBits` (`I32Attr`, which prime-ir defaults to 0; absence is kept so that the
  op prints back as it was parsed) and the unit attribute `parallel`.
-/
structure EllipticCurveMSMProperties where
  degree : IntegerAttr
  windowBits : Option IntegerAttr
  parallel : Bool
deriving Inhabited, Repr, Hashable, DecidableEq

def EllipticCurveMSMProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String EllipticCurveMSMProperties := do
  let known := (["degree", "windowBits", "parallel"].filter
    (fun key => attrDict.contains key.toUTF8)).length
  if attrDict.size > known then
    throw s!"elliptic_curve.msm: expected only the 'degree', 'windowBits' and 'parallel' properties, but got {attrDict.size} properties"
  let some attr := attrDict["degree".toUTF8]?
    | throw "elliptic_curve.msm: missing 'degree' property"
  let .integerAttr degree := attr
    | throw s!"elliptic_curve.msm: expected 'degree' to be an integer attribute, but got {attr}"
  let windowBits ← match attrDict["windowBits".toUTF8]? with
    | none => pure none
    | some (.integerAttr bits) => pure (some bits)
    | some attr =>
      throw s!"elliptic_curve.msm: expected 'windowBits' to be an integer attribute, but got {attr}"
  let parallel ← getUnitAttr "parallel" attrDict
  return { degree, windowBits, parallel }

def EllipticCurveMSMProperties.toAttrDict (props : EllipticCurveMSMProperties) :
    Std.HashMap ByteArray Attribute := Id.run do
  let mut dict : Std.HashMap ByteArray Attribute := Std.HashMap.emptyWithCapacity 3
  dict := dict.insert "degree".toUTF8 (Attribute.integerAttr props.degree)
  if let some bits := props.windowBits then
    dict := dict.insert "windowBits".toUTF8 (Attribute.integerAttr bits)
  if props.parallel then
    dict := dict.insert "parallel".toUTF8 (Attribute.unitAttr UnitAttr.mk)
  return dict

end

end Veir
