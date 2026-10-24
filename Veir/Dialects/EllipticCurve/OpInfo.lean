module

public import Veir.IR.Simp
public import Veir.IR.OpInfo
public import Veir.Verifier.Basic
public import Veir.Dialects.EllipticCurve.Properties
public import Veir.Dialects.ModArith.Properties
public import Veir.Dialects.Field.OpInfo
meta import Veir.Meta.OpCode

namespace Veir

public section

/--
The prime-ir `elliptic_curve` dialect over the point types `!elliptic_curve.affine`,
`jacobian`, `xyzz` (short Weierstrass) and `ed_affine`, `ed_extended` (twisted Edwards)
(`EllipticCurveOps.td` at fractalyze/prime-ir `fc4261887`).
-/
@[opcodes]
inductive Elliptic_Curve where
| constant
| from_coords
| to_coords
| is_zero
| add
| sub
| negate
| double
| scalar_mul
| cmp
| msm
| pairing_check
| convert_point_type
| bitcast
deriving Inhabited, Repr, Hashable, DecidableEq

@[expose, properties_of]
def Elliptic_Curve.propertiesOf (op : Elliptic_Curve) : Type :=
match op with
| .constant => EllipticCurveConstantProperties
| .cmp => CmpPredicateProperties
| .msm => EllipticCurveMSMProperties
| .from_coords | .to_coords | .is_zero | .add | .sub | .negate | .double | .scalar_mul
| .pairing_check | .convert_point_type | .bitcast => Unit

def Elliptic_Curve.fromAttrDict
    (op : Elliptic_Curve) (attrDict : Std.HashMap ByteArray Attribute) :
    Except String (Elliptic_Curve.propertiesOf op) := by
  cases op
  case constant => exact EllipticCurveConstantProperties.fromAttrDict attrDict
  case cmp => exact CmpPredicateProperties.fromAttrDict "elliptic_curve.cmp" attrDict
  case msm => exact EllipticCurveMSMProperties.fromAttrDict attrDict
  all_goals exact .ok ()

def Elliptic_Curve.toAttrDict
    (op : Elliptic_Curve) (props : Elliptic_Curve.propertiesOf op) :
    Std.HashMap ByteArray Attribute :=
  match op with
  | .constant => EllipticCurveConstantProperties.toAttrDict props
  | .cmp => CmpPredicateProperties.toAttrDict props
  | .msm => EllipticCurveMSMProperties.toAttrDict props
  | _ => Std.HashMap.emptyWithCapacity 0

@[get_effects]
def Elliptic_Curve.getEffects
    (_op : Elliptic_Curve) (_props : Elliptic_Curve.propertiesOf _op) : MemoryEffects :=
  .none

def Elliptic_Curve.isConstantLike (op : Elliptic_Curve) : Bool :=
  match op with
  | .constant => true
  | _ => false

def Elliptic_Curve.hasSSADominance (_op : Elliptic_Curve) (_index : Nat) : Bool :=
  true

#generate_dialect Elliptic_Curve

instance : IsOpCode Elliptic_Curve where
  fromName := Elliptic_Curve.fromName
  name := Elliptic_Curve.name
  propertiesOf := Elliptic_Curve.propertiesOf
  fromAttrDict := Elliptic_Curve.fromAttrDict
  toAttrDict := Elliptic_Curve.toAttrDict

/-- The number of coordinates of a point representation (`getNumCoords` in prime-ir). -/
def EllipticCurvePointRepr.numCoords : EllipticCurvePointRepr → Nat
  | .affine | .edAffine => 2
  | .jacobian => 3
  | .xyzz | .edExtended => 4

/--
Check that `ty` is `PointLike`: a point type, or a shaped container of one, whose
curve attribute has the form the representation requires. Returns the point type.
-/
def Attribute.verifyPointLike (ty : Attribute) (msg : String) :
    Except String EllipticCurvePointType :=
  match ty.shapedElementType with
  | .ellipticCurvePointType type =>
    match type.curve with
    | .ellipticCurveAttr curve =>
      if curve.form = type.repr.form then pure type
      else throw s!"{msg} but found {ty} over a curve of the wrong form."
    | curve => throw s!"{msg} but found {ty} over {curve}, expected a curve attribute."
  | _ => throw s!"{msg} but found {ty} instead."

/-- `i1`, or a shaped `i1` container of the shape of `like`. -/
def Attribute.verifyBoolLikeOfShape (ty like : Attribute) (msg : String) : Except String PUnit := do
  let .integerType ⟨1⟩ := ty.shapedElementType
    | throw s!"{msg}: Expected i1 result"
  if ty.shapedShape ≠ like.shapedShape then
    throw s!"{msg}: Expected result to have the shape of the operands"

/--
`add`, `sub`: two point-like operands and a point-like result, all over the same
curve and of the same shape. The representations may differ (`type($lhs), type($rhs)
-> type($output)`).
-/
def OperationPtr.verifyEllipticCurveBinOp {OpInfo : Type} [IsOpCode OpInfo]
    (op : OperationPtr) (ctx : WfIRContext OpInfo)
    (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  op.verifyPlainOpCounts ctx opIn 2 1
  let instrName := String.fromUTF8! (IsOpCode.name (op.getOpType ctx.raw opIn))
  let lhs := ((op.getOperand! ctx.raw 0).getType! ctx.raw).val
  let rhs := ((op.getOperand! ctx.raw 1).getType! ctx.raw).val
  let result := ((op.getResult 0).getType! ctx.raw).val
  let lhsPoint ← lhs.verifyPointLike s!"{instrName}: Expected point-like lhs"
  let rhsPoint ← rhs.verifyPointLike s!"{instrName}: Expected point-like rhs"
  let resultPoint ← result.verifyPointLike s!"{instrName}: Expected point-like result"
  if lhsPoint.curve ≠ rhsPoint.curve ∨ lhsPoint.curve ≠ resultPoint.curve then
    throw s!"{instrName}: Expected operands and result on the same curve"
  if lhs.shapedShape ≠ rhs.shapedShape ∨ lhs.shapedShape ≠ result.shapedShape then
    throw s!"{instrName}: Expected operands and result of the same shape"

/--
`double`, `convert_point_type`: a point-like operand and a point-like result on the
same curve and of the same shape; the representation may change.
-/
def OperationPtr.verifyEllipticCurvePointConversion {OpInfo : Type} [IsOpCode OpInfo]
    (op : OperationPtr) (ctx : WfIRContext OpInfo)
    (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  op.verifyPlainOpCounts ctx opIn 1 1
  let instrName := String.fromUTF8! (IsOpCode.name (op.getOpType ctx.raw opIn))
  let input := ((op.getOperand! ctx.raw 0).getType! ctx.raw).val
  let output := ((op.getResult 0).getType! ctx.raw).val
  let inPoint ← input.verifyPointLike s!"{instrName}: Expected point-like operand"
  let outPoint ← output.verifyPointLike s!"{instrName}: Expected point-like result"
  if inPoint.curve ≠ outPoint.curve then
    throw s!"{instrName}: Expected operand and result on the same curve"
  if input.shapedShape ≠ output.shapedShape then
    throw s!"{instrName}: Expected operand and result of the same shape"

/-- `negate`: a point-like operand and a result of the same type. -/
def OperationPtr.verifyEllipticCurveNegate {OpInfo : Type} [IsOpCode OpInfo]
    (op : OperationPtr) (ctx : WfIRContext OpInfo)
    (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  op.verifyPlainOpCounts ctx opIn 1 1
  let instrName := String.fromUTF8! (IsOpCode.name (op.getOpType ctx.raw opIn))
  let operandType := (op.getOperand! ctx.raw 0).getType! ctx.raw
  op.verifyResultTypeMatches ctx operandType
    s!"{instrName}: Expected result type to match operand type"
  let _ ← operandType.val.verifyPointLike s!"{instrName}: Expected point-like operand"

/--
`constant`: a point-like result, and one coordinate array per point, each with the
representation's number of coordinates.
-/
def OperationPtr.verifyEllipticCurveConstant {OpInfo : Type} [IsOpCode OpInfo]
    [HasDialect OpInfo Elliptic_Curve] (op : OperationPtr) (ctx : WfIRContext OpInfo)
    (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  op.verifyPlainOpCounts ctx opIn 0 1
  let instrName := String.fromUTF8! (IsOpCode.name (op.getOpType ctx.raw opIn))
  let resultType := ((op.getResult 0).getType! ctx.raw).val
  let point ← resultType.verifyPointLike s!"{instrName}: Expected point-like result"
  let numPoints := (resultType.shapedShape.getD #[]).foldl (· * ·) 1
  let coords := (op.getProperties! ctx.raw Elliptic_Curve.constant).coords.value
  if coords.size ≠ numPoints then
    throw s!"{instrName}: Expected {numPoints} point(s) in 'coords', but got {coords.size}"
  for entry in coords do
    let .arrayAttr pointCoords := entry
      | throw s!"{instrName}: Expected each entry of 'coords' to be an array, but got {entry}"
    if pointCoords.value.size ≠ point.repr.numCoords then
      throw s!"{instrName}: Expected {point.repr.numCoords} coordinates per point, but got {pointCoords.value.size}"

/--
`from_coords`: one operand per coordinate of the point-like result. `to_coords` is
the converse: one point-like operand and one result per coordinate.
-/
def OperationPtr.verifyEllipticCurveCoords {OpInfo : Type} [IsOpCode OpInfo]
    (op : OperationPtr) (ctx : WfIRContext OpInfo)
    (opIn : op.InBounds ctx.raw) (fromCoords : Bool) : Except String PUnit := do
  let instrName := String.fromUTF8! (IsOpCode.name (op.getOpType ctx.raw opIn))
  if fromCoords then
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw s!"{instrName}: Expected 1 result(s)"
    let point ← ((op.getResult 0).getType! ctx.raw).val.verifyPointLike
      s!"{instrName}: Expected point-like result"
    op.verifyPlainOpCounts ctx opIn point.repr.numCoords 1
  else
    if op.getNumOperands ctx.raw opIn ≠ 1 then
      throw s!"{instrName}: Expected 1 operand(s)"
    let point ← ((op.getOperand! ctx.raw 0).getType! ctx.raw).val.verifyPointLike
      s!"{instrName}: Expected point-like operand"
    op.verifyPlainOpCounts ctx opIn 1 point.repr.numCoords

/-- `is_zero`: a point-like operand and an `i1`-like result of its shape. -/
def OperationPtr.verifyEllipticCurveIsZero {OpInfo : Type} [IsOpCode OpInfo]
    (op : OperationPtr) (ctx : WfIRContext OpInfo)
    (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  op.verifyPlainOpCounts ctx opIn 1 1
  let instrName := String.fromUTF8! (IsOpCode.name (op.getOpType ctx.raw opIn))
  let operandType := ((op.getOperand! ctx.raw 0).getType! ctx.raw).val
  let _ ← operandType.verifyPointLike s!"{instrName}: Expected point-like operand"
  ((op.getResult 0).getType! ctx.raw).val.verifyBoolLikeOfShape operandType instrName

/-- `cmp`: two point-like operands of the same type and an `i1`-like result of their shape. -/
def OperationPtr.verifyEllipticCurveCmp {OpInfo : Type} [IsOpCode OpInfo]
    (op : OperationPtr) (ctx : WfIRContext OpInfo)
    (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  op.verifyPlainOpCounts ctx opIn 2 1
  let instrName := String.fromUTF8! (IsOpCode.name (op.getOpType ctx.raw opIn))
  let operandType ← op.verifyOperandTypesMatch ctx 0 1
    s!"{instrName}: Expected operands to have the same type"
  let _ ← operandType.val.verifyPointLike s!"{instrName}: Expected point-like operands"
  ((op.getResult 0).getType! ctx.raw).val.verifyBoolLikeOfShape operandType.val instrName

/--
`scalar_mul`: a prime-field-like scalar, a point-like operand, and a point-like
result on the operand's curve.
-/
def OperationPtr.verifyEllipticCurveScalarMul {OpInfo : Type} [IsOpCode OpInfo]
    (op : OperationPtr) (ctx : WfIRContext OpInfo)
    (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  op.verifyPlainOpCounts ctx opIn 2 1
  let instrName := String.fromUTF8! (IsOpCode.name (op.getOpType ctx.raw opIn))
  let scalar := ((op.getOperand! ctx.raw 0).getType! ctx.raw).val
  let .primeFieldType _ := scalar.shapedElementType
    | throw s!"{instrName}: Expected a prime-field-like scalar but found {scalar} instead."
  let pointType := ((op.getOperand! ctx.raw 1).getType! ctx.raw).val
  let result := ((op.getResult 0).getType! ctx.raw).val
  let point ← pointType.verifyPointLike s!"{instrName}: Expected point-like operand"
  let resultPoint ← result.verifyPointLike s!"{instrName}: Expected point-like result"
  if point.curve ≠ resultPoint.curve then
    throw s!"{instrName}: Expected operand and result on the same curve"

/--
`msm`: a ranked tensor of prime field scalars, a ranked tensor of points of the same
shape, and a scalar point result on the points' curve.
-/
def OperationPtr.verifyEllipticCurveMSM {OpInfo : Type} [IsOpCode OpInfo]
    (op : OperationPtr) (ctx : WfIRContext OpInfo)
    (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  op.verifyPlainOpCounts ctx opIn 2 1
  let instrName := String.fromUTF8! (IsOpCode.name (op.getOpType ctx.raw opIn))
  let .rankedTensorType scalars := ((op.getOperand! ctx.raw 0).getType! ctx.raw).val
    | throw s!"{instrName}: Expected a ranked tensor of scalars"
  let .primeFieldType _ := scalars.elementType
    | throw s!"{instrName}: Expected prime field scalars"
  let .rankedTensorType points := ((op.getOperand! ctx.raw 1).getType! ctx.raw).val
    | throw s!"{instrName}: Expected a ranked tensor of points"
  let point ← points.elementType.verifyPointLike s!"{instrName}: Expected point elements"
  if scalars.shape ≠ points.shape then
    throw s!"{instrName}: Expected scalars and points of the same shape"
  let .ellipticCurvePointType output := ((op.getResult 0).getType! ctx.raw).val
    | throw s!"{instrName}: Expected a point result"
  if output.curve ≠ point.curve then
    throw s!"{instrName}: Expected the result on the points' curve"

/--
`pairing_check`: two 1-D tensors of affine points of the same length (G1 and G2) and
an `i1` result.
-/
def OperationPtr.verifyEllipticCurvePairingCheck {OpInfo : Type} [IsOpCode OpInfo]
    (op : OperationPtr) (ctx : WfIRContext OpInfo)
    (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  op.verifyPlainOpCounts ctx opIn 2 1
  let instrName := String.fromUTF8! (IsOpCode.name (op.getOpType ctx.raw opIn))
  let .rankedTensorType g1 := ((op.getOperand! ctx.raw 0).getType! ctx.raw).val
    | throw s!"{instrName}: Expected a 1-D tensor of G1 points"
  let .rankedTensorType g2 := ((op.getOperand! ctx.raw 1).getType! ctx.raw).val
    | throw s!"{instrName}: Expected a 1-D tensor of G2 points"
  for t in [g1, g2] do
    if t.shape.size ≠ 1 then
      throw s!"{instrName}: Expected 1-D tensors of points"
    let .ellipticCurvePointType ⟨.affine, _⟩ := t.elementType
      | throw s!"{instrName}: Expected affine points"
  if g1.shape ≠ g2.shape then
    throw s!"{instrName}: Expected G1 and G2 tensors of the same length"
  let .integerType ⟨1⟩ := ((op.getResult 0).getType! ctx.raw).val
    | throw s!"{instrName}: Expected i1 result"

/--
Verify the local invariants of an `elliptic_curve` operation in any operation-info type
containing the `elliptic_curve` dialect.
-/
def Elliptic_Curve.verifyLocalInvariants {OpInfo : Type} [IsOpCode OpInfo]
    [HasDialect OpInfo Elliptic_Curve] (opType : Elliptic_Curve) (op : OperationPtr)
    (ctx : WfIRContext OpInfo) (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  match opType with
  | .constant => op.verifyEllipticCurveConstant ctx opIn
  | .from_coords => op.verifyEllipticCurveCoords ctx opIn true
  | .to_coords => op.verifyEllipticCurveCoords ctx opIn false
  | .is_zero => op.verifyEllipticCurveIsZero ctx opIn
  | .add | .sub => op.verifyEllipticCurveBinOp ctx opIn
  | .negate => op.verifyEllipticCurveNegate ctx opIn
  | .double | .convert_point_type => op.verifyEllipticCurvePointConversion ctx opIn
  | .scalar_mul => op.verifyEllipticCurveScalarMul ctx opIn
  | .cmp => op.verifyEllipticCurveCmp ctx opIn
  | .msm => op.verifyEllipticCurveMSM ctx opIn
  | .pairing_check => op.verifyEllipticCurvePairingCheck ctx opIn
  | .bitcast => op.verifyPlainOpCounts ctx opIn 1 1

instance : HasOpInfo Elliptic_Curve where
  verifyLocalInvariants := Elliptic_Curve.verifyLocalInvariants
  getEffects := Elliptic_Curve.getEffects
  isConstantLike := Elliptic_Curve.isConstantLike
  hasSSADominance := Elliptic_Curve.hasSSADominance

end

end Veir
