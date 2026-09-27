module

import Veir.Meta.OpCode

public import Veir.IR.Basic
public import Veir.OpCode
public import Veir.Printer.CustomPrinting
public import Veir.Dialects.Func.Printing

namespace Veir

public section

/--
  A type family that maps an operation code to the type of its properties.
  For operations that do not have any properties, the type is `Unit`.
-/
@[expose, properties_of]
def _propertiesOf (opCode : OpCode) : Type :=
match opCode with
| .arith op => Arith.propertiesOf op
| .llvm op => Llvm.propertiesOf op
| .riscv op => Riscv.propertiesOf op
| .riscv_cf op => Riscv_Cf.propertiesOf op
| .riscv_stack op => Riscv_Stack.propertiesOf op
| .rv64 op => Rv64.propertiesOf op
| .mod_arith op => Mod_Arith.propertiesOf op
| .field op => Field.propertiesOf op
| .elliptic_curve op => Elliptic_Curve.propertiesOf op
| .poly op => Poly.propertiesOf op
| .ring op => Ring.propertiesOf op
| .tensor_ext op => Tensor_Ext.propertiesOf op
| .cf op => Cf.propertiesOf op
| .comb op => Comb.propertiesOf op
| .hw op => HW.propertiesOf op
| .verif op => Verif.propertiesOf op
| .builtin op => Builtin.propertiesOf op
| .func op => Func.propertiesOf op
| .datapath op => Datapath.propertiesOf op
| .pdl op => PDL.propertiesOf op
| .io op => Io.propertiesOf op
| .gmir op => GMIR.propertiesOf op
| .test op => Test.propertiesOf op
| .felt op => Felt.propertiesOf op
| .cir op => Cir.propertiesOf op
| .include op => LLZK.Include.propertiesOf op
| .function op => LLZK.Function.propertiesOf op
| .seq op => Seq.propertiesOf op
| .catcrypt op => Catcrypt.propertiesOf op
| .memref op => Memref.propertiesOf op
| .polynomial op => Polynomial.propertiesOf op
| .vector op => Vector.propertiesOf op
| .x86vector op => X86vector.propertiesOf op

/--
  What are the memory effects of an operation with this opcode and these
  properties?
-/
@[get_effects]
def OpCode.getEffects (opCode : OpCode) (props : _propertiesOf opCode) : MemoryEffects :=
  match opCode, props with
  | .arith op, props => Arith.getEffects op props
  | .llvm op, props => Llvm.getEffects op props
  | .riscv op, props => Riscv.getEffects op props
  | .riscv_cf op, props => Riscv_Cf.getEffects op props
  | .riscv_stack op, props => Riscv_Stack.getEffects op props
  | .rv64 op, props => Rv64.getEffects op props
  | .mod_arith op, props => Mod_Arith.getEffects op props
  | .field op, props => Field.getEffects op props
  | .elliptic_curve op, props => Elliptic_Curve.getEffects op props
  | .poly op, props => Poly.getEffects op props
  | .ring op, props => Ring.getEffects op props
  | .tensor_ext op, props => Tensor_Ext.getEffects op props
  | .cf op, props => Cf.getEffects op props
  | .comb op, props => Comb.getEffects op props
  | .hw op, props => HW.getEffects op props
  | .verif op, props => Verif.getEffects op props
  | .builtin op, props => Builtin.getEffects op props
  | .func op, props => Func.getEffects op props
  | .datapath op, props => Datapath.getEffects op props
  | .pdl op, props => PDL.getEffects op props
  | .io op, props => Io.getEffects op props
  | .gmir op, props => GMIR.getEffects op props
  | .test op, props => Test.getEffects op props
  | .felt op, props => Felt.getEffects op props
  | .cir op, props => Cir.getEffects op props
  | .include op, props => LLZK.Include.getEffects op props
  | .function op, props => LLZK.Function.getEffects op props
  | .seq op, props => Seq.getEffects op props
  | .catcrypt op, props => Catcrypt.getEffects op props
  | .memref op, props => Memref.getEffects op props
  | .polynomial op, props => Polynomial.getEffects op props
  | .vector op, props => Vector.getEffects op props
  | .x86vector op, props => X86vector.getEffects op props

/-- Delegate folding to the operation's dialect-local `HasOpInfo` instance. -/
def OpCode.tryFold (opCode : OpCode) (props : _propertiesOf opCode)
    (resultTypes : Array TypeAttr) (constantOperands : Array (Option RuntimeValue)) :
    Option (Array FoldDecision) :=
  match opCode, props with
  | .arith op, props => HasOpInfo.tryFold op props resultTypes constantOperands
  | .llvm op, props => HasOpInfo.tryFold op props resultTypes constantOperands
  | .riscv op, props => HasOpInfo.tryFold op props resultTypes constantOperands
  | .riscv_cf op, props => HasOpInfo.tryFold op props resultTypes constantOperands
  | .riscv_stack op, props => HasOpInfo.tryFold op props resultTypes constantOperands
  | .rv64 op, props => HasOpInfo.tryFold op props resultTypes constantOperands
  | .mod_arith op, props => HasOpInfo.tryFold op props resultTypes constantOperands
  | .field op, props => HasOpInfo.tryFold op props resultTypes constantOperands
  | .elliptic_curve op, props => HasOpInfo.tryFold op props resultTypes constantOperands
  | .poly op, props => HasOpInfo.tryFold op props resultTypes constantOperands
  | .ring op, props => HasOpInfo.tryFold op props resultTypes constantOperands
  | .tensor_ext op, props => HasOpInfo.tryFold op props resultTypes constantOperands
  | .cf op, props => HasOpInfo.tryFold op props resultTypes constantOperands
  | .comb op, props => HasOpInfo.tryFold op props resultTypes constantOperands
  | .hw op, props => HasOpInfo.tryFold op props resultTypes constantOperands
  | .verif op, props => HasOpInfo.tryFold op props resultTypes constantOperands
  | .builtin op, props => HasOpInfo.tryFold op props resultTypes constantOperands
  | .func op, props => HasOpInfo.tryFold op props resultTypes constantOperands
  | .datapath op, props => HasOpInfo.tryFold op props resultTypes constantOperands
  | .pdl op, props => HasOpInfo.tryFold op props resultTypes constantOperands
  | .io op, props => HasOpInfo.tryFold op props resultTypes constantOperands
  | .gmir op, props => HasOpInfo.tryFold op props resultTypes constantOperands
  | .test op, props => HasOpInfo.tryFold op props resultTypes constantOperands
  | .felt op, props => HasOpInfo.tryFold op props resultTypes constantOperands
  | .cir op, props => HasOpInfo.tryFold op props resultTypes constantOperands
  | .include op, props => HasOpInfo.tryFold op props resultTypes constantOperands
  | .function op, props => HasOpInfo.tryFold op props resultTypes constantOperands
  | .seq op, props => HasOpInfo.tryFold op props resultTypes constantOperands
  | .catcrypt op, props => HasOpInfo.tryFold op props resultTypes constantOperands
  | .memref op, props => HasOpInfo.tryFold op props resultTypes constantOperands
  | .polynomial op, props => HasOpInfo.tryFold op props resultTypes constantOperands
  | .vector op, props => HasOpInfo.tryFold op props resultTypes constantOperands
  | .x86vector op, props => HasOpInfo.tryFold op props resultTypes constantOperands

/--
  Return the kind of the region with the given index inside this operation.
-/
def OpCode.getRegionKind (opCode : OpCode) (index : Nat) : RegionKind :=
  match opCode with
  | .arith op => HasOpInfo.getRegionKind op index
  | .llvm op => HasOpInfo.getRegionKind op index
  | .riscv op => HasOpInfo.getRegionKind op index
  | .riscv_cf op => HasOpInfo.getRegionKind op index
  | .riscv_stack op => HasOpInfo.getRegionKind op index
  | .rv64 op => HasOpInfo.getRegionKind op index
  | .mod_arith op => HasOpInfo.getRegionKind op index
  | .field op => HasOpInfo.getRegionKind op index
  | .elliptic_curve op => HasOpInfo.getRegionKind op index
  | .poly op => HasOpInfo.getRegionKind op index
  | .ring op => HasOpInfo.getRegionKind op index
  | .tensor_ext op => HasOpInfo.getRegionKind op index
  | .cf op => HasOpInfo.getRegionKind op index
  | .comb op => HasOpInfo.getRegionKind op index
  | .hw op => HasOpInfo.getRegionKind op index
  | .verif op => HasOpInfo.getRegionKind op index
  | .builtin op => HasOpInfo.getRegionKind op index
  | .func op => HasOpInfo.getRegionKind op index
  | .datapath op => HasOpInfo.getRegionKind op index
  | .pdl op => HasOpInfo.getRegionKind op index
  | .io op => HasOpInfo.getRegionKind op index
  | .gmir op => HasOpInfo.getRegionKind op index
  | .test op => HasOpInfo.getRegionKind op index
  | .felt op => HasOpInfo.getRegionKind op index
  | .cir op => HasOpInfo.getRegionKind op index
  | .include op => HasOpInfo.getRegionKind op index
  | .function op => HasOpInfo.getRegionKind op index
  | .seq op => HasOpInfo.getRegionKind op index
  | .catcrypt op => HasOpInfo.getRegionKind op index
  | .memref op => HasOpInfo.getRegionKind op index
  | .polynomial op => HasOpInfo.getRegionKind op index
  | .vector op => HasOpInfo.getRegionKind op index
  | .x86vector op => HasOpInfo.getRegionKind op index

/--
  Whether definitions in the indexed region of this opcode must dominate
  their uses.
-/
def OpCode.hasSSADominance (opCode : OpCode) (index : Nat) : Bool :=
  match opCode with
  | .arith op => Arith.hasSSADominance op index
  | .llvm op => Llvm.hasSSADominance op index
  | .riscv op => Riscv.hasSSADominance op index
  | .riscv_cf op => Riscv_Cf.hasSSADominance op index
  | .riscv_stack op => Riscv_Stack.hasSSADominance op index
  | .rv64 op => Rv64.hasSSADominance op index
  | .mod_arith op => Mod_Arith.hasSSADominance op index
  | .field op => Field.hasSSADominance op index
  | .elliptic_curve op => Elliptic_Curve.hasSSADominance op index
  | .poly op => Poly.hasSSADominance op index
  | .ring op => Ring.hasSSADominance op index
  | .tensor_ext op => Tensor_Ext.hasSSADominance op index
  | .cf op => Cf.hasSSADominance op index
  | .comb op => Comb.hasSSADominance op index
  | .hw op => HW.hasSSADominance op index
  | .verif op => Verif.hasSSADominance op index
  | .builtin op => Builtin.hasSSADominance op index
  | .func op => Func.hasSSADominance op index
  | .datapath op => Datapath.hasSSADominance op index
  | .pdl op => PDL.hasSSADominance op index
  | .io op => Io.hasSSADominance op index
  | .gmir op => GMIR.hasSSADominance op index
  | .test op => Test.hasSSADominance op index
  | .felt op => Felt.hasSSADominance op index
  | .cir op => Cir.hasSSADominance op index
  | .include op => LLZK.Include.hasSSADominance op index
  | .function op => LLZK.Function.hasSSADominance op index
  | .seq op => Seq.hasSSADominance op index
  | .catcrypt op => Catcrypt.hasSSADominance op index
  | .memref op => Memref.hasSSADominance op index
  | .polynomial op => Polynomial.hasSSADominance op index
  | .vector op => Vector.hasSSADominance op index
  | .x86vector op => X86vector.hasSSADominance op index

/--
  Whether the indexed region of this opcode is exempt from the requirement
  that each of its blocks ends in a terminator. Dialects that do not say
  otherwise inherit the `HasOpInfo` default of `false`.
-/
def OpCode.hasNoTerminator (opCode : OpCode) (index : Nat) : Bool :=
  match opCode with
  | .arith op => HasOpInfo.hasNoTerminator op index
  | .llvm op => HasOpInfo.hasNoTerminator op index
  | .riscv op => HasOpInfo.hasNoTerminator op index
  | .riscv_cf op => HasOpInfo.hasNoTerminator op index
  | .riscv_stack op => HasOpInfo.hasNoTerminator op index
  | .rv64 op => HasOpInfo.hasNoTerminator op index
  | .mod_arith op => HasOpInfo.hasNoTerminator op index
  | .field op => HasOpInfo.hasNoTerminator op index
  | .elliptic_curve op => HasOpInfo.hasNoTerminator op index
  | .poly op => HasOpInfo.hasNoTerminator op index
  | .ring op => HasOpInfo.hasNoTerminator op index
  | .tensor_ext op => HasOpInfo.hasNoTerminator op index
  | .cf op => HasOpInfo.hasNoTerminator op index
  | .comb op => HasOpInfo.hasNoTerminator op index
  | .hw op => HasOpInfo.hasNoTerminator op index
  | .verif op => HasOpInfo.hasNoTerminator op index
  | .builtin op => HasOpInfo.hasNoTerminator op index
  | .func op => HasOpInfo.hasNoTerminator op index
  | .datapath op => HasOpInfo.hasNoTerminator op index
  | .pdl op => HasOpInfo.hasNoTerminator op index
  | .io op => HasOpInfo.hasNoTerminator op index
  | .gmir op => HasOpInfo.hasNoTerminator op index
  | .test op => HasOpInfo.hasNoTerminator op index
  | .felt op => HasOpInfo.hasNoTerminator op index
  | .cir op => HasOpInfo.hasNoTerminator op index
  | .include op => HasOpInfo.hasNoTerminator op index
  | .function op => HasOpInfo.hasNoTerminator op index
  | .seq op => HasOpInfo.hasNoTerminator op index
  | .catcrypt op => HasOpInfo.hasNoTerminator op index
  | .memref op => HasOpInfo.hasNoTerminator op index
  | .polynomial op => HasOpInfo.hasNoTerminator op index
  | .vector op => HasOpInfo.hasNoTerminator op index
  | .x86vector op => HasOpInfo.hasNoTerminator op index

/-- Whether this opcode carries MLIR's `IsolatedFromAbove` trait. -/
def OpCode.isIsolatedFromAbove (opCode : OpCode) : Bool :=
  match opCode with
  | .arith op => HasOpInfo.isIsolatedFromAbove op
  | .llvm op => HasOpInfo.isIsolatedFromAbove op
  | .riscv op => HasOpInfo.isIsolatedFromAbove op
  | .riscv_cf op => HasOpInfo.isIsolatedFromAbove op
  | .riscv_stack op => HasOpInfo.isIsolatedFromAbove op
  | .rv64 op => HasOpInfo.isIsolatedFromAbove op
  | .mod_arith op => HasOpInfo.isIsolatedFromAbove op
  | .field op => HasOpInfo.isIsolatedFromAbove op
  | .elliptic_curve op => HasOpInfo.isIsolatedFromAbove op
  | .poly op => HasOpInfo.isIsolatedFromAbove op
  | .ring op => HasOpInfo.isIsolatedFromAbove op
  | .tensor_ext op => HasOpInfo.isIsolatedFromAbove op
  | .cf op => HasOpInfo.isIsolatedFromAbove op
  | .comb op => HasOpInfo.isIsolatedFromAbove op
  | .hw op => HasOpInfo.isIsolatedFromAbove op
  | .verif op => HasOpInfo.isIsolatedFromAbove op
  | .builtin op => HasOpInfo.isIsolatedFromAbove op
  | .func op => HasOpInfo.isIsolatedFromAbove op
  | .datapath op => HasOpInfo.isIsolatedFromAbove op
  | .pdl op => HasOpInfo.isIsolatedFromAbove op
  | .io op => HasOpInfo.isIsolatedFromAbove op
  | .gmir op => HasOpInfo.isIsolatedFromAbove op
  | .test op => HasOpInfo.isIsolatedFromAbove op
  | .felt op => HasOpInfo.isIsolatedFromAbove op
  | .cir op => HasOpInfo.isIsolatedFromAbove op
  | .include op => HasOpInfo.isIsolatedFromAbove op
  | .function op => HasOpInfo.isIsolatedFromAbove op
  | .seq op => HasOpInfo.isIsolatedFromAbove op
  | .catcrypt op => HasOpInfo.isIsolatedFromAbove op
  | .memref op => HasOpInfo.isIsolatedFromAbove op
  | .polynomial op => HasOpInfo.isIsolatedFromAbove op
  | .vector op => HasOpInfo.isIsolatedFromAbove op
  | .x86vector op => HasOpInfo.isIsolatedFromAbove op

/-- Whether this opcode carries MLIR's `SymbolTable` trait. -/
def OpCode.isSymbolTable (opCode : OpCode) : Bool :=
  match opCode with
  | .arith op => HasOpInfo.isSymbolTable op
  | .llvm op => HasOpInfo.isSymbolTable op
  | .riscv op => HasOpInfo.isSymbolTable op
  | .riscv_cf op => HasOpInfo.isSymbolTable op
  | .riscv_stack op => HasOpInfo.isSymbolTable op
  | .rv64 op => HasOpInfo.isSymbolTable op
  | .mod_arith op => HasOpInfo.isSymbolTable op
  | .cf op => HasOpInfo.isSymbolTable op
  | .comb op => HasOpInfo.isSymbolTable op
  | .hw op => HasOpInfo.isSymbolTable op
  | .verif op => HasOpInfo.isSymbolTable op
  | .builtin op => HasOpInfo.isSymbolTable op
  | .func op => HasOpInfo.isSymbolTable op
  | .datapath op => HasOpInfo.isSymbolTable op
  | .pdl op => HasOpInfo.isSymbolTable op
  | .io op => HasOpInfo.isSymbolTable op
  | .gmir op => HasOpInfo.isSymbolTable op
  | .test op => HasOpInfo.isSymbolTable op
  | .felt op => HasOpInfo.isSymbolTable op
  | .cir op => HasOpInfo.isSymbolTable op
  | .include op => HasOpInfo.isSymbolTable op
  | .function op => HasOpInfo.isSymbolTable op
  | .seq op => HasOpInfo.isSymbolTable op
  | .catcrypt op => HasOpInfo.isSymbolTable op
  | .memref op => HasOpInfo.isSymbolTable op
  | .polynomial op => HasOpInfo.isSymbolTable op
  | .vector op => HasOpInfo.isSymbolTable op
  | .x86vector op => HasOpInfo.isSymbolTable op
  | .field op => HasOpInfo.isSymbolTable op
  | .elliptic_curve op => HasOpInfo.isSymbolTable op
  | .poly op => HasOpInfo.isSymbolTable op
  | .ring op => HasOpInfo.isSymbolTable op
  | .tensor_ext op => HasOpInfo.isSymbolTable op

/--
  Does this OpCode count as an MLIR basic block terminator? Dialects that do
  not say otherwise inherit the `HasOpInfo` default of `false`.
-/
@[is_terminator]
def OpCode.isTerminator (opCode : OpCode) : Bool :=
  match opCode with
  | .arith op => HasOpInfo.isTerminator op
  | .llvm op => HasOpInfo.isTerminator op
  | .riscv op => HasOpInfo.isTerminator op
  | .riscv_cf op => HasOpInfo.isTerminator op
  | .riscv_stack op => HasOpInfo.isTerminator op
  | .rv64 op => HasOpInfo.isTerminator op
  | .mod_arith op => HasOpInfo.isTerminator op
  | .field op => HasOpInfo.isTerminator op
  | .elliptic_curve op => HasOpInfo.isTerminator op
  | .poly op => HasOpInfo.isTerminator op
  | .ring op => HasOpInfo.isTerminator op
  | .tensor_ext op => HasOpInfo.isTerminator op
  | .cf op => HasOpInfo.isTerminator op
  | .comb op => HasOpInfo.isTerminator op
  | .hw op => HasOpInfo.isTerminator op
  | .verif op => HasOpInfo.isTerminator op
  | .builtin op => HasOpInfo.isTerminator op
  | .func op => HasOpInfo.isTerminator op
  | .datapath op => HasOpInfo.isTerminator op
  | .pdl op => HasOpInfo.isTerminator op
  | .io op => HasOpInfo.isTerminator op
  | .gmir op => HasOpInfo.isTerminator op
  | .test op => HasOpInfo.isTerminator op
  | .felt op => HasOpInfo.isTerminator op
  | .cir op => HasOpInfo.isTerminator op
  | .include op => HasOpInfo.isTerminator op
  | .function op => HasOpInfo.isTerminator op
  | .seq op => HasOpInfo.isTerminator op
  | .catcrypt op => HasOpInfo.isTerminator op
  | .memref op => HasOpInfo.isTerminator op
  | .polynomial op => HasOpInfo.isTerminator op
  | .vector op => HasOpInfo.isTerminator op
  | .x86vector op => HasOpInfo.isTerminator op

/--
  Does this `OpCode` materialize a literal constant value, i.e. an op
  whose single result is a compile-time constant taken from its
  properties, with no SSA operands and no side effects?

  This is the analogue of MLIR's `ConstantLike` op trait, which likewise
  covers `llvm.mlir.poison`: poison is a perfectly good constant.
-/
def OpCode.isConstantLike (opCode : OpCode) : Bool :=
  match opCode with
  | .arith op => Arith.isConstantLike op
  | .llvm op => Llvm.isConstantLike op
  | .riscv op => Riscv.isConstantLike op
  | .riscv_cf op => Riscv_Cf.isConstantLike op
  | .riscv_stack op => Riscv_Stack.isConstantLike op
  | .rv64 op => Rv64.isConstantLike op
  | .mod_arith op => Mod_Arith.isConstantLike op
  | .field op => Field.isConstantLike op
  | .elliptic_curve op => Elliptic_Curve.isConstantLike op
  | .poly op => Poly.isConstantLike op
  | .ring op => Ring.isConstantLike op
  | .tensor_ext op => Tensor_Ext.isConstantLike op
  | .cf op => Cf.isConstantLike op
  | .comb op => Comb.isConstantLike op
  | .hw op => HW.isConstantLike op
  | .verif op => Verif.isConstantLike op
  | .builtin op => Builtin.isConstantLike op
  | .func op => Func.isConstantLike op
  | .datapath op => Datapath.isConstantLike op
  | .pdl op => PDL.isConstantLike op
  | .io op => Io.isConstantLike op
  | .gmir op => GMIR.isConstantLike op
  | .test op => Test.isConstantLike op
  | .felt op => Felt.isConstantLike op
  | .cir op => Cir.isConstantLike op
  | .include op => LLZK.Include.isConstantLike op
  | .function op => LLZK.Function.isConstantLike op
  | .seq op => Seq.isConstantLike op
  | .catcrypt op => Catcrypt.isConstantLike op
  | .memref op => Memref.isConstantLike op
  | .polynomial op => Polynomial.isConstantLike op
  | .vector op => Vector.isConstantLike op
  | .x86vector op => X86vector.isConstantLike op

/--
  Does an operation with this opcode produce a wholly poisoned result whenever
  any one of its operands is wholly poison?
-/
def OpCode.propagatesPoison (opCode : OpCode) : Bool :=
  match opCode with
  | .arith op => HasOpInfo.propagatesPoison op
  | .llvm op => HasOpInfo.propagatesPoison op
  | .riscv op => HasOpInfo.propagatesPoison op
  | .riscv_cf op => HasOpInfo.propagatesPoison op
  | .riscv_stack op => HasOpInfo.propagatesPoison op
  | .rv64 op => HasOpInfo.propagatesPoison op
  | .mod_arith op => HasOpInfo.propagatesPoison op
  | .field op => HasOpInfo.propagatesPoison op
  | .elliptic_curve op => HasOpInfo.propagatesPoison op
  | .poly op => HasOpInfo.propagatesPoison op
  | .ring op => HasOpInfo.propagatesPoison op
  | .tensor_ext op => HasOpInfo.propagatesPoison op
  | .cf op => HasOpInfo.propagatesPoison op
  | .comb op => HasOpInfo.propagatesPoison op
  | .hw op => HasOpInfo.propagatesPoison op
  | .verif op => HasOpInfo.propagatesPoison op
  | .builtin op => HasOpInfo.propagatesPoison op
  | .func op => HasOpInfo.propagatesPoison op
  | .datapath op => HasOpInfo.propagatesPoison op
  | .pdl op => HasOpInfo.propagatesPoison op
  | .io op => HasOpInfo.propagatesPoison op
  | .gmir op => HasOpInfo.propagatesPoison op
  | .test op => HasOpInfo.propagatesPoison op
  | .felt op => HasOpInfo.propagatesPoison op
  | .cir op => HasOpInfo.propagatesPoison op
  | .include op => HasOpInfo.propagatesPoison op
  | .function op => HasOpInfo.propagatesPoison op
  | .seq op => HasOpInfo.propagatesPoison op
  | .catcrypt op => HasOpInfo.propagatesPoison op
  | .memref op => HasOpInfo.propagatesPoison op
  | .polynomial op => HasOpInfo.propagatesPoison op
  | .vector op => HasOpInfo.propagatesPoison op
  | .x86vector op => HasOpInfo.propagatesPoison op

def Properties.fromAttrDict (opCode : OpCode) (attrDict : Std.HashMap ByteArray Attribute) :
    Except String (_propertiesOf opCode) :=
  match opCode with
  | .arith op => Arith.fromAttrDict op attrDict
  | .llvm op => Llvm.fromAttrDict op attrDict
  | .riscv op => Riscv.fromAttrDict op attrDict
  | .riscv_cf op => Riscv_Cf.fromAttrDict op attrDict
  | .riscv_stack op => Riscv_Stack.fromAttrDict op attrDict
  | .rv64 op => Rv64.fromAttrDict op attrDict
  | .mod_arith op => Mod_Arith.fromAttrDict op attrDict
  | .field op => Field.fromAttrDict op attrDict
  | .elliptic_curve op => Elliptic_Curve.fromAttrDict op attrDict
  | .poly op => Poly.fromAttrDict op attrDict
  | .ring op => Ring.fromAttrDict op attrDict
  | .tensor_ext op => Tensor_Ext.fromAttrDict op attrDict
  | .cf op => Cf.fromAttrDict op attrDict
  | .comb op => Comb.fromAttrDict op attrDict
  | .hw op => HW.fromAttrDict op attrDict
  | .verif op => Verif.fromAttrDict op attrDict
  | .builtin op => Builtin.fromAttrDict op attrDict
  | .func op => Func.fromAttrDict op attrDict
  | .datapath op => Datapath.fromAttrDict op attrDict
  | .pdl op => PDL.fromAttrDict op attrDict
  | .io op => Io.fromAttrDict op attrDict
  | .gmir op => GMIR.fromAttrDict op attrDict
  | .test op => Test.fromAttrDict op attrDict
  | .felt op => Felt.fromAttrDict op attrDict
  | .cir op => Cir.fromAttrDict op attrDict
  | .include op => LLZK.Include.fromAttrDict op attrDict
  | .function op => LLZK.Function.fromAttrDict op attrDict
  | .seq op => Seq.fromAttrDict op attrDict
  | .catcrypt op => Catcrypt.fromAttrDict op attrDict
  | .memref op => Memref.fromAttrDict op attrDict
  | .polynomial op => Polynomial.fromAttrDict op attrDict
  | .vector op => Vector.fromAttrDict op attrDict
  | .x86vector op => X86vector.fromAttrDict op attrDict

/--
  Converts the properties of an operation into a dictionary of attributes.
-/
def Properties.toAttrDict
    (opCode : OpCode) (props : _propertiesOf opCode) :
    Std.HashMap ByteArray Attribute :=
  match opCode, props with
  | .arith op, props => Arith.toAttrDict op props
  | .llvm op, props => Llvm.toAttrDict op props
  | .riscv op, props => Riscv.toAttrDict op props
  | .riscv_cf op, props => Riscv_Cf.toAttrDict op props
  | .riscv_stack op, props => Riscv_Stack.toAttrDict op props
  | .rv64 op, props => Rv64.toAttrDict op props
  | .mod_arith op, props => Mod_Arith.toAttrDict op props
  | .field op, props => Field.toAttrDict op props
  | .elliptic_curve op, props => Elliptic_Curve.toAttrDict op props
  | .poly op, props => Poly.toAttrDict op props
  | .ring op, props => Ring.toAttrDict op props
  | .tensor_ext op, props => Tensor_Ext.toAttrDict op props
  | .cf op, props => Cf.toAttrDict op props
  | .comb op, props => Comb.toAttrDict op props
  | .hw op, props => HW.toAttrDict op props
  | .verif op, props => Verif.toAttrDict op props
  | .builtin op, props => Builtin.toAttrDict op props
  | .func op, props => Func.toAttrDict op props
  | .datapath op, props => Datapath.toAttrDict op props
  | .pdl op, props => PDL.toAttrDict op props
  | .io op, props => Io.toAttrDict op props
  | .gmir op, props => GMIR.toAttrDict op props
  | .test op, props => Test.toAttrDict op props
  | .felt op, props => Felt.toAttrDict op props
  | .cir op, props => Cir.toAttrDict op props
  | .include op, props => LLZK.Include.toAttrDict op props
  | .function op, props => LLZK.Function.toAttrDict op props
  | .seq op, props => Seq.toAttrDict op props
  | .catcrypt op, props => Catcrypt.toAttrDict op props
  | .memref op, props => Memref.toAttrDict op props
  | .polynomial op, props => Polynomial.toAttrDict op props
  | .vector op, props => Vector.toAttrDict op props
  | .x86vector op, props => X86vector.toAttrDict op props

instance : IsOpCode OpCode where
  fromName := OpCode.fromName
  name := OpCode.name
  propertiesOf := _propertiesOf
  fromAttrDict := Properties.fromAttrDict
  toAttrDict := Properties.toAttrDict

/-- Symbol-interface information assembled from the registered dialects. -/
def OpCode.symbolInterface? (opCode : OpCode) : Option (SymbolOpInterface (_propertiesOf opCode)) :=
  match opCode with
  | .arith op => HasOpInfo.symbolInterface? op
  | .llvm op => HasOpInfo.symbolInterface? op
  | .riscv op => HasOpInfo.symbolInterface? op
  | .riscv_cf op => HasOpInfo.symbolInterface? op
  | .riscv_stack op => HasOpInfo.symbolInterface? op
  | .rv64 op => HasOpInfo.symbolInterface? op
  | .mod_arith op => HasOpInfo.symbolInterface? op
  | .cf op => HasOpInfo.symbolInterface? op
  | .comb op => HasOpInfo.symbolInterface? op
  | .hw op => HasOpInfo.symbolInterface? op
  | .verif op => HasOpInfo.symbolInterface? op
  | .builtin op => HasOpInfo.symbolInterface? op
  | .func op => HasOpInfo.symbolInterface? op
  | .datapath op => HasOpInfo.symbolInterface? op
  | .pdl op => HasOpInfo.symbolInterface? op
  | .io op => HasOpInfo.symbolInterface? op
  | .gmir op => HasOpInfo.symbolInterface? op
  | .test op => HasOpInfo.symbolInterface? op
  | .felt op => HasOpInfo.symbolInterface? op
  | .cir op => HasOpInfo.symbolInterface? op
  | .include op => HasOpInfo.symbolInterface? op
  | .function op => HasOpInfo.symbolInterface? op
  | .seq op => HasOpInfo.symbolInterface? op
  | .catcrypt op => HasOpInfo.symbolInterface? op
  | .memref op => HasOpInfo.symbolInterface? op
  | .polynomial op => HasOpInfo.symbolInterface? op
  | .vector op => HasOpInfo.symbolInterface? op
  | .x86vector op => HasOpInfo.symbolInterface? op
  | .field op => HasOpInfo.symbolInterface? op
  | .elliptic_curve op => HasOpInfo.symbolInterface? op
  | .poly op => HasOpInfo.symbolInterface? op
  | .ring op => HasOpInfo.symbolInterface? op
  | .tensor_ext op => HasOpInfo.symbolInterface? op

/-- Function-interface information assembled from the registered dialects. -/
def OpCode.functionInterface? (opCode : OpCode) : Option (FunctionOpInterface (_propertiesOf opCode)) :=
  match opCode with
  | .arith op => HasOpInfo.functionInterface? op
  | .llvm op => HasOpInfo.functionInterface? op
  | .riscv op => HasOpInfo.functionInterface? op
  | .riscv_cf op => HasOpInfo.functionInterface? op
  | .riscv_stack op => HasOpInfo.functionInterface? op
  | .rv64 op => HasOpInfo.functionInterface? op
  | .mod_arith op => HasOpInfo.functionInterface? op
  | .field op => HasOpInfo.functionInterface? op
  | .elliptic_curve op => HasOpInfo.functionInterface? op
  | .poly op => HasOpInfo.functionInterface? op
  | .ring op => HasOpInfo.functionInterface? op
  | .tensor_ext op => HasOpInfo.functionInterface? op
  | .cf op => HasOpInfo.functionInterface? op
  | .comb op => HasOpInfo.functionInterface? op
  | .hw op => HasOpInfo.functionInterface? op
  | .verif op => HasOpInfo.functionInterface? op
  | .builtin op => HasOpInfo.functionInterface? op
  | .func op => HasOpInfo.functionInterface? op
  | .datapath op => HasOpInfo.functionInterface? op
  | .pdl op => HasOpInfo.functionInterface? op
  | .io op => HasOpInfo.functionInterface? op
  | .gmir op => HasOpInfo.functionInterface? op
  | .test op => HasOpInfo.functionInterface? op
  | .felt op => HasOpInfo.functionInterface? op
  | .cir op => HasOpInfo.functionInterface? op
  | .include op => HasOpInfo.functionInterface? op
  | .function op => HasOpInfo.functionInterface? op
  | .seq op => HasOpInfo.functionInterface? op
  | .catcrypt op => HasOpInfo.functionInterface? op
  | .memref op => HasOpInfo.functionInterface? op
  | .polynomial op => HasOpInfo.functionInterface? op
  | .vector op => HasOpInfo.functionInterface? op
  | .x86vector op => HasOpInfo.functionInterface? op

theorem OpCode.functionInterface_requires_symbol {opCode : OpCode}
    {f : FunctionOpInterface (_propertiesOf opCode)}
    (h : OpCode.functionInterface? opCode = some f) :
    (OpCode.symbolInterface? opCode).isSome := by
  cases opCode <;> exact HasOpInfo.functionInterface_requires_symbol h

theorem OpCode.functionInterface_getSymName_isSome {opCode : OpCode}
    {f : FunctionOpInterface (_propertiesOf opCode)}
    {symbolInterface : SymbolOpInterface (_propertiesOf opCode)}
    (h : OpCode.functionInterface? opCode = some f)
    (hs : OpCode.symbolInterface? opCode = some symbolInterface) {props : _propertiesOf opCode} :
    (symbolInterface.getSymName props).isSome := by
  cases opCode <;> exact HasOpInfo.functionInterface_getSymName_isSome h hs

/-- Branch-interface information assembled from the registered dialects. -/
def OpCode.branchOpInterface?
    (opCode : OpCode) : Option (BranchOpInterface (_propertiesOf opCode)) :=
  match opCode with
  | .arith op => HasOpInfo.branchOpInterface? op
  | .llvm op => HasOpInfo.branchOpInterface? op
  | .riscv op => HasOpInfo.branchOpInterface? op
  | .riscv_cf op => HasOpInfo.branchOpInterface? op
  | .riscv_stack op => HasOpInfo.branchOpInterface? op
  | .rv64 op => HasOpInfo.branchOpInterface? op
  | .mod_arith op => HasOpInfo.branchOpInterface? op
  | .cf op => HasOpInfo.branchOpInterface? op
  | .comb op => HasOpInfo.branchOpInterface? op
  | .hw op => HasOpInfo.branchOpInterface? op
  | .verif op => HasOpInfo.branchOpInterface? op
  | .builtin op => HasOpInfo.branchOpInterface? op
  | .func op => HasOpInfo.branchOpInterface? op
  | .datapath op => HasOpInfo.branchOpInterface? op
  | .pdl op => HasOpInfo.branchOpInterface? op
  | .io op => HasOpInfo.branchOpInterface? op
  | .gmir op => HasOpInfo.branchOpInterface? op
  | .test op => HasOpInfo.branchOpInterface? op
  | .felt op => HasOpInfo.branchOpInterface? op
  | .cir op => HasOpInfo.branchOpInterface? op
  | .include op => HasOpInfo.branchOpInterface? op
  | .function op => HasOpInfo.branchOpInterface? op
  | .seq op => HasOpInfo.branchOpInterface? op
  | .catcrypt op => HasOpInfo.branchOpInterface? op
  | .memref op => HasOpInfo.branchOpInterface? op
  | .polynomial op => HasOpInfo.branchOpInterface? op
  | .vector op => HasOpInfo.branchOpInterface? op
  | .x86vector op => HasOpInfo.branchOpInterface? op
  | .field op => HasOpInfo.branchOpInterface? op
  | .elliptic_curve op => HasOpInfo.branchOpInterface? op
  | .poly op => HasOpInfo.branchOpInterface? op
  | .ring op => HasOpInfo.branchOpInterface? op
  | .tensor_ext op => HasOpInfo.branchOpInterface? op

/-- Call-interface information assembled from the registered dialects. -/
def OpCode.callOpInterface?
    (opCode : OpCode) : Option (CallOpInterface (_propertiesOf opCode)) :=
  match opCode with
  | .arith op => HasOpInfo.callOpInterface? op
  | .llvm op => HasOpInfo.callOpInterface? op
  | .riscv op => HasOpInfo.callOpInterface? op
  | .riscv_cf op => HasOpInfo.callOpInterface? op
  | .riscv_stack op => HasOpInfo.callOpInterface? op
  | .rv64 op => HasOpInfo.callOpInterface? op
  | .mod_arith op => HasOpInfo.callOpInterface? op
  | .cf op => HasOpInfo.callOpInterface? op
  | .comb op => HasOpInfo.callOpInterface? op
  | .hw op => HasOpInfo.callOpInterface? op
  | .verif op => HasOpInfo.callOpInterface? op
  | .builtin op => HasOpInfo.callOpInterface? op
  | .func op => HasOpInfo.callOpInterface? op
  | .datapath op => HasOpInfo.callOpInterface? op
  | .pdl op => HasOpInfo.callOpInterface? op
  | .io op => HasOpInfo.callOpInterface? op
  | .gmir op => HasOpInfo.callOpInterface? op
  | .test op => HasOpInfo.callOpInterface? op
  | .felt op => HasOpInfo.callOpInterface? op
  | .cir op => HasOpInfo.callOpInterface? op
  | .include op => HasOpInfo.callOpInterface? op
  | .function op => HasOpInfo.callOpInterface? op
  | .seq op => HasOpInfo.callOpInterface? op
  | .catcrypt op => HasOpInfo.callOpInterface? op
  | .memref op => HasOpInfo.callOpInterface? op
  | .polynomial op => HasOpInfo.callOpInterface? op
  | .vector op => HasOpInfo.callOpInterface? op
  | .x86vector op => HasOpInfo.callOpInterface? op
  | .field op => HasOpInfo.callOpInterface? op
  | .elliptic_curve op => HasOpInfo.callOpInterface? op
  | .poly op => HasOpInfo.callOpInterface? op
  | .ring op => HasOpInfo.callOpInterface? op
  | .tensor_ext op => HasOpInfo.callOpInterface? op

#generate_has_dialect_instances OpCode

@[expose]
def OpCode.verifyLocalInvariants (opCode : OpCode) (op : OperationPtr)
    (ctx : WfIRContext OpCode) (opIn : op.InBounds ctx.raw) : Except String Unit :=
  match opCode with
  | .builtin opType => Builtin.verifyLocalInvariants opType op ctx opIn
  | .arith opType => Arith.verifyLocalInvariants opType op ctx opIn
  | .datapath opType => Datapath.verifyLocalInvariants opType op ctx opIn
  | .func opType => Func.verifyLocalInvariants opType op ctx opIn
  | .cf opType => Cf.verifyLocalInvariants opType op ctx opIn
  | .pdl opType => PDL.verifyLocalInvariants opType op ctx opIn
  | .test .test => pure ()
  | .llvm opType => Llvm.verifyLocalInvariants opType op ctx opIn
  | .mod_arith opType => Mod_Arith.verifyLocalInvariants opType op ctx opIn
  | .field opType => Field.verifyLocalInvariants opType op ctx opIn
  | .elliptic_curve opType => Elliptic_Curve.verifyLocalInvariants opType op ctx opIn
  | .poly opType => Poly.verifyLocalInvariants opType op ctx opIn
  | .ring opType => Ring.verifyLocalInvariants opType op ctx opIn
  | .tensor_ext opType => Tensor_Ext.verifyLocalInvariants opType op ctx opIn
  | .riscv opType => Riscv.verifyLocalInvariants opType op ctx opIn
  | .riscv_cf opType =>
    Riscv_Cf.verifyLocalInvariants OpCode.functionInterface? opType op ctx opIn
  | .riscv_stack opType => Riscv_Stack.verifyLocalInvariants opType op ctx opIn
  | .gmir opType => GMIR.verifyLocalInvariants opType op ctx opIn
  | .rv64 opType => Rv64.verifyLocalInvariants opType op ctx opIn
  | .comb opType => Comb.verifyLocalInvariants opType op ctx opIn
  | .hw opType => HW.verifyLocalInvariants opType op ctx opIn
  | .verif opType => Verif.verifyLocalInvariants opType op ctx opIn
  | .felt opType => Felt.verifyLocalInvariants opType op ctx opIn
  | .cir opType => Cir.verifyLocalInvariants opType op ctx opIn
  | .io opType => Io.verifyLocalInvariants opType op ctx opIn
  | .include opType => LLZK.Include.verifyLocalInvariants opType op ctx opIn
  | .function opType => LLZK.Function.verifyLocalInvariants opType op ctx opIn
  | .seq opType => Seq.verifyLocalInvariants opType op ctx opIn
  | .catcrypt opType => Catcrypt.verifyLocalInvariants opType op ctx opIn
  | .memref opType => Memref.verifyLocalInvariants opType op ctx opIn
  | .polynomial opType => Polynomial.verifyLocalInvariants opType op ctx opIn
  | .vector opType => Vector.verifyLocalInvariants opType op ctx opIn
  | .x86vector opType => X86vector.verifyLocalInvariants opType op ctx opIn

instance : HasOpInfo OpCode where
  verifyLocalInvariants := OpCode.verifyLocalInvariants
  tryFold := OpCode.tryFold
  getEffects := OpCode.getEffects
  isConstantLike := OpCode.isConstantLike
  propagatesPoison := OpCode.propagatesPoison
  symbolInterface? := OpCode.symbolInterface?
  functionInterface? := OpCode.functionInterface?
  functionInterface_requires_symbol := OpCode.functionInterface_requires_symbol
  functionInterface_getSymName_isSome := OpCode.functionInterface_getSymName_isSome
  callOpInterface? := OpCode.callOpInterface?
  branchOpInterface? := OpCode.branchOpInterface?
  getRegionKind := OpCode.getRegionKind
  hasSSADominance := OpCode.hasSSADominance
  hasNoTerminator := OpCode.hasNoTerminator
  isTerminator := OpCode.isTerminator
  isIsolatedFromAbove := OpCode.isIsolatedFromAbove
  isSymbolTable := OpCode.isSymbolTable

/--
Ask the dialect of `opCode` how to represent a folded
constant. Dialects without a materializer, and values a dialect cannot
represent, decline to fold.
-/
def OpCode.materializeConstant (opCode : OpCode) (value : RuntimeValue)
    (type : TypeAttr) : Option (Materialized OpCode) := do
  let materialized ←
    match opCode with
    | .arith op => Arith.materializeConstant op value type
    | .comb op => Comb.materializeConstant op value type
    | .hw op => HW.materializeConstant op value type
    | .llvm op => Llvm.materializeConstant op value type
    | .mod_arith op => Mod_Arith.materializeConstant op value type
    | .riscv op => Riscv.materializeConstant op value type
    | .felt op => Felt.materializeConstant op value type
    -- Listed rather than folded into a catch-all so that adding a dialect
    -- fails to compile until it decides how, or whether, to materialize.
    | .riscv_cf _ | .riscv_stack _ | .rv64 _ | .cf _ | .builtin _
    | .verif _
    | .func _ | .datapath _ | .pdl _ | .test _ | .cir _ | .io _ | .include _
    | .function _ | .seq _ | .gmir _
    | .catcrypt _ | .memref _ | .polynomial _ | .vector _ | .x86vector _ | .field _
    | .elliptic_curve _ | .poly _ | .ring _ | .tensor_ext _ => none
  guard materialized.fst.isConstantLike
  return materialized

/--
  The unconditional branch that replaces a branch of `opCode`'s dialect once
  its successor is known, preserving applicable properties such as LLVM loop
  annotations.
-/
def OpCode.unconditionalBranch? (opCode : OpCode) (props : propertiesOf opCode) :
    Option (Σ op : OpCode, propertiesOf op) :=
  match opCode, props with
  | .cf _, _ => some (Materialized.of Cf.br ())
  | .llvm .br, props => some (Materialized.of Llvm.br props)
  | .llvm .cond_br, props =>
    some (Materialized.of Llvm.br ({ loop_annotation := props.loop_annotation } : LLVMBrProperties))
  | .llvm _, _ => some (Materialized.of Llvm.br ({ loop_annotation := none } : LLVMBrProperties))
  | .riscv_cf _, _ => some (Materialized.of Riscv_Cf.branch ())
  | _, _ => none

/--
  Is this `OpCode` commutative in its operands, i.e. `op x y` always
  computes the same value as `op y x`?
-/
def OpCode.isCommutative (opCode : OpCode) : Bool :=
  match opCode with
  | .arith .addi | .arith .muli
  | .arith .andi | .arith .ori | .arith .xori
  | .arith .maxsi | .arith .maxui | .arith .minsi | .arith .minui
  | .arith .addui_extended
  | .arith .mulsi_extended | .arith .mului_extended
  | .llvm .add | .llvm .mul
  | .llvm .and | .llvm .or | .llvm .xor
  | .llvm .intr__smax | .llvm .intr__smin | .llvm .intr__umax | .llvm .intr__umin
  | .llvm .intr__sadd__sat | .llvm .intr__uadd__sat
  | .llvm .fadd | .llvm .fmul
  | .riscv .add | .riscv .and | .riscv .or | .riscv .xor | .riscv .xnor
  | .riscv .mul | .riscv .mulh | .riscv .mulhu
  | .riscv .max | .riscv .maxu | .riscv .min | .riscv .minu
  | .riscv .addw | .riscv .mulw
  | .mod_arith .add | .mod_arith .mul
  | .field .add | .field .mul
  | .elliptic_curve .add | .ring .add | .ring .mul
  | .felt .add | .felt .mul
  | .felt .bit_and | .felt .bit_or | .felt .bit_xor
  | .cir .add | .cir .mul | .cir .and | .cir .or | .cir .xor | .cir .min | .cir .max => true
  | _ => false

instance : HasCustomPrinting OpCode OpCode where
  customPrinter?
    | .func f =>
      HasCustomPrinting.customPrinter?
        (Dialect := Func) (GlobalOpCode := OpCode) f
    | _ => none
