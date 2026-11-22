module

public import Veir.Interpreter.Basic
import all Veir.Interpreter.Basic
import all Init.Internal.Order.Basic

/-!
# Calls in the interpreter

The interpretation is monotone in the call oracle (`interpretFunction_rel` and the lemmas before
it), which makes `interpretSym`, the oracle of a module, a single `partial_fixpoint`. The
unfolding lemmas of `interpretSym` and the lemmas on the interpretation of a call
operation follow.
-/

public section
namespace Veir
open Lean.Order

theorem Interp.bind_rel {α β : Type} {x y : Interp α} {f g : α → Interp β} (hx : x ⊑ y)
    (hf : ∀ a, f a ⊑ g a) : (x >>= f) ⊑ (y >>= g) :=
  PartialOrder.rel_trans (MonoBind.bind_mono_left hx) (MonoBind.bind_mono_right hf)

variable {ctx : WfIRContext OpCode}

theorem interpretCall_rel {g₁ g₂ : CallOracle} (hg : ∀ s a m, g₁ s a m ⊑ g₂ s a m)
    (callee : Option String) (op : OperationPtr) (state : InterpreterState ctx)
    (h : op.InBounds ctx.raw) :
    interpretCall g₁ callee op state h ⊑ interpretCall g₂ callee op state h := by
  unfold interpretCall
  split
  · apply Interp.bind_rel PartialOrder.rel_refl
    intro sa
    apply Interp.bind_rel (hg _ _ _)
    intro _
    exact PartialOrder.rel_refl
  · exact PartialOrder.rel_refl

theorem interpretOpWith_rel {g₁ g₂ : CallOracle} (hg : ∀ s a m, g₁ s a m ⊑ g₂ s a m)
    (op : OperationPtr) (state : InterpreterState ctx) (h : op.InBounds ctx.raw) :
    interpretOpWith (some g₁) op state h ⊑ interpretOpWith (some g₂) op state h := by
  rcases hc : op.callee? ctx.raw with _ | callee
  · simp only [interpretOpWith, hc]; exact PartialOrder.rel_refl
  · simp only [interpretOpWith, hc]; exact interpretCall_rel hg _ _ _ _

theorem interpretOpChain_rel {g₁ g₂ : CallOracle} (hg : ∀ s a m, g₁ s a m ⊑ g₂ s a m) :
    ∀ (n : Nat) (op : OperationPtr) (state : InterpreterState ctx) (h : op.InBounds ctx.raw),
      op.idxInParentFromTail ctx.raw = n →
      interpretOpChain op state h (some g₁) ⊑ interpretOpChain op state h (some g₂) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro op state h hn
    rw [interpretOpChain.eq_1, interpretOpChain.eq_1]
    apply Interp.bind_rel (interpretOpWith_rel hg op state h)
    rintro ⟨state', action⟩
    cases action with
    | some a => exact PartialOrder.rel_refl
    | none =>
      dsimp only
      split
      · exact PartialOrder.rel_refl
      · rename_i next hnext
        exact ih _ (by grind) next state' _ rfl


theorem interpretBlock_rel {g₁ g₂ : CallOracle} (hg : ∀ s a m, g₁ s a m ⊑ g₂ s a m)
    (b : BlockPtr) (values : Array RuntimeValue) (state : InterpreterState ctx)
    (h : b.InBounds ctx.raw) :
    interpretBlock b values state h (some g₁) ⊑ interpretBlock b values state h (some g₂) := by
  unfold interpretBlock
  apply Interp.bind_rel PartialOrder.rel_refl
  intro vars
  dsimp only
  split
  · exact PartialOrder.rel_refl
  · exact interpretOpChain_rel hg _ _ _ _ rfl

theorem interpretBlockCFG_rel {g₁ g₂ : CallOracle} (hg : ∀ s a m, g₁ s a m ⊑ g₂ s a m) :
    ∀ (b : BlockPtr) (values : Array RuntimeValue) (state : InterpreterState ctx)
      (h : b.InBounds ctx.raw),
      interpretBlockCFG b values state h (some g₁) ⊑ interpretBlockCFG b values state h (some g₂) := by
  refine interpretBlockCFG.fixpoint_induct (some g₁)
    (fun f => ∀ b values state h, f b values state h ⊑ interpretBlockCFG b values state h (some g₂))
    ?_ ?_
  · refine admissible_pi_apply (β := fun b => Array RuntimeValue → InterpreterState ctx →
        b.InBounds ctx.raw → Interp (InterpreterState ctx × Array RuntimeValue))
      (fun b fb => ∀ values state h, fb values state h ⊑ interpretBlockCFG b values state h (some g₂))
      fun b => ?_
    refine admissible_pi_apply (β := fun _ => InterpreterState ctx →
        b.InBounds ctx.raw → Interp (InterpreterState ctx × Array RuntimeValue))
      (fun values fv => ∀ state h, fv state h ⊑ interpretBlockCFG b values state h (some g₂))
      fun values => ?_
    refine admissible_pi_apply (β := fun _ =>
        b.InBounds ctx.raw → Interp (InterpreterState ctx × Array RuntimeValue))
      (fun state fs => ∀ h, fs h ⊑ interpretBlockCFG b values state h (some g₂))
      fun state => ?_
    refine admissible_pi_apply (β := fun _ => Interp (InterpreterState ctx × Array RuntimeValue))
      (fun h fh => fh ⊑ interpretBlockCFG b values state h (some g₂))
      fun h => ?_
    exact Interp.admissible_of_ub _ (Interp.rel_iff.mpr (.inl rfl))
  · intro f hf b values state h
    rw [interpretBlockCFG.eq_1 (call := some g₂)]
    dsimp only
    rcases Interp.rel_iff.mp (interpretBlock_rel hg b values state h) with heq | heq
    · rw [heq]; exact Interp.rel_iff.mpr (.inl rfl)
    · rw [← heq]
      split
      · exact PartialOrder.rel_refl
      · split
        · exact hf _ _ _ _
        · exact PartialOrder.rel_refl
      · exact PartialOrder.rel_refl
      · exact PartialOrder.rel_refl

theorem interpretRegion_rel {g₁ g₂ : CallOracle} (hg : ∀ s a m, g₁ s a m ⊑ g₂ s a m)
    (r : RegionPtr) (values : Array RuntimeValue) (state : InterpreterState ctx)
    (h : r.InBounds ctx.raw) :
    interpretRegion r values state h (some g₁) ⊑ interpretRegion r values state h (some g₂) := by
  unfold interpretRegion
  split
  · exact PartialOrder.rel_refl
  · exact interpretBlockCFG_rel hg _ _ _ _

theorem interpretFunction_rel {g₁ g₂ : CallOracle} (hg : ∀ s a m, g₁ s a m ⊑ g₂ s a m)
    {op : OperationPtr} (f : FunctionOp ctx.raw op) (values : Array RuntimeValue)
    (mem : MemoryState) (h : op.InBounds ctx.raw) :
    interpretFunction f values mem h (some g₁) ⊑ interpretFunction f values mem h (some g₂) := by
  unfold interpretFunction
  split
  · exact PartialOrder.rel_refl
  · exact Interp.bind_rel (interpretRegion_rel hg _ _ _ _) fun _ => PartialOrder.rel_refl


/-- The functions and the interpreted externals of a module, by symbol. -/
structure ModuleEnv (ctx : WfIRContext OpCode) where
  functions : Std.HashMap String
    {op : OperationPtr // op.InBounds ctx.raw ∧ (FunctionOp.of? op ctx.raw).isSome}
  externals : String → Option (Array RuntimeValue → MemoryState →
    Interp (MemoryState × Array RuntimeValue))
  /-- The global variables of the module with their initial bytes. -/
  globals : List (String × ByteArray) := []

/-- The `FunctionOp` of a function of a module environment. -/
@[expose]
def ModuleEnv.funcOp
    (f : {op : OperationPtr // op.InBounds ctx.raw ∧ (FunctionOp.of? op ctx.raw).isSome}) :
    FunctionOp ctx.raw f.1 :=
  (FunctionOp.of? f.1 ctx.raw).get f.2.2

/-- The knot: a call of `sym` runs the body of the function `sym` of the module, with calls
    resolved by `interpretSym` itself, or the external `sym`; an unknown symbol is UB. -/
def interpretSym (M : ModuleEnv ctx) (sym : String) (args : Array RuntimeValue)
    (mem : MemoryState) : Interp (MemoryState × Array RuntimeValue) :=
  match M.functions[sym]?, M.externals sym with
  | some f, _ => interpretFunction (ModuleEnv.funcOp f) args mem f.2.1 (some (interpretSym M))
  | none, some g => g args mem
  | none, none => .ub none
partial_fixpoint monotonicity by
  intro x y hxy sym args mem
  dsimp only
  split
  · exact interpretFunction_rel (fun s a m => hxy s a m) _ _ _ _
  · exact PartialOrder.rel_refl
  · exact PartialOrder.rel_refl

/-! ## Unfolding `interpretSym` -/

theorem interpretSym_eq_function (M : ModuleEnv ctx) {s : String} {f}
    (hf : M.functions[s]? = some f) (args : Array RuntimeValue) (mem : MemoryState) :
    interpretSym M s args mem =
      interpretFunction (ModuleEnv.funcOp f) args mem f.2.1 (some (interpretSym M)) := by
  rw [interpretSym.eq_1]; simp only [hf]

theorem interpretSym_eq_external (M : ModuleEnv ctx) {s : String} {g}
    (hf : M.functions[s]? = none) (hg : M.externals s = some g)
    (args : Array RuntimeValue) (mem : MemoryState) :
    interpretSym M s args mem = g args mem := by
  rw [interpretSym.eq_1]; simp only [hf, hg]

theorem interpretSym_eq_ub (M : ModuleEnv ctx) {s : String}
    (hf : M.functions[s]? = none) (hg : M.externals s = none)
    (args : Array RuntimeValue) (mem : MemoryState) :
    interpretSym M s args mem = .ub none := by
  rw [interpretSym.eq_1]; simp only [hf, hg]

/-! ## Interpreting a call operation -/

theorem callee?_llvm_call {op : OperationPtr} {c : IRContext OpCode}
    (h : op.getOpType! c = .llvm .call) :
    op.callee? c = some ((op.getProperties! c (OpCode.llvm .call) : LLVMCallProperties).callee.map
      (·.value)) := by
  unfold OperationPtr.callee?; rw [h]

theorem callee?_func_call {op : OperationPtr} {c : IRContext OpCode}
    (h : op.getOpType! c = .func .call) :
    op.callee? c = some (some (op.getProperties! c (OpCode.func .call) : FuncCallProperties).callee.value) := by
  unfold OperationPtr.callee?; rw [h]

/-- A direct call `llvm.call @s` or `func.call @s` with operand values `vs` runs the oracle at
    `s` on `vs` and the memory, and sets the results to what the oracle returns. -/
theorem interpretOp_call_direct (c : CallOracle) {op : OperationPtr} (state : InterpreterState ctx)
    (h : op.InBounds ctx.raw) {s : String} {vs : Array RuntimeValue}
    (hcallee : op.callee? ctx.raw = some (some s))
    (hops : state.variables.getOperandValues op = some vs) :
    interpretOpWith (some c) op state h = (do
      let (mem', rs) ← c s vs state.memory
      let newVars ← Interp.withBlame op (state.variables.setResultValues? op rs : Interp _)
      return (⟨newVars, mem'⟩, none)) := by
  simp only [interpretOpWith, hcallee, interpretCall, hops, resolveCallee, Interp.withBlame_ok,
    Interp.bind_ok]

/-- An indirect call through a pointer to the start of the object of the symbol `s` runs the
    oracle at `s` on the remaining operands. -/
theorem interpretOp_call_indirect (c : CallOracle) {op : OperationPtr} (state : InterpreterState ctx)
    (h : op.InBounds ctx.raw) {s : String} {vs : Array RuntimeValue} {p : Data.Pointer}
    (hcallee : op.callee? ctx.raw = some none)
    (hops : state.variables.getOperandValues op = some vs)
    (hp : vs[0]? = some (.addr (.val p))) (hs : state.memory.globalAt? p = some s) :
    interpretOpWith (some c) op state h = (do
      let (mem', rs) ← c s (vs.extract 1) state.memory
      let newVars ← Interp.withBlame op (state.variables.setResultValues? op rs : Interp _)
      return (⟨newVars, mem'⟩, none)) := by
  simp only [interpretOpWith, hcallee, interpretCall, hops, resolveCallee, hp, hs,
    Interp.withBlame_ok, Interp.bind_ok]

/-- An indirect call through a poison pointer is UB. -/
theorem interpretOp_call_indirect_poison (c : CallOracle) {op : OperationPtr}
    (state : InterpreterState ctx) (h : op.InBounds ctx.raw) {vs : Array RuntimeValue}
    (hcallee : op.callee? ctx.raw = some none)
    (hops : state.variables.getOperandValues op = some vs)
    (hp : vs[0]? = some (.addr .poison)) :
    interpretOpWith (some c) op state h = .ub (some op) := by
  simp only [interpretOpWith, hcallee, interpretCall, hops, resolveCallee, hp]
  rfl

/-- An indirect call through a pointer that is not the start of a function or global object
    is UB. -/
theorem interpretOp_call_indirect_nonfunction (c : CallOracle) {op : OperationPtr}
    (state : InterpreterState ctx) (h : op.InBounds ctx.raw) {vs : Array RuntimeValue}
    {p : Data.Pointer}
    (hcallee : op.callee? ctx.raw = some none)
    (hops : state.variables.getOperandValues op = some vs)
    (hp : vs[0]? = some (.addr (.val p))) (hs : state.memory.globalAt? p = none) :
    interpretOpWith (some c) op state h = .ub (some op) := by
  simp only [interpretOpWith, hcallee, interpretCall, hops, resolveCallee, hp, hs]
  rfl

end Veir
