module

public import Veir.Interpreter.Refinement.Basic
public import Veir.Interpreter.Refinement.Lemmas
public import Veir.Interpreter.Calls
public import RefinementWP
import all Veir.Interpreter.Refinement.Basic
import all Veir.Interpreter.Calls
import all Init.Internal.Order.Basic

/-!
# VeIR's refinement as an instance of `RefinementWP.Refines`

The `Std.WP` instance of `Interp` (`Prop` assertions, no exception postcondition), the
equivalence of `Interp.isRefinedBy` with `RefinementWP.Refines` at the identity concretization,
the equivalence of `FunctionOp.isRefinedBy` with a `Refines` of state transformers
of the memory at the concretization of memory refinement, and the monotonicity of
the module oracle `interpretSym`.
-/

public section

namespace Veir

open Std.WP Lean.Order RefinementWP

/-- The weakest precondition of an interpretation: `Prop` assertions and no exception
    postcondition; `ok a` establishes `Q` when `Q a`, and `ub` and `fail` establish nothing. -/
instance Interp.instWP {α : Type} : WP (Interp α) α Prop EStack⟨⟩ where
  trans x := ⟨fun Q _ => match x with
    | .ok a => Q a
    | .ub _ => False
    | .fail _ => False⟩
  trans_monotone x := fun _ _ _ _ _ hQ => by
    cases x with
    | ok a => exact hQ a
    | ub _ => exact id
    | fail _ => exact id

@[simp] theorem Interp.wp_ok {α : Type} (a : α) (Q : α → Prop) (E : EStack⟨⟩) :
    wp (Interp.ok a) Q E = Q a := rfl
@[simp] theorem Interp.wp_ub {α : Type} (op : Option OperationPtr) (Q : α → Prop) (E : EStack⟨⟩) :
    wp (Interp.ub op : Interp α) Q E = False := rfl
@[simp] theorem Interp.wp_fail {α : Type} (op : Option OperationPtr) (Q : α → Prop)
    (E : EStack⟨⟩) : wp (Interp.fail op : Interp α) Q E = False := rfl

/-- `Interp` is a `WPMonad`: `wp` of `pure` and of `>>=` is exact. -/
instance Interp.instWPMonad : WPMonad Interp Prop EStack⟨⟩ where
  toWP _ := inferInstance
  pure_le_wp_pure _ _ _ := PartialOrder.rel_refl
  bind_le_wp_bind x f _ _ := by cases x <;> exact id

/-- The `wp` of a bind is the composite `wp` (the hypothesis of `Refines.bind`). -/
theorem Interp.wp_bind_le {α β : Type} (x : Interp α) (f : α → Interp β) (Q : β → Prop)
    (E : EStack⟨⟩) : wp (x >>= f) Q E ⊑ wp x (fun v => wp (f v) Q E) E := by
  cases x <;> exact id

theorem refines_iff_prop {α β : Type} (s : Interp α) (t : Interp β) (Q : β → α → Prop) :
    Refines (⊤ : Prop) Concretization.id (fun _ : EStack⟨⟩ => (⊥ : EStack⟨⟩)) t s Q ↔
      ∀ Qa : α → Prop, wp s Qa ⊥ → wp t (fun cv => ∃ av, Q cv av ∧ Qa av) ⊥ := by
  have hpost : ∀ Qa : α → Prop,
      (Concretization.id : Concretization Prop Prop).post Q Qa =
        fun cv => ∃ av, Q cv av ∧ Qa av := by
    intro Qa; funext cv
    simp only [Concretization.post, Concretization.id, iSup_prop_eq_exists, meet_prop_eq_and]
  rw [refines_top_iff]
  constructor
  · intro h Qa hs
    have := h Qa ⊥ hs
    rw [hpost] at this
    exact this
  · intro h Qa Ea hs
    have := h Qa hs
    rw [hpost]
    exact this

/-- `Interp.isRefinedBy R s t` is the refinement of the source `s` by the target `t`
    at the identity concretization, the exception map with value `⊥`, and the return relation
    `fun cv av => R av cv` (target value first). -/
theorem interp_isRefinedBy_iff_refines {α β : Type} (R : α → β → Prop) (s : Interp α)
    (t : Interp β) :
    Interp.isRefinedBy R s t ↔
      Refines (⊤ : Prop) Concretization.id (fun _ : EStack⟨⟩ => (⊥ : EStack⟨⟩)) t s
        (fun cv av => R av cv) := by
  rw [refines_iff_prop]
  constructor
  · intro h Qa hs
    cases s with
    | ok a =>
      cases t with
      | ok b => exact ⟨a, h, hs⟩
      | ub _ => exact h.elim
      | fail _ => exact h.elim
    | ub _ => exact hs.elim
    | fail _ => exact hs.elim
  · intro h
    cases s with
    | ok a =>
      have := h (· = a) rfl
      cases t with
      | ok b =>
        obtain ⟨av, hR, rfl⟩ := this
        exact hR
      | ub _ => exact this.elim
      | fail _ => exact this.elim
    | ub _ => trivial
    | fail _ => trivial

theorem Interp.wp_stateT {σ α : Type} (S : StateT σ Interp α) (Q : α → σ → Prop) (E : EStack⟨⟩)
    (m : σ) : wp S Q E m = wp (S m) (fun p => Q p.1 p.2) E := rfl

/-- Refinement of a state transformer over `Interp` at the concretization of a state relation is
    the forward simulation of the source by the target. -/
theorem refines_stateT_iff {σ A α β : Type} (S : StateT A Interp α) (T : StateT σ Interp β)
    (SR : σ → A → Prop) (Rv : β → α → Prop) :
    Refines (⊤ : σ → Prop) (Concretization.ofStateRel SR) (fun _ : EStack⟨⟩ => (⊥ : EStack⟨⟩))
        T S (fun cv av _ => Rv cv av) ↔
      ∀ mt ms, SR mt ms →
        Interp.isRefinedBy (fun (p : α × A) (q : β × σ) => Rv q.1 p.1 ∧ SR q.2 p.2) (S ms) (T mt) := by
  rw [refines_top_iff]
  constructor
  · intro h mt ms hSR
    cases hS : S ms with
    | ub _ => trivial
    | fail _ => trivial
    | ok p =>
      have h' := h (fun a m => a = p.1 ∧ m = p.2) ⊥ mt ⟨ms, hSR, by
        rw [Interp.wp_stateT, hS]; exact ⟨rfl, rfl⟩⟩
      rw [Interp.wp_stateT] at h'
      cases hT : T mt with
      | ub _ => rw [hT] at h'; exact h'.elim
      | fail _ => rw [hT] at h'; exact h'.elim
      | ok q =>
        rw [hT, Interp.wp_ok] at h'
        obtain ⟨av, hR, hpred⟩ := (Concretization.post_apply _ _ _ _ _).1 h'
        simp only [Concretization.ofStateRel] at hpred
        obtain ⟨m, hm, rfl, rfl⟩ := hpred
        exact ⟨hR, hm⟩
  · intro h Qa Ea mt ⟨ms, hSR, hwp⟩
    have h' := h mt ms hSR
    rw [Interp.wp_stateT] at hwp ⊢
    cases hS : S ms with
    | ub _ => rw [hS] at hwp; exact hwp.elim
    | fail _ => rw [hS] at hwp; exact hwp.elim
    | ok p =>
      rw [hS] at hwp h'
      cases hT : T mt with
      | ub _ => rw [hT] at h'; exact h'.elim
      | fail _ => rw [hT] at h'; exact h'.elim
      | ok q =>
        rw [hT] at h'
        rw [Interp.wp_ok]
        refine (Concretization.post_apply _ _ _ _ _).2 ⟨p.1, h'.1, ?_⟩
        simp only [Concretization.ofStateRel]
        exact ⟨p.2, h'.2, hwp⟩

/-- Reflexivity through `RefinementWP.Refines.refl`: an interpretation refines itself at the
    identity concretization and the equality return relation. -/
theorem interp_refines_refl {α : Type} (s : Interp α) :
    Refines (⊤ : Prop) Concretization.id (fun e : EStack⟨⟩ => e) s s (eqRel (CPred := Prop)) :=
  Refines.refl _ s

/-- Horizontal composition through `RefinementWP.Refines.bind`: refinement of interpretations
    is preserved by `>>=` with refining continuations. -/
theorem interp_isRefinedBy_bind {α β α' β' : Type} {R : α → β → Prop} {S : α' → β' → Prop}
    {s : Interp α} {t : Interp β} {k : α → Interp α'} {k' : β → Interp β'}
    (h : Interp.isRefinedBy R s t) (hk : ∀ a b, R a b → Interp.isRefinedBy S (k a) (k' b)) :
    Interp.isRefinedBy S (s >>= k) (t >>= k') := by
  rw [interp_isRefinedBy_iff_refines] at h ⊢
  refine Refines.bind (fun Qa Ea => Interp.wp_bind_le s k Qa Ea) h fun b a => ?_
  apply wrp_intro
  intro Qa Ea hpre
  rw [meet_prop_eq_and] at hpre
  obtain ⟨hR, hs⟩ := hpre
  have := (interp_isRefinedBy_iff_refines S (k a) (k' b)).1 (hk a b hR)
  exact (refines_top_iff.1 this) Qa Ea hs

/-- The interpretation of a function as a state transformer of the memory. -/
@[expose]
def FunctionOp.prog {ctx : WfIRContext OpCode} {op : OperationPtr} (f : FunctionOp ctx.raw op)
    (values : Array RuntimeValue) (h : op.InBounds ctx.raw) (call : Option CallOracle := none) :
    StateT MemoryState Interp (Array RuntimeValue) :=
  fun m => (interpretFunction f values m h call).map fun r => (r.2, r.1)

/-- Refinement of functions is the refinement of their state transformers, for all
    refining arguments, at the concretization of memory refinement (`ms ⊒ mt`, target memory
    first) and the return relation of value refinement. -/
theorem functionOp_isRefinedBy_iff_refines {ctx₁ ctx₂ : WfIRContext OpCode}
    {op₁ op₂ : OperationPtr} (f₁ : FunctionOp ctx₁.raw op₁) (f₂ : FunctionOp ctx₂.raw op₂)
    (h₁ : op₁.InBounds ctx₁.raw) (h₂ : op₂.InBounds ctx₂.raw) (call₁ call₂ : Option CallOracle) :
    FunctionOp.isRefinedBy f₁ f₂ h₁ h₂ call₁ call₂ ↔
      ∀ vs vt : Array RuntimeValue, vs ⊒ vt →
        Refines (⊤ : MemoryState → Prop)
          (Concretization.ofStateRel (fun mt ms : MemoryState => MemoryState.isRefinedBy ms mt))
          (fun _ : EStack⟨⟩ => (⊥ : EStack⟨⟩))
          (FunctionOp.prog f₂ vt h₂ call₂) (FunctionOp.prog f₁ vs h₁ call₁)
          (fun (rt rs : Array RuntimeValue) _ => RuntimeValue.arrayIsRefinedBy rs rt) := by
  have key : ∀ vs vt, Refines (⊤ : MemoryState → Prop)
          (Concretization.ofStateRel (fun mt ms : MemoryState => MemoryState.isRefinedBy ms mt))
          (fun _ : EStack⟨⟩ => (⊥ : EStack⟨⟩))
          (FunctionOp.prog f₂ vt h₂ call₂) (FunctionOp.prog f₁ vs h₁ call₁)
          (fun (rt rs : Array RuntimeValue) _ => RuntimeValue.arrayIsRefinedBy rs rt) ↔
        ∀ ms mt : MemoryState, ms ⊒ mt → Interp.isRefinedBy FunctionResult.isRefinedBy
          (interpretFunction f₁ vs ms h₁ call₁) (interpretFunction f₂ vt mt h₂ call₂) := by
    intro vs vt
    rw [refines_stateT_iff (Rv := fun (rt rs : Array RuntimeValue) => RuntimeValue.arrayIsRefinedBy rs rt)]
    constructor
    · intro h ms mt hm
      have := h mt ms hm
      simp only [FunctionOp.prog] at this
      revert this
      cases interpretFunction f₁ vs ms h₁ call₁ <;> cases interpretFunction f₂ vt mt h₂ call₂ <;>
        simp [Interp.isRefinedBy, FunctionResult.isRefinedBy, and_comm]
    · intro h mt ms hm
      have := h ms mt hm
      simp only [FunctionOp.prog]
      revert this
      cases interpretFunction f₁ vs ms h₁ call₁ <;> cases interpretFunction f₂ vt mt h₂ call₂ <;>
        simp [Interp.isRefinedBy, FunctionResult.isRefinedBy, and_comm]
  constructor
  · intro h vs vt hv
    exact (key vs vt).2 fun ms mt hm => h vs vt ms mt hv hm
  · intro h vs vt ms mt hv hm
    exact (key vs vt).1 (h vs vt hv) ms mt hm

/-- Vertical composition through `RefinementWP.Refines.vcomp_top`: two function refinements
    give a refinement of the state transformers at the composite concretization and the
    composite return relation. -/
theorem functionOp_refines_vcomp {ctx₁ ctx₂ ctx₃ : WfIRContext OpCode}
    {op₁ op₂ op₃ : OperationPtr} {f₁ : FunctionOp ctx₁.raw op₁} {f₂ : FunctionOp ctx₂.raw op₂}
    {f₃ : FunctionOp ctx₃.raw op₃} {h₁ : op₁.InBounds ctx₁.raw} {h₂ : op₂.InBounds ctx₂.raw}
    {h₃ : op₃.InBounds ctx₃.raw} {c₁ c₂ c₃ : Option CallOracle}
    (h₁₂ : FunctionOp.isRefinedBy f₁ f₂ h₁ h₂ c₁ c₂) (h₂₃ : FunctionOp.isRefinedBy f₂ f₃ h₂ h₃ c₂ c₃)
    {vs₁ vs₂ vs₃ : Array RuntimeValue} (hv₁ : vs₁ ⊒ vs₂) (hv₂ : vs₂ ⊒ vs₃) :
    Refines (top : MemoryState → Prop)
      ((Concretization.ofStateRel (fun mt ms : MemoryState => MemoryState.isRefinedBy ms mt)).comp
        (Concretization.ofStateRel (fun mt ms : MemoryState => MemoryState.isRefinedBy ms mt)))
      (fun _ : EStack⟨⟩ => (⊥ : EStack⟨⟩))
      (FunctionOp.prog f₃ vs₃ h₃ c₃) (FunctionOp.prog f₁ vs₁ h₁ c₁)
      ((Concretization.ofStateRel (fun mt ms : MemoryState => MemoryState.isRefinedBy ms mt)).relComp
        (fun (rt rs : Array RuntimeValue) _ => RuntimeValue.arrayIsRefinedBy rs rt)
        (fun (rt rs : Array RuntimeValue) _ => RuntimeValue.arrayIsRefinedBy rs rt)) := by
  have A := (functionOp_isRefinedBy_iff_refines f₁ f₂ h₁ h₂ c₁ c₂).1 h₁₂ vs₁ vs₂ hv₁
  have B := (functionOp_isRefinedBy_iff_refines f₂ f₃ h₂ h₃ c₂ c₃).1 h₂₃ vs₂ vs₃ hv₂
  exact Refines.vcomp_top (eps₁ := fun _ : EStack⟨⟩ => (⊥ : EStack⟨⟩))
    (eps₂ := fun _ : EStack⟨⟩ => (⊥ : EStack⟨⟩)) (Concretization.ofStateRel_supPreserving _) A B

/-- The oracle `c₁` is refined by the oracle `c₂`: at every symbol, refining arguments and
    refining memories give refining results. -/
@[expose]
def CallOracle.isRefinedBy (c₁ c₂ : CallOracle) : Prop :=
  ∀ (s : String) (vs vt : Array RuntimeValue) (ms mt : MemoryState), vs ⊒ vt → ms ⊒ mt →
    Interp.isRefinedBy FunctionResult.isRefinedBy (c₁ s vs ms) (c₂ s vt mt)

/-- The module environment `M₁` is refined by `M₂`: each function of `M₁` is refined by the
    same-named function of `M₂` under all refining oracles, and each external of `M₁` (at a
    symbol that is no function of `M₁`) is refined by the same-named external of `M₂`. -/
structure ModuleEnv.isRefinedBy {ctx₁ ctx₂ : WfIRContext OpCode} (M₁ : ModuleEnv ctx₁)
    (M₂ : ModuleEnv ctx₂) : Prop where
  functions : ∀ (s : String) f₁, M₁.functions[s]? = some f₁ → ∃ f₂, M₂.functions[s]? = some f₂ ∧
    ∀ c₁ c₂ : CallOracle, CallOracle.isRefinedBy c₁ c₂ →
      FunctionOp.isRefinedBy (ModuleEnv.funcOp f₁) (ModuleEnv.funcOp f₂) f₁.2.1 f₂.2.1
        (some c₁) (some c₂)
  externals : ∀ (s : String), M₁.functions[s]? = none → ∀ g₁, M₁.externals s = some g₁ →
    M₂.functions[s]? = none ∧ ∃ g₂, M₂.externals s = some g₂ ∧
      ∀ (vs vt : Array RuntimeValue) (ms mt : MemoryState), vs ⊒ vt → ms ⊒ mt →
        Interp.isRefinedBy FunctionResult.isRefinedBy (g₁ vs ms) (g₂ vt mt)

/-- The oracle of a module is refined by the oracle of a refining module. The proof
    is a fixpoint induction on the `partial_fixpoint` of `interpretSym M₁`; the property holds at
    `ub none` and is therefore admissible. -/
theorem interpretSym_monotone {ctx₁ ctx₂ : WfIRContext OpCode} {M₁ : ModuleEnv ctx₁}
    {M₂ : ModuleEnv ctx₂} (h : M₁.isRefinedBy M₂) :
    CallOracle.isRefinedBy (interpretSym M₁) (interpretSym M₂) := by
  have key : ∀ (s : String) (vs : Array RuntimeValue) (ms : MemoryState)
      (vt : Array RuntimeValue) (mt : MemoryState), vs ⊒ vt → ms ⊒ mt →
      Interp.isRefinedBy FunctionResult.isRefinedBy (interpretSym M₁ s vs ms)
        (interpretSym M₂ s vt mt) := by
    refine interpretSym.fixpoint_induct M₁ (fun F => ∀ (s : String) (vs : Array RuntimeValue)
      (ms : MemoryState) (vt : Array RuntimeValue) (mt : MemoryState), vs ⊒ vt → ms ⊒ mt →
      Interp.isRefinedBy FunctionResult.isRefinedBy (F s vs ms) (interpretSym M₂ s vt mt)) ?_ ?_
    · refine admissible_pi_apply (β := fun _ => Array RuntimeValue → MemoryState →
          Interp (MemoryState × Array RuntimeValue))
        (fun s fs => ∀ (vs : Array RuntimeValue) (ms : MemoryState) (vt : Array RuntimeValue)
          (mt : MemoryState), vs ⊒ vt → ms ⊒ mt →
          Interp.isRefinedBy FunctionResult.isRefinedBy (fs vs ms) (interpretSym M₂ s vt mt))
        fun s => ?_
      refine admissible_pi_apply (β := fun _ => MemoryState →
          Interp (MemoryState × Array RuntimeValue))
        (fun vs fv => ∀ (ms : MemoryState) (vt : Array RuntimeValue)
          (mt : MemoryState), vs ⊒ vt → ms ⊒ mt →
          Interp.isRefinedBy FunctionResult.isRefinedBy (fv ms) (interpretSym M₂ s vt mt))
        fun vs => ?_
      refine admissible_pi_apply (β := fun _ => Interp (MemoryState × Array RuntimeValue))
        (fun ms fm => ∀ (vt : Array RuntimeValue)
          (mt : MemoryState), vs ⊒ vt → ms ⊒ mt →
          Interp.isRefinedBy FunctionResult.isRefinedBy fm (interpretSym M₂ s vt mt))
        fun ms => ?_
      exact Interp.admissible_of_ub _ fun _ _ _ _ => trivial
    · intro F hF s vs ms vt mt hv hm
      dsimp only
      rcases hf₁ : M₁.functions[s]? with _ | f₁
      · rcases hg₁ : M₁.externals s with _ | g₁
        · trivial
        · obtain ⟨hn, g₂, hg₂, hr⟩ := h.externals s hf₁ g₁ hg₁
          rw [interpretSym_eq_external M₂ hn hg₂]
          exact hr vs vt ms mt hv hm
      · obtain ⟨f₂, hf₂, hr⟩ := h.functions s f₁ hf₁
        rw [interpretSym_eq_function M₂ hf₂]
        exact hr F (interpretSym M₂) (fun s vs vt ms mt hv hm => hF s vs ms vt mt hv hm)
          vs vt ms mt hv hm
  intro s vs vt ms mt hv hm
  exact key s vs ms vt mt hv hm

end Veir
