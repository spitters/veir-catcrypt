module

public import Veir.Interpreter.Lemmas
public import Veir.Interpreter.LoadStore
public import Veir.Dialects.LLVM.ByteShift
import all Veir.Interpreter.Refinement.Basic
import all Veir.Data.LLVM.Int.Basic
import all Veir.Data.LLVM.Int.Bitblast
import all Veir.Data.LLVM.Byte.Basic
import all Veir.Data.LLVM.Ptr.Basic
import all Veir.Interpreter.Memory
import all Veir.Dialects.LLVM.OpInfo
import all Veir.Data.Pointer.Basic
import all Veir.Interfaces.DataLayoutInterfaces
import all Veir.DataLayout.RISCV64
import all Veir.IR.Attribute

public section

/-!
# Monotonicity of more LLVM opcodes

`InterpretOp'Monotone` instances, which take precedence over the assumption
`interpretOp'_monotone_assumed` in `Veir.Dialects.Monotonicity`.
-/

set_option linter.unusedVariables false

namespace Veir

theorem RuntimeValue.pair_isRefinedBy_iff {a b : RuntimeValue} {t : Array RuntimeValue} :
    #[a, b] ⊒ t ↔ ∃ c d, t = #[c, d] ∧ a ⊒ c ∧ b ⊒ d := by
  constructor
  · intro h
    rcases t with ⟨l⟩
    rcases l with _ | ⟨c, _ | ⟨d, _ | ⟨e, l⟩⟩⟩
    · exact absurd h.1 (by simp)
    · exact absurd h.1 (by simp)
    · exact ⟨c, d, rfl, by simpa using h.2 0 (by simp), by simpa using h.2 1 (by simp)⟩
    · exact absurd h.1 (by simp)
  · rintro ⟨c, d, rfl, hc, hd⟩
    simp [RuntimeValue.arrayIsRefinedBy_cons, hc, hd]

theorem RuntimeValue.int_isRefinedBy_int {bw : Nat} {x y : Data.LLVM.Int bw} (h : x ⊒ y) :
    RuntimeValue.int bw x ⊒ RuntimeValue.int bw y := ⟨rfl, by simpa using h⟩

theorem OperationResult.single_int {bw : Nat} {x y : Data.LLVM.Int bw} (h : x ⊒ y)
    (mem : MemoryState) :
    Interp.isRefinedBy OperationResult.isRefinedBy
      (Interp.ok (#[RuntimeValue.int bw x], mem, none))
      (Interp.ok (#[RuntimeValue.int bw y], mem, none)) := by
  simp only [Interp.isRefinedBy, OperationResult.isRefinedBy,
    RuntimeValue.arrayIsRefinedBy_singleton]
  exact ⟨RuntimeValue.int_isRefinedBy_int h, trivial, trivial⟩

/-- `llvm.call` is not interpreted by `interpretOp'` (calls run through the oracle of
    `interpretOpWith`), so it fails and is trivially monotone. -/
instance : InterpretOp'Monotone (.llvm .call) where
  monotone props resultTypes operands operands' blockOperands mem h := by
    simp [interpretOp', Llvm.interpretOp', Interp.isRefinedBy]

instance : InterpretOp'Monotone (.llvm .mlir__constant) where
  monotone props resultTypes operands operands' blockOperands mem h :=
    Interp.isRefinedBy_refl_operationResult _

instance : InterpretOp'Monotone (.llvm .mlir__addressof) where
  monotone props resultTypes operands operands' blockOperands mem h :=
    Interp.isRefinedBy_refl_operationResult _

instance : InterpretOp'Monotone (.llvm .add) where
  monotone props resultTypes operands operands' blockOperands mem h := by
    simp only [interpretOp', Llvm.interpretOp']
    split
    · next bw lhs bw' rhs hOps =>
      obtain rfl : operands = #[.int bw lhs, .int bw' rhs] := List.eq_toArray_iff.mpr hOps
      obtain ⟨a, b, rfl, ha, hb⟩ := RuntimeValue.pair_isRefinedBy_iff.mp h
      obtain ⟨lhs', rfl, hl⟩ := RuntimeValue.int_of_isRefinedBy ha
      obtain ⟨rhs', rfl, hr⟩ := RuntimeValue.int_of_isRefinedBy hb
      by_cases hbw : bw' ≠ bw
      · simp [hbw, Interp.isRefinedBy]
      · obtain rfl : bw' = bw := by simpa using hbw
        simp only [ne_eq, not_true_eq_false, dite_false, Interp.pure_eq]
        exact OperationResult.single_int
          (Data.LLVM.Int.add_mono _ _ _ _ hl (by simpa using hr) _ _) mem
    · simp [Interp.isRefinedBy]

instance : InterpretOp'Monotone (.llvm .and) where
  monotone props resultTypes operands operands' blockOperands mem h := by
    simp only [interpretOp', Llvm.interpretOp']
    split
    · next bw lhs bw' rhs hOps =>
      obtain rfl : operands = #[.int bw lhs, .int bw' rhs] := List.eq_toArray_iff.mpr hOps
      obtain ⟨a, b, rfl, ha, hb⟩ := RuntimeValue.pair_isRefinedBy_iff.mp h
      obtain ⟨lhs', rfl, hl⟩ := RuntimeValue.int_of_isRefinedBy ha
      obtain ⟨rhs', rfl, hr⟩ := RuntimeValue.int_of_isRefinedBy hb
      by_cases hbw : bw' ≠ bw
      · simp [hbw, Interp.isRefinedBy]
      · obtain rfl : bw' = bw := by simpa using hbw
        simp only [ne_eq, not_true_eq_false, dite_false, Interp.pure_eq]
        exact OperationResult.single_int
          (Data.LLVM.Int.and_mono _ _ _ _  hl (by simpa using hr) ) mem
    · simp [Interp.isRefinedBy]

instance : InterpretOp'Monotone (.llvm .or) where
  monotone props resultTypes operands operands' blockOperands mem h := by
    simp only [interpretOp', Llvm.interpretOp']
    split
    · next bw lhs bw' rhs hOps =>
      obtain rfl : operands = #[.int bw lhs, .int bw' rhs] := List.eq_toArray_iff.mpr hOps
      obtain ⟨a, b, rfl, ha, hb⟩ := RuntimeValue.pair_isRefinedBy_iff.mp h
      obtain ⟨lhs', rfl, hl⟩ := RuntimeValue.int_of_isRefinedBy ha
      obtain ⟨rhs', rfl, hr⟩ := RuntimeValue.int_of_isRefinedBy hb
      by_cases hbw : bw' ≠ bw
      · simp [hbw, Interp.isRefinedBy]
      · obtain rfl : bw' = bw := by simpa using hbw
        simp only [ne_eq, not_true_eq_false, dite_false, Interp.pure_eq]
        exact OperationResult.single_int
          (Data.LLVM.Int.or_mono _ _ _ _ _ hl (by simpa using hr) ) mem
    · simp [Interp.isRefinedBy]

instance : InterpretOp'Monotone (.llvm .icmp) where
  monotone props resultTypes operands operands' blockOperands mem h := by
    simp only [interpretOp', Llvm.interpretOp']
    split
    · next bw lhs bw' rhs hOps =>
      obtain rfl : operands = #[.int bw lhs, .int bw' rhs] := List.eq_toArray_iff.mpr hOps
      obtain ⟨a, b, rfl, ha, hb⟩ := RuntimeValue.pair_isRefinedBy_iff.mp h
      obtain ⟨lhs', rfl, hl⟩ := RuntimeValue.int_of_isRefinedBy ha
      obtain ⟨rhs', rfl, hr⟩ := RuntimeValue.int_of_isRefinedBy hb
      by_cases hbw : bw' ≠ bw
      · simp [hbw, Interp.isRefinedBy]
      · obtain rfl : bw' = bw := by simpa using hbw
        simp only [ne_eq, not_true_eq_false, dite_false, Interp.pure_eq]
        exact OperationResult.single_int
          (Data.LLVM.Int.icmp_mono _ _ _ _ _ hl (by simpa using hr) ) mem
    · simp [Interp.isRefinedBy]

instance : InterpretOp'Monotone (.llvm .zext) where
  monotone props resultTypes operands operands' blockOperands mem h := by
    simp only [interpretOp', Llvm.interpretOp']
    split
    · next w v hOps =>
      obtain rfl : operands = #[.int w v] := List.eq_toArray_iff.mpr hOps
      obtain ⟨a, rfl, ha⟩ := RuntimeValue.singleton_isRefinedBy_iff.mp h
      obtain ⟨v', rfl, hv⟩ := RuntimeValue.int_of_isRefinedBy ha
      cases hrt : resultTypes[0]? with
      | none => simp [hrt, Interp.isRefinedBy]
      | some rt =>
        simp only [hrt]
        generalize rt.val = a
        cases a <;> try (simp [Interp.isRefinedBy]; done)
        rename_i resBw
        by_cases hle : resBw.bitwidth ≤ w
        · simp [hle, Interp.isRefinedBy]
        · simp only [hle, dite_false]
          exact OperationResult.single_int (Data.LLVM.Int.zext_mono _ _ _ hv) mem
    · simp [Interp.isRefinedBy]

theorem Data.LLVM.Int.eq_of_val_isRefinedBy {w : Nat} {c : BitVec w} {t : Data.LLVM.Int w}
    (h : Data.LLVM.Int.val c ⊒ t) : t = .val c := by
  cases t with
  | poison => simp [Data.LLVM.Int.isRefinedBy_iff, Data.LLVM.Int.isPoison] at h
  | val c' =>
    simp [Data.LLVM.Int.isRefinedBy_iff, Data.LLVM.Int.isPoison, Data.LLVM.Int.getValue] at h
    rw [h]

instance : InterpretOp'Monotone (.llvm .br) where
  monotone props resultTypes operands operands' blockOperands mem h := by
    simp only [interpretOp', Llvm.interpretOp']
    split
    · simp [Interp.isRefinedBy, OperationResult.isRefinedBy,
        ControlFlowAction.optionIsRefinedBy, ControlFlowAction.isRefinedBy, h]
    · simp [Interp.isRefinedBy]

instance : InterpretOp'Monotone (.llvm .alloca) where
  monotone props resultTypes operands operands' blockOperands mem h := by
    simp only [interpretOp', Llvm.interpretOp']
    split
    · next w count hOps =>
      obtain rfl : operands = #[.int w (.val count)] := List.eq_toArray_iff.mpr hOps
      obtain ⟨a, rfl, ha⟩ := RuntimeValue.singleton_isRefinedBy_iff.mp h
      obtain ⟨t, rfl, ht⟩ := RuntimeValue.int_of_isRefinedBy ha
      obtain rfl := Data.LLVM.Int.eq_of_val_isRefinedBy ht
      exact Interp.isRefinedBy_refl_operationResult _
    · simp [Interp.isRefinedBy]

instance : InterpretOp'Monotone (.llvm .ptrtoint) where
  monotone props resultTypes operands operands' blockOperands mem h := by
    simp only [interpretOp', Llvm.interpretOp']
    split
    · next v hOps =>
      obtain rfl : operands = #[.addr v] := List.eq_toArray_iff.mpr hOps
      obtain ⟨a, rfl, ha⟩ := RuntimeValue.singleton_isRefinedBy_iff.mp h
      cases a with
      | addr v' =>
        have hv : v ⊒ v' := ha
        simp only [List.toList_toArray]
        cases hrt : resultTypes.toList with
        | nil => simp [Interp.isRefinedBy]
        | cons rt rest =>
          cases rest with
          | cons _ _ => simp [Interp.isRefinedBy]
          | nil =>
            simp only
            generalize rt.val = a
            cases a <;> try (simp [Interp.isRefinedBy]; done)
            rename_i bw
            by_cases hb : bw.bitwidth = 64
            · simp only [hb, ite_true, Interp.pure_eq]
              refine OperationResult.single_int ?_ mem
              cases v with
              | poison => simp [Data.LLVM.Ptr.toInt, Data.LLVM.Int.isRefinedBy_iff, Data.LLVM.Int.isPoison]
              | val p =>
                cases v' with
                | poison => exact hv.elim
                | val p' =>
                  have : p = p' := hv
                  subst this
                  simp [Data.LLVM.Int.isRefinedBy_iff]
            · simp [hb, Interp.isRefinedBy]
      | _ => exact ha.elim
    · simp [Interp.isRefinedBy]

theorem RuntimeValue.arrayIsRefinedBy_extract {a b : Array RuntimeValue} (h : a ⊒ b)
    (i j : Nat) : a.extract i j ⊒ b.extract i j := by
  obtain ⟨hs, hp⟩ := h
  refine ⟨by simp [hs], fun k hk => ?_⟩
  simp only [Array.size_extract] at hk
  have h1 : i + k < a.size := by omega
  have h2 : i + k < b.size := by omega
  rw [getElem!_pos (a.extract i j) k (by simp; omega), getElem!_pos (b.extract i j) k (by simp; omega)]
  simp only [Array.getElem_extract]
  have := hp (i + k) h1
  rwa [getElem!_pos a (i + k) h1, getElem!_pos b (i + k) h2] at this

instance : InterpretOp'Monotone (.llvm .cond_br) where
  monotone props resultTypes operands operands' blockOperands mem h := by
    simp only [interpretOp', Llvm.interpretOp']
    split
    · rename_i destTrue destFalse _
      have hsz := h.1
      cases h0 : operands[0]? with
      | none => simp [Interp.isRefinedBy]
      | some c =>
        have h0' : operands'[0]? = some operands'[0]! := by
          have : 0 < operands.size := by
            rcases Array.getElem?_eq_some_iff.mp h0 with ⟨hlt, _⟩; exact hlt
          rw [getElem!_pos operands' 0 (by omega)]; simp
        have hc : c ⊒ operands'[0]! := by
          have : 0 < operands.size := by
            rcases Array.getElem?_eq_some_iff.mp h0 with ⟨hlt, _⟩; exact hlt
          have := h.2 0 this
          rwa [getElem!_pos operands 0 (by omega), (Array.getElem?_eq_some_iff.mp h0).2] at this
        simp only [h0', Interp.bind_ok]
        cases hts : props.operandSegmentSizes.values[1]? with
        | none => simp [Interp.isRefinedBy]
        | some ts =>
          simp only
          split
          · rename_i cond
            obtain ⟨t, ht, hct⟩ := RuntimeValue.int_of_isRefinedBy hc
            obtain rfl := Data.LLVM.Int.eq_of_val_isRefinedBy hct
            rw [ht]
            simp only
            split
            · simp [Interp.isRefinedBy, OperationResult.isRefinedBy,
                ControlFlowAction.optionIsRefinedBy, ControlFlowAction.isRefinedBy,
                RuntimeValue.arrayIsRefinedBy_extract h]
            · simp [Interp.isRefinedBy, OperationResult.isRefinedBy,
                ControlFlowAction.optionIsRefinedBy, ControlFlowAction.isRefinedBy,
                RuntimeValue.arrayIsRefinedBy_extract h, hsz]
          · simp [Interp.isRefinedBy]
          · simp [Interp.isRefinedBy]
    · simp [Interp.isRefinedBy]

theorem MemoryState.ptrFromInt_isRefinedBy (mem : MemoryState) {x y : Data.LLVM.Int 64}
    (h : x ⊒ y) : mem.ptrFromInt x ⊒ mem.ptrFromInt y := by
  cases x with
  | poison => simp only [MemoryState.ptrFromInt, Data.LLVM.Ptr.isRefinedBy]
  | val c =>
    obtain rfl := Data.LLVM.Int.eq_of_val_isRefinedBy h
    show mem.ptrFromInt (.val c) ⊒ mem.ptrFromInt (.val c)
    exact Data.LLVM.Ptr.isRefinedBy_refl _

instance : InterpretOp'Monotone (.llvm .inttoptr) where
  monotone props resultTypes operands operands' blockOperands mem h := by
    simp only [interpretOp', Llvm.interpretOp']
    split
    · next bw v hOps =>
      obtain rfl : operands = #[.int bw v] := List.eq_toArray_iff.mpr hOps
      obtain ⟨a, rfl, ha⟩ := RuntimeValue.singleton_isRefinedBy_iff.mp h
      obtain ⟨v', rfl, hv⟩ := RuntimeValue.int_of_isRefinedBy ha
      simp only [List.toList_toArray]
      cases hrt : resultTypes.toList with
      | nil => simp [Interp.isRefinedBy]
      | cons rt rest =>
        cases rest with
        | cons _ _ => simp [Interp.isRefinedBy]
        | nil =>
          simp only
          generalize rt.val = a
          cases a <;> try (simp [Interp.isRefinedBy]; done)
          by_cases hb : bw = 64
          · subst hb
            simp only [dite_true, Interp.pure_eq, Interp.isRefinedBy, OperationResult.isRefinedBy,
              RuntimeValue.arrayIsRefinedBy_singleton]
            exact ⟨MemoryState.ptrFromInt_isRefinedBy mem (by simpa using hv), trivial, trivial⟩
          · simp [hb, Interp.isRefinedBy]
    · simp [Interp.isRefinedBy]

theorem Data.LLVM.Byte.trunc_mono {w : Nat} {x y : Data.LLVM.Byte w} (w' : Nat) (hw : w' ≤ w)
    (h : x ⊒ y) : x.trunc w' ⊒ y.trunc w' := by
  simp only [Data.LLVM.Byte.isRefinedBy, Data.LLVM.Byte.trunc] at h ⊢
  have := congrArg (BitVec.setWidth w') h
  simp only [BitVec.setWidth_or, BitVec.setWidth_and, BitVec.setWidth_xor,
    BitVec.setWidth_not hw] at this
  rw [this]
  ext i hi
  simp [hi]
  omega

theorem OperationResult.single_byte {bw : Nat} {x y : Data.LLVM.Byte bw} (h : x ⊒ y)
    (mem : MemoryState) :
    Interp.isRefinedBy OperationResult.isRefinedBy
      (Interp.ok (#[RuntimeValue.byte bw x], mem, none))
      (Interp.ok (#[RuntimeValue.byte bw y], mem, none)) := by
  simp only [Interp.isRefinedBy, OperationResult.isRefinedBy,
    RuntimeValue.arrayIsRefinedBy_singleton]
  exact ⟨⟨rfl, by simpa using h⟩, trivial, trivial⟩

instance : InterpretOp'Monotone (.llvm .trunc) where
  monotone props resultTypes operands operands' blockOperands mem h := by
    simp only [interpretOp', Llvm.interpretOp']
    split
    · next v hOps =>
      obtain rfl : operands = #[v] := List.eq_toArray_iff.mpr hOps
      obtain ⟨a, rfl, ha⟩ := RuntimeValue.singleton_isRefinedBy_iff.mp h
      simp only [List.toList_toArray]
      cases hrt : resultTypes[0]? with
      | none => simp [Interp.isRefinedBy]
      | some rt =>
        simp only
        cases v with
        | int w x =>
          obtain ⟨y, rfl, hxy⟩ := RuntimeValue.int_of_isRefinedBy ha
          simp only
          generalize rt.val = t
          cases t <;> try (simp [Interp.isRefinedBy]; done)
          rename_i resBw
          by_cases hle : resBw.bitwidth ≥ w
          · simp [hle, Interp.isRefinedBy]
          · simp only [hle, dite_false, Interp.pure_eq]
            exact OperationResult.single_int (Data.LLVM.Int.trunc_mono _ _ _ hxy) mem
        | byte w x =>
          obtain ⟨y, rfl, hxy⟩ := RuntimeValue.byte_of_isRefinedBy ha
          simp only
          generalize rt.val = t
          cases t <;> try (simp [Interp.isRefinedBy]; done)
          rename_i resBw
          by_cases hle : resBw.bitwidth ≥ w
          · simp [hle, Interp.isRefinedBy]
          · simp only [hle, dite_false, Interp.pure_eq]
            exact OperationResult.single_byte (Data.LLVM.Byte.trunc_mono _ (by omega) hxy) mem
        | _ => simp [Interp.isRefinedBy]
    · simp [Interp.isRefinedBy]

instance : InterpretOp'Monotone (.llvm .shl) where
  monotone props resultTypes operands operands' blockOperands mem h := by
    simp only [interpretOp', Llvm.interpretOp']
    split
    · next lhs bw' rhs hOps =>
      obtain rfl : operands = #[lhs, .int bw' rhs] := List.eq_toArray_iff.mpr hOps
      obtain ⟨a, b, rfl, ha, hb⟩ := RuntimeValue.pair_isRefinedBy_iff.mp h
      obtain ⟨rhs', rfl, hr⟩ := RuntimeValue.int_of_isRefinedBy hb
      simp only [List.toList_toArray]
      cases lhs with
      | int bw x =>
        obtain ⟨y, rfl, hxy⟩ := RuntimeValue.int_of_isRefinedBy ha
        simp only
        by_cases hbw : bw' ≠ bw
        · simp [hbw, Interp.isRefinedBy]
        · obtain rfl : bw' = bw := by simpa using hbw
          simp only [ne_eq, not_true_eq_false, dite_false, Interp.pure_eq]
          exact OperationResult.single_int
            (Data.LLVM.Int.shl_mono _ _ _ _ hxy (by simpa using hr) _ _) mem
      | byte bw x =>
        obtain ⟨y, rfl, hxy⟩ := RuntimeValue.byte_of_isRefinedBy ha
        simp only
        by_cases hbw : bw' ≠ bw
        · simp [hbw, Interp.isRefinedBy]
        · obtain rfl : bw' = bw := by simpa using hbw
          simp only [ne_eq, not_true_eq_false, dite_false, Interp.pure_eq]
          by_cases hnsw : props.nsw = true
          · simp [hnsw, Interp.isRefinedBy]
          simp only [hnsw, Bool.false_eq_true, ite_false]
          exact OperationResult.single_byte
            (Data.LLVM.Byte.shl_mono hxy (by simpa using hr) _) mem
      | _ => simp [Interp.isRefinedBy]
    · simp [Interp.isRefinedBy]

instance : InterpretOp'Monotone (.llvm .lshr) where
  monotone props resultTypes operands operands' blockOperands mem h := by
    simp only [interpretOp', Llvm.interpretOp']
    split
    · next lhs bw' rhs hOps =>
      obtain rfl : operands = #[lhs, .int bw' rhs] := List.eq_toArray_iff.mpr hOps
      obtain ⟨a, b, rfl, ha, hb⟩ := RuntimeValue.pair_isRefinedBy_iff.mp h
      obtain ⟨rhs', rfl, hr⟩ := RuntimeValue.int_of_isRefinedBy hb
      simp only [List.toList_toArray]
      cases lhs with
      | int bw x =>
        obtain ⟨y, rfl, hxy⟩ := RuntimeValue.int_of_isRefinedBy ha
        simp only
        by_cases hbw : bw' ≠ bw
        · simp [hbw, Interp.isRefinedBy]
        · obtain rfl : bw' = bw := by simpa using hbw
          simp only [ne_eq, not_true_eq_false, dite_false, Interp.pure_eq]
          exact OperationResult.single_int
            (Data.LLVM.Int.lshr_mono _ _ _ _ hxy (by simpa using hr) _) mem
      | byte bw x =>
        obtain ⟨y, rfl, hxy⟩ := RuntimeValue.byte_of_isRefinedBy ha
        simp only
        by_cases hbw : bw' ≠ bw
        · simp [hbw, Interp.isRefinedBy]
        · obtain rfl : bw' = bw := by simpa using hbw
          simp only [ne_eq, not_true_eq_false, dite_false, Interp.pure_eq]

          exact OperationResult.single_byte
            (Data.LLVM.Byte.lshr_mono hxy (by simpa using hr) _) mem
      | _ => simp [Interp.isRefinedBy]
    · simp [Interp.isRefinedBy]


/-- Refinement of loop steps: the same constructor, related states. -/
@[expose]
def ForInStep.rel {β β' : Type} (R : β → β' → Prop) : ForInStep β → ForInStep β' → Prop
  | .done x, .done y => R x y
  | .yield x, .yield y => R x y
  | _, _ => False

theorem Interp.isRefinedBy_bind_rel {α β α' β' : Type} {R : α → β → Prop} {S : α' → β' → Prop}
    {s : Interp α} {t : Interp β} {k : α → Interp α'} {k' : β → Interp β'}
    (h : Interp.isRefinedBy R s t) (hk : ∀ a b, R a b → Interp.isRefinedBy S (k a) (k' b)) :
    Interp.isRefinedBy S (s >>= k) (t >>= k') := by
  cases s <;> cases t <;> first | trivial | exact h.elim | exact hk _ _ h

/-- A loop over a list is refined by a loop whose steps refine its steps. -/
theorem Interp.forIn_rel {β β' : Type} (R : β → β' → Prop) (l : List Nat)
    (f : Nat → β → Interp (ForInStep β)) (g : Nat → β' → Interp (ForInStep β'))
    (hstep : ∀ a x y, R x y → Interp.isRefinedBy (ForInStep.rel R) (f a x) (g a y)) :
    ∀ b b', R b b' → Interp.isRefinedBy R (forIn l b f) (forIn l b' g) := by
  induction l with
  | nil => intro b b' hb; exact hb
  | cons a l ih =>
    intro b b' hb
    simp only [List.forIn_cons]
    refine Interp.isRefinedBy_bind_rel (hstep a b b' hb) fun x y hxy => ?_
    cases x <;> cases y <;> simp only [ForInStep.rel] at hxy <;> first
      | exact hxy
      | exact ih _ _ hxy

instance : InterpretOp'Monotone (.llvm .switch) where
  monotone props resultTypes operands operands' blockOperands mem h := by
    simp only [interpretOp', Llvm.interpretOp']
    cases hd : blockOperands[0]? with
    | none => simp [Interp.isRefinedBy]
    | some destDefault =>
      simp only
      cases h0 : operands[0]? with
      | none => simp [Interp.isRefinedBy]
      | some c =>
        have hlt : 0 < operands.size := by
          rcases Array.getElem?_eq_some_iff.mp h0 with ⟨hlt, _⟩; exact hlt
        have h0' : operands'[0]? = some operands'[0]! := by
          rw [getElem!_pos operands' 0 (by have := h.1; omega)]; simp
        have hc : c ⊒ operands'[0]! := by
          have := h.2 0 hlt
          rwa [getElem!_pos operands 0 hlt, (Array.getElem?_eq_some_iff.mp h0).2] at this
        simp only [h0']
        cases hds : props.operandSegmentSizes.values[1]? with
        | none => simp [Interp.isRefinedBy]
        | some ds =>
          simp only
          cases hcv : LLVMSwitchProperties.caseValues? props with
          | none => simp [Interp.isRefinedBy]
          | some cvs =>
            simp only
            split
            · simp [Interp.isRefinedBy]
            · cases c with
              | int bw x =>
                obtain ⟨t, ht, hxt⟩ := RuntimeValue.int_of_isRefinedBy hc
                rw [ht]
                cases x with
                | poison => simp [Interp.isRefinedBy]
                | val v =>
                  obtain rfl := Data.LLVM.Int.eq_of_val_isRefinedBy hxt
                  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
                  refine Interp.isRefinedBy_bind_rel (R := fun x y => x.2 = y.2 ∧
                    (match x.1, y.1 with
                      | none, none => True
                      | some r, some r' => OperationResult.isRefinedBy r r'
                      | _, _ => False))
                    (Interp.forIn_rel _ _ _ _ ?_ _ _ ⟨rfl, trivial⟩) ?_
                  · intro i x y ⟨hxy2, hxy1⟩
                    rw [hxy2]
                    split
                    · split
                      · split
                        · simp [Interp.isRefinedBy, ForInStep.rel,
                            OperationResult.isRefinedBy, ControlFlowAction.optionIsRefinedBy,
                            ControlFlowAction.isRefinedBy, RuntimeValue.arrayIsRefinedBy_extract h]
                        · simp [Interp.isRefinedBy]
                      · simp [Interp.isRefinedBy, ForInStep.rel]
                    · simp [Interp.isRefinedBy]
                  · rintro ⟨o, base⟩ ⟨o', base'⟩ ⟨hb, ho⟩
                    simp only at hb ho
                    cases o <;> cases o' <;> simp only at ho
                    · simp [Interp.isRefinedBy, OperationResult.isRefinedBy,
                        ControlFlowAction.optionIsRefinedBy, ControlFlowAction.isRefinedBy,
                        RuntimeValue.arrayIsRefinedBy_extract h, hb]
                    · exact ho
              | _ => simp [Interp.isRefinedBy]


/-- The opcodes with an `InterpretOp'Monotone` instance proved here (collected so that
    `#print axioms` checks that none of them uses `interpretOp'_monotone_assumed`). -/
theorem interpretOp'Monotone_proved :
    InterpretOp'Monotone (.llvm .call) ∧
    InterpretOp'Monotone (.llvm .mlir__constant) ∧
    InterpretOp'Monotone (.llvm .mlir__addressof) ∧
    InterpretOp'Monotone (.llvm .add) ∧
    InterpretOp'Monotone (.llvm .and) ∧
    InterpretOp'Monotone (.llvm .or) ∧
    InterpretOp'Monotone (.llvm .icmp) ∧
    InterpretOp'Monotone (.llvm .zext) ∧
    InterpretOp'Monotone (.llvm .br) ∧
    InterpretOp'Monotone (.llvm .alloca) ∧
    InterpretOp'Monotone (.llvm .ptrtoint) ∧
    InterpretOp'Monotone (.llvm .cond_br) ∧
    InterpretOp'Monotone (.llvm .inttoptr) ∧
    InterpretOp'Monotone (.llvm .trunc) ∧
    InterpretOp'Monotone (.llvm .shl) ∧
    InterpretOp'Monotone (.llvm .lshr) ∧
    InterpretOp'Monotone (.llvm .switch) :=
  ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance⟩

end Veir

end
