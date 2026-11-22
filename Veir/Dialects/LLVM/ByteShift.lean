module

public import Veir.Data.LLVM.Byte
import all Veir.Data.LLVM.Byte.Basic
import all Veir.Data.LLVM.Int.Bitblast

public section

/-!
# Monotonicity of byte shifts

`Byte.lshr` and `Byte.shl` are monotone in refinement of the shifted byte and of the shift
amount, for the monotonicity instances of `llvm.lshr` and `llvm.shl`.
-/

namespace Veir.Data.LLVM.Byte

theorem isRefinedBy_iff_getElem {w : Nat} {x y : Byte w} :
    x ⊒ y ↔ ∀ i (hi : i < w), x.poison[i] = true ∨ (x.val[i] = y.val[i] ∧ y.poison[i] = false) := by
  unfold isRefinedBy
  constructor
  · intro h i hi
    have := congrArg (·[i]) h
    simp only [BitVec.getElem_or, BitVec.getElem_and, BitVec.getElem_xor, BitVec.getElem_not,
      BitVec.getElem_allOnes] at this
    revert this
    cases x.poison[i] <;> cases x.val[i] <;> cases y.val[i] <;> cases y.poison[i] <;> simp
  · intro h
    ext i hi
    simp only [BitVec.getElem_or, BitVec.getElem_and, BitVec.getElem_xor, BitVec.getElem_not,
      BitVec.getElem_allOnes]
    rcases h i hi with h | ⟨h1, h2⟩
    · simp [h]
    · rw [h1, h2]; cases y.val[i] <;> simp

theorem ushiftRight_shiftLeft_eq_iff {w : Nat} (v : BitVec w) (c : Nat) :
    (v >>> c) <<< c = v ↔ ∀ i (hi : i < w), i < c → v[i] = false := by
  constructor
  · intro h i hi hc
    have := congrArg (·[i]) h
    simp only [BitVec.getElem_shiftLeft, hc, decide_true, Bool.not_true, Bool.false_and] at this
    exact this.symm
  · intro h
    ext i hi
    simp only [BitVec.getElem_shiftLeft, BitVec.getLsbD_ushiftRight]
    by_cases hc : i < c
    · simp [hc, h i hi hc]
    · have : c + (i - c) = i := by omega
      simp [hc, this, BitVec.getLsbD_eq_getElem hi]

theorem shiftLeft_ushiftRight_eq_iff {w : Nat} (v : BitVec w) (c : Nat) :
    (v <<< c) >>> c = v ↔ ∀ i (hi : i < w), w ≤ i + c → v[i] = false := by
  constructor
  · intro h i hi hc
    have := congrArg (·[i]) h
    simp only [BitVec.getElem_ushiftRight, BitVec.getLsbD_shiftLeft] at this
    have h1 : ¬ c + i < w := by omega
    simp [h1] at this
    exact this
  · intro h
    ext i hi
    simp only [BitVec.getElem_ushiftRight, BitVec.getLsbD_shiftLeft]
    by_cases hc : w ≤ i + c
    · have h1 : ¬ c + i < w := by omega
      simp [h1, h i hi hc]
    · have h1 : c + i < w := by omega
      have h2 : ¬ c + i < c := by omega
      have h3 : c + i - c = i := by omega
      simp [h1, h2, h3, BitVec.getLsbD_eq_getElem hi]

theorem lshr_bits_mono {w : Nat} {x y : Byte w} (h : x ⊒ y) (c : Nat) :
    ∀ i (hi : i < w), (x.poison >>> c)[i] = true ∨
      ((x.val >>> c)[i] = (y.val >>> c)[i] ∧ (y.poison >>> c)[i] = false) := by
  intro i hi
  simp only [BitVec.getElem_ushiftRight]
  by_cases hc : c + i < w
  · simp only [BitVec.getLsbD_eq_getElem hc]
    exact isRefinedBy_iff_getElem.mp h (c + i) hc
  · simp [BitVec.getLsbD_of_ge _ _ (by omega : w ≤ c + i)]

theorem shl_bits_mono {w : Nat} {x y : Byte w} (h : x ⊒ y) (c : Nat) :
    ∀ i (hi : i < w), (x.poison <<< c)[i] = true ∨
      ((x.val <<< c)[i] = (y.val <<< c)[i] ∧ (y.poison <<< c)[i] = false) := by
  intro i hi
  simp only [BitVec.getElem_shiftLeft]
  by_cases hc : i < c
  · simp [hc]
  · have : i - c < w := by omega
    simp only [hc, decide_false, Bool.not_false, Bool.true_and]
    exact isRefinedBy_iff_getElem.mp h (i - c) this

theorem Int.eq_of_val_isRefinedBy' {w : Nat} {c : BitVec w} {t : Int w}
    (h : Int.val c ⊒ t) : t = .val c := by
  cases t with
  | poison => simp [Int.isRefinedBy_iff, Int.isPoison] at h
  | val c' =>
    simp [Int.isRefinedBy_iff, Int.isPoison, Int.getValue] at h
    rw [h]

/-- The low bits that an exact shift right drops are zero in a refining byte too. -/
theorem lshr_exact_target {w : Nat} {x y : Byte w} (h : x ⊒ y) (c : Nat)
    (hv : (x.val >>> c) <<< c = x.val) (hp : (x.poison >>> c) <<< c = x.poison) :
    (y.val >>> c) <<< c = y.val ∧ (y.poison >>> c) <<< c = y.poison := by
  rw [ushiftRight_shiftLeft_eq_iff] at hv hp ⊢
  rw [ushiftRight_shiftLeft_eq_iff]
  refine ⟨fun i hi hc => ?_, fun i hi hc => ?_⟩
  · rcases isRefinedBy_iff_getElem.mp h i hi with h' | ⟨h1, _⟩
    · rw [hp i hi hc] at h'; cases h'
    · rw [← h1]; exact hv i hi hc
  · rcases isRefinedBy_iff_getElem.mp h i hi with h' | ⟨_, h2⟩
    · rw [hp i hi hc] at h'; cases h'
    · exact h2

/-- The high bits that a `nuw` shift left drops are zero in a refining byte too. -/
theorem shl_nuw_target {w : Nat} {x y : Byte w} (h : x ⊒ y) (c : Nat)
    (hv : (x.val <<< c) >>> c = x.val) (hp : (x.poison <<< c) >>> c = x.poison) :
    (y.val <<< c) >>> c = y.val ∧ (y.poison <<< c) >>> c = y.poison := by
  rw [shiftLeft_ushiftRight_eq_iff] at hv hp ⊢
  rw [shiftLeft_ushiftRight_eq_iff]
  refine ⟨fun i hi hc => ?_, fun i hi hc => ?_⟩
  · rcases isRefinedBy_iff_getElem.mp h i hi with h' | ⟨h1, _⟩
    · rw [hp i hi hc] at h'; cases h'
    · rw [← h1]; exact hv i hi hc
  · rcases isRefinedBy_iff_getElem.mp h i hi with h' | ⟨_, h2⟩
    · rw [hp i hi hc] at h'; cases h'
    · exact h2

theorem lshr_mono {w : Nat} {x y : Byte w} {a b : Int w} (h : x ⊒ y) (hab : a ⊒ b)
    (exact : Bool) : lshr x a exact ⊒ lshr y b exact := by
  cases a with
  | poison => simp only [lshr, Int.isPoison, Bool.true_or, ite_true]; exact allPoison_isRefinedBy _
  | val c =>
    obtain rfl := Int.eq_of_val_isRefinedBy' hab
    unfold lshr
    simp only [Int.isPoison, Int.getValueD, Bool.false_or]
    split
    · exact isRefinedBy_refl _
    · simp only [BitVec.ushiftRight_eq', BitVec.shiftLeft_eq']
      by_cases e : exact = true
      · by_cases c1 : x.val >>> c.toNat <<< c.toNat = x.val
        · by_cases c2 : x.poison >>> c.toNat <<< c.toNat = x.poison
          · obtain ⟨t1, t2⟩ := lshr_exact_target h _ c1 c2
            simp only [e, c1, c2, t1, t2, ne_eq, not_true_eq_false, and_false, ite_false]
            exact isRefinedBy_iff_getElem.mpr (lshr_bits_mono h _)
          · simp only [e, c1, c2, ne_eq, not_true_eq_false, and_false, ite_false, not_false_eq_true,
              and_self, ite_true]
            exact allPoison_isRefinedBy _
        · simp only [e, c1, ne_eq, not_false_eq_true, and_self, ite_true]
          exact allPoison_isRefinedBy _
      · simp only [e, false_and, ite_false]
        exact isRefinedBy_iff_getElem.mpr (lshr_bits_mono h _)

theorem shl_mono {w : Nat} {x y : Byte w} {a b : Int w} (h : x ⊒ y) (hab : a ⊒ b)
    (nuw : Bool) : shl x a nuw ⊒ shl y b nuw := by
  cases a with
  | poison => simp only [shl, Id.run]; exact allPoison_isRefinedBy _
  | val c =>
    obtain rfl := Int.eq_of_val_isRefinedBy' hab
    unfold shl
    simp only [Id.run, pure]
    split
    · exact isRefinedBy_refl _
    · simp only [BitVec.ushiftRight_eq', BitVec.shiftLeft_eq']
      by_cases e : nuw = true
      · by_cases c1 : x.val <<< c.toNat >>> c.toNat = x.val
        · by_cases c2 : x.poison <<< c.toNat >>> c.toNat = x.poison
          · obtain ⟨t1, t2⟩ := shl_nuw_target h _ c1 c2
            simp only [e, c1, c2, t1, t2, ne_eq, not_true_eq_false, and_false, ite_false]
            exact isRefinedBy_iff_getElem.mpr (shl_bits_mono h _)
          · simp only [e, c1, c2, ne_eq, not_true_eq_false, and_false, ite_false, not_false_eq_true,
              and_self, ite_true]
            exact allPoison_isRefinedBy _
        · simp only [e, c1, ne_eq, not_false_eq_true, and_self, ite_true]
          exact allPoison_isRefinedBy _
      · simp only [e, false_and, ite_false]
        exact isRefinedBy_iff_getElem.mpr (shl_bits_mono h _)

end Veir.Data.LLVM.Byte
