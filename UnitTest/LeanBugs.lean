import Lean

/-!
Regression tests for upstream Lean bugs.
-/

/-! Lean v4.35 generated an ill-typed proof when `cbv` reduced `if True`, which is fixed in
v4.36. The `PuddleCbv.guard_eq_cond` workaround in
Veir/PatternRewriter/Puddle/Validity.lean dates from that bug. -/

#guard_msgs in
example : (if True then 0 else 1 : Nat) = 0 := by
  cbv
