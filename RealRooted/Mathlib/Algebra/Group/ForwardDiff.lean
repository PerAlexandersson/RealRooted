import Mathlib.Algebra.Group.ForwardDiff

/-!
# Causal forward differences

This file records the forward-difference convention for sequences indexed by
natural numbers which retains the initial value.
-/

namespace Function

/-- The forward difference with its initial value retained. This is the
causal difference convention for sequences indexed by `ℕ`. -/
def causalFwdDiff {R : Type*} [Sub R] (a : ℕ → R) : ℕ → R
  | 0 => a 0
  | n + 1 => a (n + 1) - a n

/-- Causal forward difference commutes with inserting a finite prefix of
zeroes. -/
theorem causalFwdDiff_prefix {R : Type*} [AddGroup R] (a : ℕ → R) (s : ℕ) :
    causalFwdDiff (fun n => if s ≤ n then a (n - s) else 0) =
      fun n => if s ≤ n then causalFwdDiff a (n - s) else 0 := by
  funext n
  cases n with
  | zero =>
      by_cases hs : s = 0
      · subst s
        simp [causalFwdDiff]
      · have hsn : ¬ s ≤ 0 := by lia
        simp [causalFwdDiff, hsn]
  | succ n =>
      by_cases hsn : s ≤ n + 1
      · by_cases hsn0 : s ≤ n
        · have hshift : n + 1 - s = (n - s) + 1 := by lia
          simp [causalFwdDiff, hsn, hsn0, hshift]
        · have hzero_succ : n + 1 - s = 0 := by lia
          simp [causalFwdDiff, hsn, hsn0, hzero_succ]
      · have hsn0 : ¬ s ≤ n := by lia
        simp [causalFwdDiff, hsn, hsn0]

end Function
