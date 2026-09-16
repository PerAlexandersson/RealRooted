import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic.Ring

/-!
# Strict inequalities for descending factorials

This file adds strict forms of monotonicity for descending factorials and the
factorial product inequality used to compare binomial-factorial weights.
-/

namespace Nat

/-- A positive-length descending factorial is strictly increasing in its
upper argument as long as the length fits in the smaller argument. -/
theorem descFactorial_lt_descFactorial_of_lt_of_pos
    {a b l : ℕ} (hab : a < b) (hl : 0 < l) (hla : l ≤ a) :
    a.descFactorial l < b.descFactorial l := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by lia : l ≠ 0)
  rw [descFactorial_succ, descFactorial_succ]
  have hjle : j ≤ a := by lia
  have hsub : a - j < b - j := Nat.sub_lt_sub_right hjle hab
  calc
    (a - j) * a.descFactorial j <
        (b - j) * a.descFactorial j :=
      Nat.mul_lt_mul_of_pos_right hsub (descFactorial_pos.mpr hjle)
    _ ≤ (b - j) * b.descFactorial j :=
      Nat.mul_le_mul_left _ (descFactorial_le j hab.le)

/-- Comparing descending factorials gives a strict binomial-factorial product
bound without using natural-number division. -/
theorem factorial_mul_choose_mul_factorial_sub_lt_factorial
    {n m l : ℕ} (hnm : n < m) (hl : 0 < l) (hln : l ≤ n) :
    l.factorial * n.choose l * (m - l).factorial < m.factorial := by
  have hlm : l ≤ m := hln.trans hnm.le
  have hdesc := descFactorial_lt_descFactorial_of_lt_of_pos hnm hl hln
  calc
    l.factorial * n.choose l * (m - l).factorial =
        (m - l).factorial * n.descFactorial l := by
      rw [descFactorial_eq_factorial_mul_choose]
      ring
    _ < (m - l).factorial * m.descFactorial l :=
      Nat.mul_lt_mul_of_pos_left hdesc (factorial_pos _)
    _ = m.factorial := factorial_mul_descFactorial hlm

end Nat
