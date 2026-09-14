import RealRooted.Mathlib.Data.Nat.Factorial.Strict
import Mathlib.Tactic

/-!
# Finite reciprocal-factorial tails

The summand `(l - 1) / l!` telescopes. This file records both range and closed
interval forms, together with the strict binomial-factorial ratio obtained
from descending-factorial monotonicity.
-/

open Finset

namespace RealRooted

/-- The elementary reciprocal-factorial telescoping identity. -/
theorem factorialTelescopingTerm (j : ℕ) :
    ((j + 1 : ℕ) : ℝ) / (Nat.factorial (j + 2) : ℝ) =
      1 / (Nat.factorial (j + 1) : ℝ) -
        1 / (Nat.factorial (j + 2) : ℝ) := by
  rw [show j + 2 = (j + 1) + 1 by lia, Nat.factorial_succ]
  push_cast
  field_simp
  ring

/-- Exact value of the first `n` terms of the shifted factorial tail. -/
theorem sum_factorialTelescopingTerm (n : ℕ) :
    ∑ j ∈ Finset.range n,
      ((j + 1 : ℕ) : ℝ) / (Nat.factorial (j + 2) : ℝ) =
        1 - 1 / (Nat.factorial (n + 1) : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih, factorialTelescopingTerm]
      ring

/-- Every finite shifted reciprocal-factorial tail is strictly below one. -/
theorem sum_factorialTelescopingTerm_lt_one (n : ℕ) :
    ∑ j ∈ Finset.range n,
      ((j + 1 : ℕ) : ℝ) / (Nat.factorial (j + 2) : ℝ) < 1 := by
  rw [sum_factorialTelescopingTerm]
  have hpos : 0 < 1 / (Nat.factorial (n + 1) : ℝ) := by positivity
  linarith

private theorem sum_Icc_factorialTail_eq_aux (j : ℕ) :
    ∑ l ∈ Finset.Icc 2 (j + 2),
      ((l : ℝ) - 1) / (Nat.factorial l : ℝ) =
        1 - 1 / (Nat.factorial (j + 2) : ℝ) := by
  induction j with
  | zero => norm_num [Nat.factorial]
  | succ j ih =>
      rw [show j + 1 + 2 = (j + 2) + 1 by lia,
        Finset.sum_Icc_succ_top (by lia), ih]
      have hterm :
          (((j + 3 : ℕ) : ℝ) - 1) / (Nat.factorial (j + 3) : ℝ) =
            1 / (Nat.factorial (j + 2) : ℝ) -
              1 / (Nat.factorial (j + 3) : ℝ) := by
        have hnum : (((j + 3 : ℕ) : ℝ) - 1) = ((j + 2 : ℕ) : ℝ) := by
          push_cast
          ring
        rw [hnum]
        simpa only [show j + 1 + 1 = j + 2 by lia,
          show j + 1 + 2 = j + 3 by lia] using
            factorialTelescopingTerm (j + 1)
      rw [hterm]
      ring

/-- The sum of `(l - 1) / l!` from `l = 2` through `n` telescopes exactly. -/
theorem sum_Icc_factorialTail_eq (n : ℕ) :
    ∑ l ∈ Finset.Icc 2 n,
      ((l : ℝ) - 1) / (Nat.factorial l : ℝ) =
        1 - 1 / (Nat.factorial n : ℝ) := by
  cases n with
  | zero => simp
  | succ n =>
      cases n with
      | zero => norm_num
      | succ j => simpa [Nat.add_assoc] using sum_Icc_factorialTail_eq_aux j

/-- The finite sum of `(l - 1) / l!` from `l = 2` through `n` is below one. -/
theorem sum_Icc_factorialTail_lt_one (n : ℕ) :
    ∑ l ∈ Finset.Icc 2 n,
      ((l : ℝ) - 1) / (Nat.factorial l : ℝ) < 1 := by
  rw [sum_Icc_factorialTail_eq]
  have hpos : 0 < 1 / (Nat.factorial n : ℝ) := by positivity
  linarith

/-- Real ratio form of the strict binomial-factorial product bound. -/
theorem factorialWeight_ratio_lt
    {n m l : ℕ} (hnm : n < m) (hl : 0 < l) (hln : l ≤ n) :
    ((n.choose l : ℕ) : ℝ) * (Nat.factorial (m - l) : ℝ) /
        (Nat.factorial m : ℝ) <
      1 / (Nat.factorial l : ℝ) := by
  have hnat := Nat.factorial_mul_choose_mul_factorial_sub_lt_factorial
    hnm hl hln
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  norm_num only [one_mul]
  have hnat' : n.choose l * (m - l).factorial * l.factorial < m.factorial := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hnat
  exact_mod_cast hnat'

end RealRooted
