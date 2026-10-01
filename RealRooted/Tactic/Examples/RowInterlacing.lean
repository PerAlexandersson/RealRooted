import RealRooted.Tactic.RowInterlacing

/-!
# Three-term recurrence examples

Regression tests for `rr_row_natDegree`, `rr_row_ne_zero`,
`rr_row_leadingCoeff_pos` and `rr_row_interlaces` on OEIS rows defined by
`P (n + 2) = a n * P (n + 1) + b n * P n`, drawn from `real-rooted-oeis-proofs`.
-/

open Polynomial

namespace RealRooted.Tactic.RowInterlacingExamples

noncomputable section

/-- `b ≤ 0` everywhere, leading coefficients constant (`ρ = 1`) (A056241). -/
def A056241 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1 + X
  | n + 2 => (2 + 2 * X) * A056241 (n + 1) + (-1 + -1 * X + -1 * X ^ 2) * A056241 n

theorem A056241_natDegree (n : ℕ) : (A056241 n).natDegree = n := by rr_row_natDegree
theorem A056241_ne_zero (n : ℕ) : A056241 n ≠ 0 := by rr_row_ne_zero
theorem A056241_leadingCoeff_pos (n : ℕ) : 0 < (A056241 n).leadingCoeff := by
  rr_row_leadingCoeff_pos
theorem A056241_interlaces (n : ℕ) : Interlaces (A056241 n) (A056241 (n + 1)) := by
  rr_row_interlaces

/-- Delannoy rows: `b = X ≤ 0` only on `(-∞, 0]`, rows with nonnegative
coefficients (A008288). -/
def A008288 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1 + X
  | n + 2 => (1 + X) * A008288 (n + 1) + X * A008288 n

theorem A008288_natDegree (n : ℕ) : (A008288 n).natDegree = n := by rr_row_natDegree
theorem A008288_interlaces (n : ℕ) : Interlaces (A008288 n) (A008288 (n + 1)) := by
  rr_row_interlaces

/-- Narayana rows: rational `n`-dependent coefficients (A001263). -/
def A001263 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1 + X
  | n + 2 =>
      (C (1 / (4 + (n : ℝ)) * (5 + 2 * (n : ℝ))) + C (1 / (4 + (n : ℝ)) * (5 + 2 * (n : ℝ))) * X) *
          A001263 (n + 1) +
        (C (1 / (4 + (n : ℝ)) * (-1 + -1 * (n : ℝ))) +
          C (1 / (4 + (n : ℝ)) * (2 + 2 * (n : ℝ))) * X +
          C (1 / (4 + (n : ℝ)) * (-1 + -1 * (n : ℝ))) * X ^ 2) * A001263 n

theorem A001263_natDegree (n : ℕ) : (A001263 n).natDegree = n := by rr_row_natDegree
theorem A001263_interlaces (n : ℕ) : Interlaces (A001263 n) (A001263 (n + 1)) := by
  rr_row_interlaces

/-- Negative denominators `-2 - n` (A008459). -/
def A008459 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1 + X
  | n + 2 =>
      (C (1 / (-2 + -1 * (n : ℝ)) * (-3 + -2 * (n : ℝ))) +
          C (1 / (-2 + -1 * (n : ℝ)) * (-3 + -2 * (n : ℝ))) * X) * A008459 (n + 1) +
        (C (1 / (-2 + -1 * (n : ℝ)) * (1 + (n : ℝ))) +
          C (1 / (-2 + -1 * (n : ℝ)) * (-2 + -2 * (n : ℝ))) * X +
          C (1 / (-2 + -1 * (n : ℝ)) * (1 + (n : ℝ))) * X ^ 2) * A008459 n

theorem A008459_natDegree (n : ℕ) : (A008459 n).natDegree = n := by rr_row_natDegree
theorem A008459_ne_zero (n : ℕ) : A008459 n ≠ 0 := by rr_row_ne_zero

end

end RealRooted.Tactic.RowInterlacingExamples
