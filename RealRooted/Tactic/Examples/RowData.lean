import RealRooted.Tactic.RowData

/-!
# `rr_row_*` examples

Regression tests for OEIS rows defined by derivative recurrences, drawn from
`real-rooted-oeis-proofs`.
-/

open Polynomial

namespace RealRooted.Tactic.RowDataExamples

noncomputable section

/-- Stirling numbers of the second kind (A008277). -/
def A008277 : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => X * (A008277 n).derivative + (1 + X) * A008277 n

theorem A008277_natDegree (n : ℕ) : (A008277 n).natDegree = n := by rr_row_natDegree
theorem A008277_ne_zero (n : ℕ) : A008277 n ≠ 0 := by rr_row_ne_zero
theorem A008277_leadingCoeff_pos (n : ℕ) : 0 < (A008277 n).leadingCoeff := by
  rr_row_leadingCoeff_pos

/-- Rows growing by two degrees, with an `n`-dependent coefficient (A165891). -/
def A165891 : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => (C 1 * X + C (-1) * X ^ 3) * (A165891 n).derivative +
      (C 1 + C 2 * X + C (1 + 2 * (n : ℝ)) * X ^ 2) * A165891 n

theorem A165891_natDegree (n : ℕ) : (A165891 n).natDegree = 2 * n := by rr_row_natDegree
theorem A165891_ne_zero (n : ℕ) : A165891 n ≠ 0 := by rr_row_ne_zero

/-- A second-order derivative recurrence (A160562). -/
def A160562 : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => (4 * X ^ 2) * (A160562 n).derivative.derivative +
      (8 * X) * (A160562 n).derivative + (1 + X) * A160562 n

theorem A160562_natDegree (n : ℕ) : (A160562 n).natDegree = n := by rr_row_natDegree
theorem A160562_ne_zero (n : ℕ) : A160562 n ≠ 0 := by rr_row_ne_zero

/-- Rational `n`-dependent coefficients; the top multiplier is `(n + 3) / (n + 1)`
(A062196). -/
def A062196 : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 =>
      (C (-2 * (1 / (1 + -1 * (2 + (n : ℝ)) ^ 2)) * (2 + (n : ℝ))) * X +
        C (2 * (1 / (1 + -1 * (2 + (n : ℝ)) ^ 2)) * (2 + (n : ℝ))) * X ^ 2) *
          (A062196 n).derivative +
      (C 1 + C (1 / (1 + -1 * (2 + (n : ℝ)) ^ 2) * (3 + -3 * (2 + (n : ℝ)) ^ 2 + 2 * (n : ℝ))) *
        X) * A062196 n

theorem A062196_natDegree (n : ℕ) : (A062196 n).natDegree = n := by rr_row_natDegree
theorem A062196_ne_zero (n : ℕ) : A062196 n ≠ 0 := by rr_row_ne_zero

/-- The top multiplier vanishes in the first step, so the degree is `n - 1`
(A055356). -/
def A055356 : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => (C 1 * X) * (A055356 n).derivative + (C 1 + C (n : ℝ) * X) * A055356 n

theorem A055356_natDegree (n : ℕ) : (A055356 n).natDegree = n - 1 := by rr_row_natDegree
theorem A055356_ne_zero (n : ℕ) : A055356 n ≠ 0 := by rr_row_ne_zero

/-- Product sequences are dispatched to `rr_product_natDegree`. -/
def binomialRows : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => (1 + X) * binomialRows n

theorem binomialRows_natDegree (n : ℕ) : (binomialRows n).natDegree = n := by
  rr_row_natDegree
theorem binomialRows_ne_zero (n : ℕ) : binomialRows n ≠ 0 := by rr_row_ne_zero

/-- Half growth: the Fibonacci polynomials of A011973 have degree `n / 2`. -/
def A011973 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1
  | n + 2 => (1) * A011973 (n + 1) + (X) * A011973 n

theorem A011973_natDegree (n : ℕ) : (A011973 n).natDegree = n / 2 := by rr_row_natDegree
theorem A011973_ne_zero (n : ℕ) : A011973 n ≠ 0 := by rr_row_ne_zero
theorem A011973_leadingCoeff_pos (n : ℕ) : 0 < (A011973 n).leadingCoeff := by
  rr_row_leadingCoeff_pos

/-- Half growth with `n`-dependent coefficients and degree `(n + 1) / 2` (A119808). -/
def A119808 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1 + X
  | n + 2 => C ((n : ℝ) + 2) * A119808 (n + 1) + (C 1 * X) * A119808 n

theorem A119808_natDegree (n : ℕ) : (A119808 n).natDegree = (n + 1) / 2 := by
  rr_row_natDegree

/-- A zero first row is split off; `h` excludes it (A128966). -/
def A128966 : ℕ → ℝ[X]
  | 0 => 0
  | 1 => 1 + X
  | n + 2 => (1 + X) * A128966 (n + 1) + X * A128966 n

theorem A128966_natDegree (n : ℕ) : (A128966 n).natDegree = n := by rr_row_natDegree
theorem A128966_ne_zero (n : ℕ) (h : n ≠ 0) : A128966 n ≠ 0 := by rr_row_ne_zero

end

end RealRooted.Tactic.RowDataExamples
