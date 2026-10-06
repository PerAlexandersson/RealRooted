import RealRooted.Tactic.Recurrence

/-!
# `rr_row_*` examples

Regression tests for OEIS rows defined by derivative recurrences, drawn from
`real-rooted-oeis-proofs`, for recurrences with explicit rows below an offset
`P (n + 3) = …`, for summands in other orders, and for the hints, the certificates and
the `?` variants of the degree tactics.
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

/-- A three-term recurrence with offset three and explicit rows `0, 1, 2`, whose degree
multiplier ratio is `1` (A084534). -/
def A084534 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1 + 2 * X
  | 2 => 1 + 4 * X + 2 * X ^ 2
  | n + 3 => ((1 + (2 * X))) * A084534 (n + 2) + ((-1 * (X) ^ (2))) * A084534 (n + 1)

theorem A084534_natDegree (n : ℕ) : (A084534 n).natDegree = n := by rr_row_natDegree
theorem A084534_ne_zero (n : ℕ) : A084534 n ≠ 0 := by rr_row_ne_zero
theorem A084534_leadingCoeff_pos (n : ℕ) : 0 < (A084534 n).leadingCoeff := by
  rr_row_leadingCoeff_pos

/-- The certificate printed by `rr_row_natDegree?` for `A084534_natDegree`. -/
example (n : ℕ) : (A084534 n).natDegree = n := by
  rcases n with _ | n
  · rr_row_side
  refine (?_ : ((fun m => A084534 (m + 1)) n).natDegree = 1 + 1 * n).trans (by lia)
  apply RealRooted.threeTermRatio_natDegree (P := fun m => A084534 (m + 1)) (d := 1) (D₀ := 1)
    (ρ := (1 : ℝ)) fun _ => rfl <;> rr_row_side

/-- The hinted call printed by `rr_row_natDegree?` for `A084534_natDegree`. -/
example (n : ℕ) : (A084534 n).natDegree = n := by
  rr_row_natDegree (degree := 1) (growth := 1) (drop := 0) (ratio := 1)

#guard_msgs (drop info) in
example (n : ℕ) : A084534 n ≠ 0 := by rr_row_ne_zero?

/-- Offset three with nonnegative coefficients (A102413). -/
def A102413 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1 + X
  | 2 => 1 + 4 * X + X ^ 2
  | n + 3 => ((1 + X)) * A102413 (n + 2) + (X) * A102413 (n + 1)

theorem A102413_natDegree (n : ℕ) : (A102413 n).natDegree = n := by rr_row_natDegree
theorem A102413_ne_zero (n : ℕ) : A102413 n ≠ 0 := by rr_row_ne_zero

/-- Offset three with `b = -(1 + X) ^ 2` (A103450). -/
def A103450 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1 + X
  | 2 => 1 + 3 * X + X ^ 2
  | n + 3 => ((2 + (2 * X))) * A103450 (n + 2) +
      ((-1 + (-1 * (X) ^ (2)) + (-2 * X))) * A103450 (n + 1)

theorem A103450_natDegree (n : ℕ) : (A103450 n).natDegree = n := by rr_row_natDegree
theorem A103450_leadingCoeff_pos (n : ℕ) : 0 < (A103450 n).leadingCoeff := by
  rr_row_leadingCoeff_pos

/-- A three-term recurrence with the summands and factors in another order. -/
def swappedLag : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1 + X
  | n + 2 => X * swappedLag n + swappedLag (n + 1) * (1 + X)

theorem swappedLag_natDegree (n : ℕ) : (swappedLag n).natDegree = n := by rr_row_natDegree
theorem swappedLag_leadingCoeff_pos (n : ℕ) : 0 < (swappedLag n).leadingCoeff := by
  rr_row_leadingCoeff_pos

/-- The certificate printed by `rr_row_natDegree?` for `swappedLag_natDegree`. -/
example (n : ℕ) : (swappedLag n).natDegree = n := by
  refine (?_ : (swappedLag n).natDegree = 0 + 1 * n).trans (by lia)
  apply RealRooted.threeTermPos_natDegree (P := swappedLag) (d := 1) (D₀ := 0)
    (show ∀ (n : ℕ), swappedLag (n + 2) = (1 + X) * swappedLag (n + 1) + X * swappedLag n from
      fun n => (swappedLag.eq_3 n).trans (by ring)) <;> rr_row_side

/-- A subtracted summand (the rows of A056241). -/
def subtractedLag : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1 + X
  | n + 2 => (2 + 2 * X) * subtractedLag (n + 1) - (1 + X + X ^ 2) * subtractedLag n

theorem subtractedLag_natDegree (n : ℕ) : (subtractedLag n).natDegree = n := by
  rr_row_natDegree

/-- A first-order recurrence with the derivative summand last (the rows of A008277). -/
def swappedDeriv : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => (1 + X) * swappedDeriv n + X * (swappedDeriv n).derivative

theorem swappedDeriv_natDegree (n : ℕ) : (swappedDeriv n).natDegree = n := by rr_row_natDegree
theorem swappedDeriv_ne_zero (n : ℕ) : swappedDeriv n ≠ 0 := by rr_row_ne_zero

/-- A product with the factor on the right. -/
def swappedProduct : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => swappedProduct n * (2 + X)

theorem swappedProduct_natDegree (n : ℕ) : (swappedProduct n).natDegree = n := by
  rr_row_natDegree
theorem swappedProduct_ne_zero (n : ℕ) : swappedProduct n ≠ 0 := by rr_row_ne_zero

/-- Hints skip the search. -/
example (n : ℕ) : (A008277 n).natDegree = n := by rr_row_natDegree (degree := 0) (growth := 1)
example (n : ℕ) : (A011973 n).natDegree = n / 2 := by
  rr_row_natDegree (degree := 0) (growth := 1) (half := 0)
example (n : ℕ) : (A055356 n).natDegree = n - 1 := by rr_row_natDegree (drop := 1)

/-- Goals about shifted rows. -/
example (n : ℕ) : (A084534 (n + 2)).natDegree = n + 2 := by rr_row_natDegree
example (n : ℕ) : A102413 (n + 1) ≠ 0 := by rr_row_ne_zero

end

end RealRooted.Tactic.RowDataExamples
