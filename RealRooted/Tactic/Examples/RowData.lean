module

public import RealRooted.Tactic.Recurrence
public import RealRooted.Tactic.Examples.RowFixtures

/-!
# `rr_row_*` examples

Regression tests for OEIS rows defined by derivative recurrences, drawn from
`real-rooted-oeis-proofs`, for recurrences with explicit rows below an offset
`P (n + 3) = …`, for summands in other orders, and for the hints, the certificates and
the `?` variants of the degree tactics.
-/

@[expose] public noncomputable section

open Polynomial
open RealRooted.Tactic.RowFixtures

namespace RealRooted.Tactic.RowDataExamples

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

/-- Half growth with `n`-dependent coefficients and degree `(n + 1) / 2`. -/
def halfGrowthRows : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1 + X
  | n + 2 => C ((n : ℝ) + 2) * halfGrowthRows (n + 1) + (C 1 * X) * halfGrowthRows n

theorem halfGrowthRows_natDegree (n : ℕ) : (halfGrowthRows n).natDegree = (n + 1) / 2 := by
  rr_row_natDegree

/-- A zero first row is split off; `h` excludes it (A128966). -/
def A128966 : ℕ → ℝ[X]
  | 0 => 0
  | 1 => 1 + X
  | n + 2 => (1 + X) * A128966 (n + 1) + X * A128966 n

theorem A128966_natDegree (n : ℕ) : (A128966 n).natDegree = n := by rr_row_natDegree
theorem A128966_ne_zero (n : ℕ) (h : n ≠ 0) : A128966 n ≠ 0 := by rr_row_ne_zero

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

theorem A102413_natDegree (n : ℕ) : (A102413 n).natDegree = n := by rr_row_natDegree
theorem A102413_ne_zero (n : ℕ) : A102413 n ≠ 0 := by rr_row_ne_zero

theorem A103450_natDegree (n : ℕ) : (A103450 n).natDegree = n := by rr_row_natDegree
theorem A103450_leadingCoeff_pos (n : ℕ) : 0 < (A103450 n).leadingCoeff := by
  rr_row_leadingCoeff_pos

theorem swappedLag_natDegree (n : ℕ) : (swappedLag n).natDegree = n := by rr_row_natDegree
theorem swappedLag_leadingCoeff_pos (n : ℕ) : 0 < (swappedLag n).leadingCoeff := by
  rr_row_leadingCoeff_pos

/-- The certificate printed by `rr_row_natDegree?` for `swappedLag_natDegree`. -/
example (n : ℕ) : (swappedLag n).natDegree = n := by
  refine (?_ : (swappedLag n).natDegree = 0 + 1 * n).trans (by lia)
  apply RealRooted.threeTermPos_natDegree (P := swappedLag) (d := 1) (D₀ := 0)
    (show ∀ (n : ℕ), swappedLag (n + 2) = (1 + X) * swappedLag (n + 1) + X * swappedLag n from
      fun n => (swappedLag.eq_3 n).trans (by ring)) <;> rr_row_side

theorem subtractedLag_natDegree (n : ℕ) : (subtractedLag n).natDegree = n := by
  rr_row_natDegree

theorem swappedDeriv_natDegree (n : ℕ) : (swappedDeriv n).natDegree = n := by rr_row_natDegree
theorem swappedDeriv_ne_zero (n : ℕ) : swappedDeriv n ≠ 0 := by rr_row_ne_zero

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

end RealRooted.Tactic.RowDataExamples
