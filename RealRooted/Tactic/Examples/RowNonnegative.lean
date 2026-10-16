module

public import RealRooted.Tactic.RowInterlacing

/-!
# General row-nonnegativity regression

These examples exercise arbitrary lags, derivative summands, and multipliers
whose coefficients are nonnegative polynomial expressions in the row index.
-/

@[expose] public section

open Polynomial RealRooted

noncomputable section

namespace RealRooted.Tactic.Examples

def nonnegativeLinRecRows : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1 + X
  | n + 2 =>
      (C ((n : ℝ) + 1) + C ((n : ℝ) ^ 2 + 3) * X) *
          (nonnegativeLinRecRows (n + 1)).derivative +
        (C ((n : ℝ) + 2) * X) * nonnegativeLinRecRows n

example : ∀ n, HasNonnegCoeffs (nonnegativeLinRecRows n) := by
  rr_row_nonneg_coeffs

def orderThreeNonnegativeRows : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1 + X
  | 2 => 1 + 2 * X
  | n + 3 =>
      (1 + X) * orderThreeNonnegativeRows (n + 2) +
        X * (orderThreeNonnegativeRows (n + 1)).derivative +
        C ((n : ℝ) + 1) * orderThreeNonnegativeRows n

example : ∀ n, HasNonnegCoeffs (orderThreeNonnegativeRows n) := by
  rr_row_nonneg_coeffs

def nonnegativeRowsAfterDrop : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 0
  | n + 2 =>
      C ((n : ℝ) - 1) * nonnegativeRowsAfterDrop (n + 1) +
        X * nonnegativeRowsAfterDrop n

example : ∀ n, HasNonnegCoeffs (nonnegativeRowsAfterDrop (n + 1)) := by
  rr_row_nonneg_coeffs

end RealRooted.Tactic.Examples
