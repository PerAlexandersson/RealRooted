module

public import RealRooted.Tactic.RowInterlacing

set_option rr.row.explain true
set_option linter.style.longLine false

/-!
# Fixed-factor and small row-adapter regressions

These examples cover the fixed-factor deflation route, an arbitrary-offset product tail,
and a degree-pattern derivative recurrence with normalized rational coefficients.
-/

@[expose] public section

open Polynomial

namespace RealRooted.Tactic.RowFactorPowerExamples

noncomputable section

/-- OEIS A090452 in its generated two-lag coefficient form. -/
def A090452 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1 + 3 * X + 2 * X ^ 2
  | n + 2 =>
      (C (1 / (4 + (n : ℝ)) * (5 + 2 * (n : ℝ))) +
          C (1 / (4 + (n : ℝ)) * (15 + 6 * (n : ℝ))) * X +
          C (1 / (4 + (n : ℝ)) * (10 + 4 * (n : ℝ))) * X ^ 2) * A090452 (n + 1) +
        (C (1 / (4 + (n : ℝ)) * (-1 - (n : ℝ))) +
          C (1 / (4 + (n : ℝ)) * (-2 - 2 * (n : ℝ))) * X +
          C (1 / (4 + (n : ℝ)) * (-1 - (n : ℝ))) * X ^ 2) * A090452 n

example (n : ℕ) : (A090452 n).Splits := by
  rr_row_splits

/-- OEIS A109983 in its generated two-lag coefficient form. -/
def A109983 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => X + 2 * X ^ 2
  | n + 2 =>
      (C (1 / (-2 - (n : ℝ)) * (-3 - 2 * (n : ℝ))) * X +
          C (1 / (-2 - (n : ℝ)) * (-6 - 4 * (n : ℝ))) * X ^ 2) * A109983 (n + 1) +
        C (1 / (-2 - (n : ℝ)) * (1 + (n : ℝ))) * X ^ 2 * A109983 n

example (n : ℕ) : (A109983 n).Splits := by
  rr_row_splits

/-- OEIS A316649 in its generated order-three coefficient form. -/
def A316649 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => X + 2 * X ^ 2
  | 2 => X + 7 * X ^ 2 + 12 * X ^ 3 + 6 * X ^ 4
  | n + 3 =>
      (C (1 / (-3 - (n : ℝ)) * (-5 - 2 * (n : ℝ))) +
          C (1 / (-3 - (n : ℝ)) * (-15 - 6 * (n : ℝ))) * X +
          C (1 / (-3 - (n : ℝ)) * (-10 - 4 * (n : ℝ))) * X ^ 2) * A316649 (n + 2) +
        (C (1 / (-3 - (n : ℝ)) * (2 + (n : ℝ))) +
          C (1 / (-3 - (n : ℝ)) * (4 + 2 * (n : ℝ))) * X +
          C (1 / (-3 - (n : ℝ)) * (2 + (n : ℝ))) * X ^ 2) * A316649 (n + 1)

example (n : ℕ) : (A316649 n).Splits := by
  rr_row_splits

/-- OEIS A147644, whose recurrence is a product only after three exceptional rows. -/
def A147644 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1 + X
  | 2 => 1 + 2 * X + X ^ 2
  | 3 => 1 + 5 * X + 5 * X ^ 2 + X ^ 3
  | n + 4 => (1 + X) * A147644 (n + 3)

example (n : ℕ) : (A147644 n).Splits := by
  rr_row_splits

/-- OEIS A263789, with half-growth and a rational derivative multiplier. -/
def A263789 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1
  | n + 2 =>
      (C (1 / (-1 / 2 - 1 / 2 * (n : ℝ)) * (-2 - (n : ℝ))) * X +
          C (1 / (-1 / 2 - 1 / 2 * (n : ℝ)) * (2 + (n : ℝ))) * X ^ 2) *
          (A263789 (n + 1)).derivative +
        C (1 / (-1 / 2 - 1 / 2 * (n : ℝ)) *
            (7 / 2 - 1 / 2 * (3 + (n : ℝ)) ^ 2 + 3 / 2 * (n : ℝ))) * X *
          A263789 (n + 1)

example (n : ℕ) : (A263789 n).Splits := by
  rr_row_splits

/-- A one-step product remains on the pre-existing route, not `delayedProduct`. -/
def ordinaryProduct : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => (1 + X) * ordinaryProduct n

/--
info: Try these:
  [apply] rr_row_splits (via := closedForm)
-/
example (n : ℕ) : (ordinaryProduct n).Splits := by
  rr_row_splits?

end
end RowFactorPowerExamples
end Tactic
end RealRooted
