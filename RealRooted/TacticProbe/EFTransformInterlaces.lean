module

public import RealRooted.Tactic.RowInterlacing

set_option rr.row.explain true
set_option linter.style.longLine false

/-!
# Regression examples for the `f`-polynomial interlacing route

The two alternating-run rows below have transformed auxiliary rows of degree
`(n + 1) / 2`.  The automatic row tactic transfers their strict interlacing
through `fPolynomial`.
-/

@[expose] public section

open RealRooted Polynomial

noncomputable section

namespace FTransformInterlacingExamples

/-- The A008970 row recurrence. -/
def a008970 : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 =>
      (C 1 * X + C (-1) * X ^ 3) * (a008970 n).derivative +
        (C 1 + C 2 * X + C (n : ℝ) * X ^ 2) * a008970 n

/-- Consecutive A008970 rows interlace via the transformed auxiliary rows. -/
example (n : ℕ) : Interlaces (a008970 n) (a008970 (n + 1)) := by
  rr_row_interlaces

/-- The A059427 row recurrence. -/
def a059427 : ℕ → ℝ[X]
  | 0 => 2
  | n + 1 =>
      (C 1 * X + C (-1) * X ^ 3) * (a059427 n).derivative +
        (C 1 + C 2 * X + C (n : ℝ) * X ^ 2) * a059427 n

/-- Consecutive A059427 rows interlace via the transformed auxiliary rows. -/
example (n : ℕ) : Interlaces (a059427 n) (a059427 (n + 1)) := by
  rr_row_interlaces

end FTransformInterlacingExamples
