import RealRooted.Tactic.RowInterlacing

open Polynomial

noncomputable section

namespace RealRooted.Tactic.Examples.RowCubicParent

/-- A184883, copied from the downstream row recurrence. -/
def a184883 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1 + X
  | 2 => 1 + 5 * X + X ^ 2
  | n + 3 =>
      (1 + 2 * X) * a184883 (n + 2) +
        (2 * X - X ^ 2) * a184883 (n + 1) + X ^ 2 * a184883 n

/-- A114123, copied from the downstream row recurrence. -/
def a114123 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1 + X
  | 2 => 1 + 5 * X + X ^ 2
  | n + 3 =>
      (2 + X) * a114123 (n + 2) +
        (-1 + 2 * X) * a114123 (n + 1) + X * a114123 n

/-- A216182, copied from the downstream row recurrence. -/
def a216182 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 3 + X
  | 2 => 5 + 7 * X + X ^ 2
  | n + 3 =>
      (2 + X) * a216182 (n + 2) +
        (-1 + 2 * X) * a216182 (n + 1) + X * a216182 n

example (n : ℕ) : (a184883 n).Splits := by
  rr_row_splits

example (n : ℕ) : (a114123 n).Splits := by
  rr_row_splits

example (n : ℕ) : (a216182 n).Splits := by
  rr_row_splits

end RealRooted.Tactic.Examples.RowCubicParent
