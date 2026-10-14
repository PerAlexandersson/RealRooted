import RealRooted.Applications.OEIS.TouchardImages
import RealRooted.Tactic.RowInterlacing

open RealRooted Polynomial

noncomputable section

namespace RealRooted.Tactic.Examples.OEIS.TouchardImages

/-- The Euler-quotient Touchard presentation of the A069138 rows. -/
def eulerQuotientRows : ℕ → ℝ[X]
  | 0 => 2
  | 1 => 2 + 3 * X
  | n + 2 =>
      X * (eulerQuotientRows (n + 1)).derivative +
        (X - X ^ 2) * (eulerQuotientRows n).derivative +
        2 * X * eulerQuotientRows (n + 1) +
        (1 + X - X ^ 2) * eulerQuotientRows n

example (n : ℕ) :
    Interlaces (eulerQuotientRows n) (eulerQuotientRows (n + 1)) := by
  rr_row_interlaces

/-- The derivative Touchard presentation of the A321331 rows. -/
def derivativeRows : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1 + 2 * X
  | n + 2 =>
      X * (derivativeRows (n + 1)).derivative -
        X ^ 2 * (derivativeRows n).derivative +
        (1 + 2 * X) * derivativeRows (n + 1) -
        X ^ 2 * derivativeRows n

example (n : ℕ) : Interlaces (derivativeRows n) (derivativeRows (n + 1)) := by
  rr_row_interlaces

end RealRooted.Tactic.Examples.OEIS.TouchardImages
