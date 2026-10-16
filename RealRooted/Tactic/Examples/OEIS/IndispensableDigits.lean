module

public import RealRooted.Applications.OEIS.IndispensableDigits
public import RealRooted.Tactic.RowInterlacing

/-!
# Row-tactic regressions for indispensable-digit models
-/

@[expose] public section

open Polynomial
open RealRooted

noncomputable section

namespace RealRooted.Tactic.IndispensableDigitsExamples

/-- Final-state recurrence, matching OEIS A330509. -/
def finalRows : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1 + 3 * X
  | 2 => 1 + 9 * X + 6 * X ^ 2
  | n + 3 => (3 + 3 * X) * finalRows (n + 2) +
      (-3 - 3 * X - 3 * X ^ 2) * finalRows (n + 1) +
      (1 + X + X ^ 2 + X ^ 3) * finalRows n

/-- The registered final-state transfer closes the exact downstream goal. -/
theorem finalRows_interlaces (n : ℕ) :
    Interlaces (finalRows n) (finalRows (n + 1)) := by
  rr_row_interlaces

/-- The final-state model also closes the splitting projection. -/
example (n : ℕ) : (finalRows n).Splits := by
  rr_row_splits

/-- Strict-position form of the final-state regression. -/
theorem finalRows_prec (n : ℕ) :
    StrictInterl (finalRows n) (finalRows (n + 1)) := by
  exact (finalRows_interlaces n).toStrictInterl

/-- Total-state recurrence, matching OEIS A340620. -/
def totalRows : ℕ → ℝ[X]
  | 0 => 3
  | 1 => 6 + 6 * X
  | 2 => 10 + 28 * X + 10 * X ^ 2
  | n + 3 => (3 + 3 * X) * totalRows (n + 2) +
      (-3 - 3 * X - 3 * X ^ 2) * totalRows (n + 1) +
      (1 + X + X ^ 2 + X ^ 3) * totalRows n

/-- The registered total-state transfer closes the exact downstream goal. -/
theorem totalRows_interlaces (n : ℕ) :
    Interlaces (totalRows n) (totalRows (n + 1)) := by
  rr_row_interlaces

/-- The total-state model also closes the splitting projection. -/
example (n : ℕ) : (totalRows n).Splits := by
  rr_row_splits

/-- Strict-position form of the total-state regression. -/
theorem totalRows_prec (n : ℕ) :
    StrictInterl (totalRows n) (totalRows (n + 1)) := by
  exact (totalRows_interlaces n).toStrictInterl

end RealRooted.Tactic.IndispensableDigitsExamples
