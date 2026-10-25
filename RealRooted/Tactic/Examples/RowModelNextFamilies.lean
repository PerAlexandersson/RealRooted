module

public import RealRooted.Applications.OEIS.A304330
public import RealRooted.Tactic.RowInterlacing

/-!
# Regression examples for the next row-model families

These statements retain the generated downstream recurrence normalization.
-/

@[expose] public section

open RealRooted Polynomial

noncomputable section

namespace RealRooted.Tactic.RowModelNextFamilyExamples

/-- Recurrence presentation of the A304330 rows. -/
def A304330 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => X
  | n + 2 =>
      (X ^ 2 + 4 * X ^ 3) * (A304330 (n + 1)).derivative.derivative +
        (X + 10 * X ^ 2) * (A304330 (n + 1)).derivative +
        2 * X * A304330 (n + 1)

example (n : ℕ) : (A304330 n).Splits := by
  rr_row_splits

example (n : ℕ) : Interlaces (A304330 n) (A304330 (n + 1)) := by
  rr_row_interlaces

end RealRooted.Tactic.RowModelNextFamilyExamples
