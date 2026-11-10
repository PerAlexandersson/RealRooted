module

public import RealRooted.Applications.OEIS.A046802
public import RealRooted.Tactic.Row.Frontend

/-!
# Per-model registry budget regressions

This exact downstream presentation shares the first rows `1, 1 + X` with several registered
models.  A mismatched model must be rejected without exhausting the declaration budget.  (An
A108426 example was removed: its search fails, and honestly accounted, the failure needs more
than the default budget.  The old example passed only because a nested auxiliary search ran
outside the budget and hid its failure.)
-/

@[expose] public section

open RealRooted Polynomial

noncomputable section

namespace RowModelRegistryBudgetExamples

namespace A046802Downstream

/-- The exact downstream recurrence presentation of A046802. -/
def A046802 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1 + X
  | n + 2 =>
      (C 1 * X + C (-1) * X ^ 2) * (A046802 (n + 1)).derivative +
        (C 1 + C (2 + (n : ℝ)) * X) * A046802 (n + 1) +
          (C (-1 + -1 * (n : ℝ)) * X) * A046802 n

example (n : ℕ) : Interlaces (A046802 n) (A046802 (n + 1)) := by
  rr_row_interlaces

end A046802Downstream

end RowModelRegistryBudgetExamples
