module

public import RealRooted.Applications.OEIS.A046802
public import RealRooted.Tactic.RowInterlacing

/-!
# Per-model registry budget regressions

These exact downstream presentations share the first rows `1, 1 + X` with several registered
models.  A mismatched model must be rejected without exhausting the declaration budget.
-/

@[expose] public section

open RealRooted Polynomial

noncomputable section

namespace RowModelRegistryBudgetExamples

namespace A108426Downstream

/-- The exact downstream recurrence presentation of A108426. -/
def A108426 : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 =>
      (C ((1 / (-5 + -3 * (n : ℝ) + 2 * (2 + (n : ℝ)) ^ 2)) *
          (-3 + (-9 / 2) * (n : ℝ))) * X +
        C ((1 / (-5 + -3 * (n : ℝ) + 2 * (2 + (n : ℝ)) ^ 2)) *
            (-3 + -5 * (n : ℝ))) * X ^ 2 +
        C ((-1 / 2) * (n : ℝ) *
            (1 / (-5 + -3 * (n : ℝ) + 2 * (2 + (n : ℝ)) ^ 2))) * X ^ 3) *
        (A108426 n).derivative +
      (C ((1 / (-5 + -3 * (n : ℝ) + 2 * (2 + (n : ℝ)) ^ 2)) *
          (-51 + (-81 / 2) * (n : ℝ) + (27 / 2) * (2 + (n : ℝ)) ^ 2)) +
        C ((1 / (-5 + -3 * (n : ℝ) + 2 * (2 + (n : ℝ)) ^ 2)) *
            (-45 + 12 * (2 + (n : ℝ)) ^ 2 + (-71 / 2) * (n : ℝ))) * X +
        C ((1 / (-5 + -3 * (n : ℝ) + 2 * (2 + (n : ℝ)) ^ 2)) *
            (-2 + (1 / 2) * (2 + (n : ℝ)) ^ 2 + -2 * (n : ℝ))) * X ^ 2) *
        A108426 n

/-- Under the default heartbeat budget, a mismatched registry entry must not exhaust it. -/
example (n : ℕ) : Interlaces (A108426 n) (A108426 (n + 1)) := by
  rr_row_interlaces

end A108426Downstream

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
