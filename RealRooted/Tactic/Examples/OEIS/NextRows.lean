module

public import RealRooted.Applications.OEIS.A046802
public import RealRooted.Tactic.RowInterlacing

/-!
# An exact downstream presentation for a recurrence-model bridge
-/

@[expose] public section

open RealRooted Polynomial

noncomputable section

namespace A046802Downstream

/-- The OEIS A046802 polynomial sequence, given by a literal recurrence with derivative terms. -/
def A046802 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1 + X
  | n + 2 =>
      (C 1 * X + C (-1) * X ^ 2) * (A046802 (n + 1)).derivative +
        (C 1 + C (2 + (n : ℝ)) * X) * A046802 (n + 1) +
          (C (-1 + -1 * (n : ℝ)) * X) * A046802 n

example (n : ℕ) : (A046802 n).Splits := by
  rr_row_splits

example (n : ℕ) : Interlaces (A046802 n) (A046802 (n + 1)) := by
  rr_row_interlaces

end A046802Downstream

