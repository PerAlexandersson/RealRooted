import RealRooted.Applications.OEIS.A046802
import RealRooted.Applications.OEIS.A132166
import RealRooted.Applications.OEIS.A262226
import RealRooted.Tactic.RowInterlacing

/-!
# Exact downstream presentations for three recurrence-model bridges
-/

open RealRooted Polynomial

noncomputable section

namespace A046802Downstream

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

namespace A132166Downstream

def A132166 : ℕ → ℝ[X]
  | 0 => 336 + 42 * X + X ^ 2
  | n + 1 =>
      (C (18 * (1 / (2 + (1 / 2) * (n : ℝ)))) * X +
          C ((1 / 2) * (1 / (2 + (1 / 2) * (n : ℝ)))) * X ^ 2) *
          (A132166 n).derivative +
        (C ((1 / (2 + (1 / 2) * (n : ℝ))) * (27 + 3 * (n : ℝ))) +
          C (1 / (2 + (1 / 2) * (n : ℝ))) * X) * A132166 n

example (n : ℕ) : (A132166 n).Splits := by
  rr_row_splits

example (n : ℕ) : Interlaces (A132166 n) (A132166 (n + 1)) := by
  rr_row_interlaces

end A132166Downstream

namespace A262226Downstream

def A262226 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1
  | n + 2 =>
      (C 2 * X + C (-2) * X ^ 2) * (A262226 (n + 1)).derivative +
        (C (-2) * X + C 4 * X ^ 2 + C (-2) * X ^ 3) *
          (A262226 n).derivative +
        (C 2 + C (2 + 2 * (n : ℝ)) * X) * A262226 (n + 1) +
        (C (-1) + C (-2 * (n : ℝ)) * X + C (1 + 2 * (n : ℝ)) * X ^ 2) *
          A262226 n

example (n : ℕ) : (A262226 n).Splits := by
  rr_row_splits

end A262226Downstream
