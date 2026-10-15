import RealRooted.Applications.OEIS.A259454
import RealRooted.Tactic.RowInterlacing

/-!
# Literal downstream regression for OEIS A259454

The definition and theorem statements below are the generated downstream presentation.
-/

open RealRooted Polynomial

noncomputable section

namespace A259454Downstream

def A259454 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1 + 3 * X
  | 2 => 1 + 6 * X + 7 * X ^ 2
  | n + 3 =>
      (C ((10 / 7) * (1 / (-3 + -1 * (n : ℝ)))) * X +
          C ((26 / 7) * (1 / (-3 + -1 * (n : ℝ)))) * X ^ 2) *
          (A259454 (n + 2)).derivative +
        (C ((-3 / 7) * (1 / (-3 + -1 * (n : ℝ)))) * X +
          C ((-10 / 7) * (1 / (-3 + -1 * (n : ℝ)))) * X ^ 2 +
          C ((-33 / 7) * (1 / (-3 + -1 * (n : ℝ)))) * X ^ 3) *
          (A259454 (n + 1)).derivative +
        (C ((1 / (-3 + -1 * (n : ℝ))) *
            (-27 / 7 + (-10 / 7) * (n : ℝ))) +
          C ((1 / (-3 + -1 * (n : ℝ))) *
            (-101 / 7 + (-40 / 7) * (n : ℝ))) * X) *
          A259454 (n + 2) +
        (C ((1 / (-3 + -1 * (n : ℝ))) *
            (6 / 7 + (3 / 7) * (n : ℝ))) +
          C ((1 / (-3 + -1 * (n : ℝ))) * (5 / 7 + (n : ℝ))) * X +
          C ((1 / (-3 + -1 * (n : ℝ))) *
            (40 / 7 + (33 / 7) * (n : ℝ))) * X ^ 2) *
          A259454 (n + 1) +
        (C ((3 / 7) * (1 / (-3 + -1 * (n : ℝ))) *
            (4 + (n : ℝ))) * X ^ 2 +
          C ((1 / (-3 + -1 * (n : ℝ))) * (4 + (n : ℝ))) * X ^ 3) *
          A259454 n

theorem A259454_interlaces (n : ℕ) :
    RealRooted.Interlaces (A259454 n) (A259454 (n + 1)) := by
  rr_row_interlaces

theorem A259454_prec (n : ℕ) :
    RealRooted.StrictInterl (A259454 n) (A259454 (n + 1)) := by
  exact (show Interlaces (A259454 n) (A259454 (n + 1)) by
    rr_row_interlaces).toStrictInterl

end A259454Downstream
