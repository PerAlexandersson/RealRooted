import RealRooted.Applications.OEIS.HarmonicDerivativeRows
import RealRooted.Tactic.RowInterlacing

/-!
# Harmonic derivative-row model regression

The definition and goals below are the literal downstream A199221 recurrence.
-/

open RealRooted Polynomial

namespace A199221Downstream

noncomputable section

def A199221 : ℕ → ℝ[X]
  | 0 => 1 + 4 * X + 2 * X ^ 2
  | 1 => 2 + 12 * X + 18 * X ^ 2 + 6 * X ^ 3
  | 2 => 3 + 28 * X + 83 * X ^ 2 + 88 * X ^ 3 + 24 * X ^ 4
  | n + 3 =>
      ((C (2) + C ((7 + (2 * (n : ℝ)))) * X)) * A199221 (n + 2) +
        ((C (-1) + C ((-4 + (-2 * (n : ℝ)))) * X +
          C ((12 + (-1 * ((4 + (n : ℝ))) ^ (2)) + (4 * (n : ℝ)))) * X ^ 2)) *
            A199221 (n + 1) +
        ((C (-2) * X + C ((-10 + (-4 * (n : ℝ)))) * X ^ 2 +
          C ((20 + (-2 * ((4 + (n : ℝ))) ^ (2)) + (6 * (n : ℝ)))) * X ^ 3)) *
            A199221 n

example (n : ℕ) :
    RealRooted.Interlaces (A199221 n) (A199221 (n + 1)) := by
  rr_row_interlaces

example (n : ℕ) :
    RealRooted.StrictInterl (A199221 n) (A199221 (n + 1)) := by
  exact (show RealRooted.Interlaces (A199221 n) (A199221 (n + 1)) by
    rr_row_interlaces).toStrictInterl

end

end A199221Downstream
