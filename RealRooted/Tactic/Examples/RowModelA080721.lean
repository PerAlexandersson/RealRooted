module

public import RealRooted.Applications.OEIS.A080721
public import RealRooted.Tactic.RowInterlacing

/-!
# Regression examples for OEIS A080721

The definition and goals below retain the exact generated downstream syntax.
-/

@[expose] public noncomputable section

open RealRooted Polynomial

namespace RealRooted.Tactic.RowModelA080721Examples

/-- The literal downstream recurrence presentation of A080721. -/
def A080721 : ℕ → ℝ[X]
  | 0 => 1 + 4 * X + 4 * X ^ 2
  | 1 => 1 + 9 * X + 21 * X ^ 2 + 14 * X ^ 3
  | 2 => 1 + 16 * X + 66 * X ^ 2 + 100 * X ^ 3 + 50 * X ^ 4
  | 3 => 1 + 25 * X + 160 * X ^ 2 + 410 * X ^ 3 + 455 * X ^ 4 + 182 * X ^ 5
  | n + 4 => ((C (((1 / ((6 + (n : ℝ)))) * (13 + ((5 / 2) * (n : ℝ))))) +
      C (((1 / ((6 + (n : ℝ)))) * (26 + (5 * (n : ℝ))))) * X)) * A080721 (n + 3) +
    ((C (((1 / ((6 + (n : ℝ)))) * ((-19 / 2) + ((-5 / 2) * (n : ℝ))))) +
      C (((1 / ((6 + (n : ℝ)))) * (-14 + (-4 * (n : ℝ))))) * X +
      C (((1 / ((6 + (n : ℝ)))) * (-14 + (-4 * (n : ℝ))))) * X ^ 2)) *
        A080721 (n + 2) +
    ((C (((1 / ((6 + (n : ℝ)))) * (3 + ((3 / 2) * (n : ℝ))))) +
      C (((1 / ((6 + (n : ℝ)))) * (6 + (3 * (n : ℝ))))) * X)) *
        A080721 (n + 1) +
    (C (((1 / ((6 + (n : ℝ)))) * ((-1 / 2) + ((-1 / 2) * (n : ℝ)))))) *
      A080721 n

example (n : ℕ) : RealRooted.Interlaces (A080721 n) (A080721 (n + 1)) := by
  rr_row_interlaces

example (n : ℕ) : RealRooted.StrictInterl (A080721 n) (A080721 (n + 1)) := by
  exact (show RealRooted.Interlaces (A080721 n) (A080721 (n + 1)) by
    rr_row_interlaces).toStrictInterl

end RealRooted.Tactic.RowModelA080721Examples
