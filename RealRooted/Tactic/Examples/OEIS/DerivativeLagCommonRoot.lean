import RealRooted.Tactic.Row.DerivLag

open Polynomial RealRooted

noncomputable section

namespace RealRooted.Tactic.DerivativeLagCommonRootExamples

example : StrictInterl (X : ℝ[X]) (X + X ^ 2) := by
  refine Interlaces.toStrictInterl ?_
  rr_interlaces_explicit

/-- A derivative--lag family with a zero row and a persistent root at zero. -/
def commonZeroLag : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 0
  | n + 2 =>
      (C 1 * X + C (-1) * X ^ 2) * (commonZeroLag (n + 1)).derivative +
        (C (1 + (n : ℝ)) * X) * commonZeroLag (n + 1) +
          (C (1 + (n : ℝ)) * X) * commonZeroLag n

example (n : ℕ) : (commonZeroLag n).Splits := by
  rr_row_deriv_lag_splits

end RealRooted.Tactic.DerivativeLagCommonRootExamples
