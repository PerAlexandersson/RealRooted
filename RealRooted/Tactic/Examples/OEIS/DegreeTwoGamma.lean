module

public import RealRooted.Applications.OEIS.A297191
public import RealRooted.Recurrence.RowModel
public import RealRooted.Recurrence.Uniqueness

@[expose] public section

open Polynomial

noncomputable section

namespace RealRooted.Tactic.Examples.OEIS.DegreeTwoGamma

namespace A297191

/-- The degree-two recurrence presentation supplied for A297191. -/
def row : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1 + 3 * X + X ^ 2
  | n + 2 =>
      (1 + X ^ 2 + 4 * X) * row (n + 1) + (-1 * X ^ 2) * row n

private theorem row_eq_polynomial (n : ℕ) :
    row n = Applications.OEIS.A297191.polynomial n := by
  induction n using Nat.twoStepInduction with
  | zero => rfl
  | one => rfl
  | more n ih ih_succ =>
      rw [row, ih, ih_succ]
      change
        (1 + X ^ 2 + 4 * X) * Applications.OEIS.A297191.polynomial (n + 1) +
            (-1 * X ^ 2) * Applications.OEIS.A297191.polynomial n =
          (1 + 4 * X + X ^ 2) * Applications.OEIS.A297191.polynomial (n + 1) -
            X ^ 2 * Applications.OEIS.A297191.polynomial n
      ring

example (n : ℕ) : row n = gammaTransform (2 * n)
    (Applications.OEIS.A297191.gammaPolynomial n) := by
  rw [row_eq_polynomial,
    Applications.OEIS.A297191.polynomial_eq_gammaTransform]

example (n : ℕ) : (row n).Splits := by
  rw [row_eq_polynomial]
  exact Applications.OEIS.A297191.splits_polynomial n

/-- Split-row transfer for the quadratic A297191 presentation. -/
@[rr_row_model]
theorem splits_of_recurrence
    {P : ℕ → ℝ[X]}
    (hzero : P 0 = 1)
    (hone : P 1 = 1 + 3 * X + X ^ 2)
    (_htwo : P 2 = 1 + 7 * X + 13 * X ^ 2 + 7 * X ^ 3 + X ^ 4)
    (_hthree : P 3 =
      1 + 11 * X + 41 * X ^ 2 + 63 * X ^ 3 + 41 * X ^ 4 + 11 * X ^ 5 + X ^ 6)
    (hrec : ∀ n : ℕ,
      P (n + 2) = (1 + X ^ 2 + 4 * X) * P (n + 1) + (-1 * X ^ 2) * P n)
    (n : ℕ) :
    (P n).Splits := by
  have heq := sequence_eq_of_same_lag_two_recurrence
    (fun _ p q => (1 + X ^ 2 + 4 * X) * p + (-1 * X ^ 2) * q)
    (hzero.trans (show (1 : ℝ[X]) = row 0 by rfl))
    (hone.trans (show (1 + 3 * X + X ^ 2 : ℝ[X]) = row 1 by rfl))
    hrec (fun _ => rfl)
  rw [heq n, row_eq_polynomial]
  exact Applications.OEIS.A297191.splits_polynomial n

end A297191

end RealRooted.Tactic.Examples.OEIS.DegreeTwoGamma
