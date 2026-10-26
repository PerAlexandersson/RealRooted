module

public import RealRooted.Applications.OEIS.A297191
public import RealRooted.Applications.OEIS.A394446
public import RealRooted.Recurrence.RowModel
public import RealRooted.Recurrence.Uniqueness

set_option rr.row.explain true
set_option linter.style.longLine false

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

/-- Split-row transfer for the quadratic A297191 presentation.  Row three
distinguishes it from A394446, whose first three rows agree. -/
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

namespace A394446

/-- The derivative-recurrence presentation supplied for A394446. -/
def row : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1 + 3 * X + X ^ 2
  | n + 2 =>
      (C (-4 * (1 / (4 + (n : ℝ)))) * X +
          C (-6 * (1 / (4 + (n : ℝ)))) * X ^ 2 +
          C (-2 * (1 / (4 + (n : ℝ)))) * X ^ 3) *
          (row (n + 1)).derivative +
        (C ((1 / (4 + (n : ℝ))) * (7 + 4 * (n : ℝ))) +
          C ((1 / (4 + (n : ℝ))) * (22 + 13 * (n : ℝ))) * X +
          C ((1 / (4 + (n : ℝ))) * (8 + 5 * (n : ℝ))) * X ^ 2) *
          row (n + 1) +
        (C ((1 / (4 + (n : ℝ))) * (-3 + -3 * (n : ℝ))) +
          C ((1 / (4 + (n : ℝ))) * (-3 + -3 * (n : ℝ))) * X +
          C ((1 / (4 + (n : ℝ))) * (-3 + -3 * (n : ℝ))) * X ^ 2) * row n

private theorem row_eq_polynomial (n : ℕ) :
    row n = Applications.OEIS.A394446.polynomial n := by
  induction n using Nat.twoStepInduction with
  | zero => rfl
  | one => rfl
  | more n ih ih_succ =>
      rw [row, ih, ih_succ, Applications.OEIS.A394446.polynomial_add_two]
      have hneg4 : C (-4 * (1 / (4 + (n : ℝ)))) =
          C (-4 / ((n : ℝ) + 4)) := by
        congr 1
        ring
      have hneg6 : C (-6 * (1 / (4 + (n : ℝ)))) =
          C (-6 / ((n : ℝ) + 4)) := by
        congr 1
        ring
      have hneg2 : C (-2 * (1 / (4 + (n : ℝ)))) =
          C (-2 / ((n : ℝ) + 4)) := by
        congr 1
        ring
      have hmain0 : C ((1 / (4 + (n : ℝ))) * (7 + 4 * (n : ℝ))) =
          C (((4 * n : ℝ) + 7) / ((n : ℝ) + 4)) := by
        congr 1
        ring
      have hmain1 : C ((1 / (4 + (n : ℝ))) * (22 + 13 * (n : ℝ))) =
          C (((13 * n : ℝ) + 22) / ((n : ℝ) + 4)) := by
        congr 1
        ring
      have hmain2 : C ((1 / (4 + (n : ℝ))) * (8 + 5 * (n : ℝ))) =
          C (((5 * n : ℝ) + 8) / ((n : ℝ) + 4)) := by
        congr 1
        ring
      have hlag : C ((1 / (4 + (n : ℝ))) * (-3 + -3 * (n : ℝ))) =
          C ((-3 * ((n : ℝ) + 1)) / ((n : ℝ) + 4)) := by
        congr 1
        ring
      rw [hneg4, hneg6, hneg2, hmain0, hmain1, hmain2, hlag]
      dsimp only [Applications.OEIS.A394446.quadraticFactor]
      ring

example (n : ℕ) : row n =
    gammaTransform (2 * n) (narayanaPolynomial 1 n) := by
  rw [row_eq_polynomial,
    Applications.OEIS.A394446.polynomial_eq_gammaTransform]

example (n : ℕ) : (row n).Splits := by
  rw [row_eq_polynomial]
  exact Applications.OEIS.A394446.splits_polynomial n

/-- Split-row transfer for the derivative-lag A394446 presentation.  Row
three distinguishes it from A297191, whose first three rows agree. -/
@[rr_row_model]
theorem splits_of_recurrence
    {P : ℕ → ℝ[X]}
    (hzero : P 0 = 1)
    (hone : P 1 = 1 + 3 * X + X ^ 2)
    (_htwo : P 2 = 1 + 7 * X + 13 * X ^ 2 + 7 * X ^ 3 + X ^ 4)
    (_hthree : P 3 =
      1 + 12 * X + 45 * X ^ 2 + 69 * X ^ 3 + 45 * X ^ 4 + 12 * X ^ 5 + X ^ 6)
    (hrec : ∀ n : ℕ,
      P (n + 2) =
        (C (-4 * (1 / (4 + (n : ℝ)))) * X +
          C (-6 * (1 / (4 + (n : ℝ)))) * X ^ 2 +
          C (-2 * (1 / (4 + (n : ℝ)))) * X ^ 3) * (P (n + 1)).derivative +
        (C ((1 / (4 + (n : ℝ))) * (7 + 4 * (n : ℝ))) +
          C ((1 / (4 + (n : ℝ))) * (22 + 13 * (n : ℝ))) * X +
          C ((1 / (4 + (n : ℝ))) * (8 + 5 * (n : ℝ))) * X ^ 2) * P (n + 1) +
        (C ((1 / (4 + (n : ℝ))) * (-3 + -3 * (n : ℝ))) +
          C ((1 / (4 + (n : ℝ))) * (-3 + -3 * (n : ℝ))) * X +
          C ((1 / (4 + (n : ℝ))) * (-3 + -3 * (n : ℝ))) * X ^ 2) * P n)
    (n : ℕ) :
    (P n).Splits := by
  let update : ℕ → ℝ[X] → ℝ[X] → ℝ[X] := fun n p q =>
    (C (-4 * (1 / (4 + (n : ℝ)))) * X +
        C (-6 * (1 / (4 + (n : ℝ)))) * X ^ 2 +
        C (-2 * (1 / (4 + (n : ℝ)))) * X ^ 3) * p.derivative +
      (C ((1 / (4 + (n : ℝ))) * (7 + 4 * (n : ℝ))) +
        C ((1 / (4 + (n : ℝ))) * (22 + 13 * (n : ℝ))) * X +
        C ((1 / (4 + (n : ℝ))) * (8 + 5 * (n : ℝ))) * X ^ 2) * p +
      (C ((1 / (4 + (n : ℝ))) * (-3 + -3 * (n : ℝ))) +
        C ((1 / (4 + (n : ℝ))) * (-3 + -3 * (n : ℝ))) * X +
        C ((1 / (4 + (n : ℝ))) * (-3 + -3 * (n : ℝ))) * X ^ 2) * q
  have heq := sequence_eq_of_same_lag_two_recurrence update
    (hzero.trans (show (1 : ℝ[X]) = row 0 by rfl))
    (hone.trans (show (1 + 3 * X + X ^ 2 : ℝ[X]) = row 1 by rfl))
    hrec (fun _ => rfl)
  rw [heq n, row_eq_polynomial]
  exact Applications.OEIS.A394446.splits_polynomial n

end A394446

end RealRooted.Tactic.Examples.OEIS.DegreeTwoGamma
