import RealRooted.Applications.OEIS.A297191
import RealRooted.Applications.OEIS.A394446

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

end A394446

end RealRooted.Tactic.Examples.OEIS.DegreeTwoGamma
