module

public import RealRooted.Applications.OEIS.A394813
public import RealRooted.Applications.OEIS.A395326
public import RealRooted.Tactic.RowInterlacing

/-!
# Regression examples for transform-backed OEIS row models

These examples retain the generated downstream recurrences and verify that the
row-model registry transfers their adjacent-interlacing theorems.
-/

@[expose] public noncomputable section

open Polynomial
open RealRooted

namespace RealRooted.Tactic.Examples.OEIS.TransformModels

def a394813Rows : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 2 + X
  | n + 2 =>
      (C 1 * X ^ 3) * (a394813Rows (n + 1)).derivative.derivative +
        (C (-1) * X ^ 3) * (a394813Rows n).derivative.derivative +
        (C (-3 - 2 * (n : ℝ)) * X ^ 2) * (a394813Rows (n + 1)).derivative +
        (C (2 * (n : ℝ)) * X ^ 2) * (a394813Rows n).derivative +
        (C 2 + C (-5 + (3 + (n : ℝ)) ^ 2 - 2 * (n : ℝ)) * X) *
          a394813Rows (n + 1) +
        (C (-1) + C (9 - (3 + (n : ℝ)) ^ 2 + 5 * (n : ℝ)) * X) *
          a394813Rows n

example (n : ℕ) : Interlaces (a394813Rows n) (a394813Rows (n + 1)) := by
  rr_row_interlaces

example (n : ℕ) : StrictInterl (a394813Rows n) (a394813Rows (n + 1)) := by
  have h : Interlaces (a394813Rows n) (a394813Rows (n + 1)) := by
    rr_row_interlaces
  exact h.toStrictInterl

def a395326Rows : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 2 * X
  | n + 2 =>
      (-4 * X ^ 2) * (a395326Rows n).derivative.derivative +
        (4 * X) * (a395326Rows (n + 1)).derivative +
        (-14 * X ^ 2 - 2 * X) * (a395326Rows n).derivative +
        (-1 + 8 * X) * a395326Rows (n + 1) +
        (-12 * X ^ 2 - 3 * X) * a395326Rows n

example (n : ℕ) : Interlaces (a395326Rows n) (a395326Rows (n + 1)) := by
  rr_row_interlaces

example (n : ℕ) : StrictInterl (a395326Rows n) (a395326Rows (n + 1)) := by
  have h : Interlaces (a395326Rows n) (a395326Rows (n + 1)) := by
    rr_row_interlaces
  exact h.toStrictInterl

end RealRooted.Tactic.Examples.OEIS.TransformModels
