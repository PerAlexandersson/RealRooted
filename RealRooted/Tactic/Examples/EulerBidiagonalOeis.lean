module

public import RealRooted.Tactic

/-!
# Euler-bidiagonal OEIS regressions

Exact copies of seven downstream recurrences whose consecutive-row interlacing follows from
the general Euler-bidiagonal step. The first six use positive parameters; A269945 is the
zero-parameter boundary case.
-/

@[expose] public section

open Polynomial RealRooted

noncomputable section

namespace RealRooted.Tactic.EulerBidiagonalOeisExamples

/-- The downstream A156289 rows. -/
def A156289 : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 =>
      X ^ 2 * (A156289 n).derivative.derivative +
        (2 * X ^ 2 + 3 * X) * (A156289 n).derivative + (1 + 3 * X) * A156289 n

/-- Consecutive A156289 rows interlace by the general Euler-bidiagonal step. -/
theorem A156289_interlaces (n : ℕ) : Interlaces (A156289 n) (A156289 (n + 1)) := by
  rr_row_interlaces (thm := RealRooted.EulerBidiagonal.interlaces_of_generalStep_rec)

/-- Consecutive A156289 rows are in strict interlacing position. -/
theorem A156289_prec (n : ℕ) : StrictInterl (A156289 n) (A156289 (n + 1)) := by
  exact (A156289_interlaces n).toStrictInterl

/-- The downstream A166960 rows. -/
def A166960 : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 =>
      (C 1 * X ^ 2) * (A166960 n).derivative.derivative +
        (C 3 * X + C (-1) * X ^ 2) * (A166960 n).derivative +
        (C 1 + C (1 + (n : ℝ)) * X) * A166960 n

/-- Consecutive A166960 rows interlace by the general Euler-bidiagonal step. -/
theorem A166960_interlaces (n : ℕ) : Interlaces (A166960 n) (A166960 (n + 1)) := by
  rr_row_interlaces (thm := RealRooted.EulerBidiagonal.interlaces_of_generalStep_rec)

/-- Consecutive A166960 rows are in strict interlacing position. -/
theorem A166960_prec (n : ℕ) : StrictInterl (A166960 n) (A166960 (n + 1)) := by
  exact (A166960_interlaces n).toStrictInterl

/-- The downstream A166961 rows. -/
def A166961 : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 =>
      (C 2 * X ^ 2) * (A166961 n).derivative.derivative +
        (C 5 * X + C (-2) * X ^ 2) * (A166961 n).derivative +
        (C 1 + C (1 + 2 * (n : ℝ)) * X) * A166961 n

/-- Consecutive A166961 rows interlace by the general Euler-bidiagonal step. -/
theorem A166961_interlaces (n : ℕ) : Interlaces (A166961 n) (A166961 (n + 1)) := by
  rr_row_interlaces (thm := RealRooted.EulerBidiagonal.interlaces_of_generalStep_rec)

/-- Consecutive A166961 rows are in strict interlacing position. -/
theorem A166961_prec (n : ℕ) : StrictInterl (A166961 n) (A166961 (n + 1)) := by
  exact (A166961_interlaces n).toStrictInterl

/-- The downstream A166962 rows. -/
def A166962 : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 =>
      (C 3 * X ^ 2) * (A166962 n).derivative.derivative +
        (C 7 * X + C (-3) * X ^ 2) * (A166962 n).derivative +
        (C 1 + C (1 + 3 * (n : ℝ)) * X) * A166962 n

/-- Consecutive A166962 rows interlace by the general Euler-bidiagonal step. -/
theorem A166962_interlaces (n : ℕ) : Interlaces (A166962 n) (A166962 (n + 1)) := by
  rr_row_interlaces (thm := RealRooted.EulerBidiagonal.interlaces_of_generalStep_rec)

/-- Consecutive A166962 rows are in strict interlacing position. -/
theorem A166962_prec (n : ℕ) : StrictInterl (A166962 n) (A166962 (n + 1)) := by
  exact (A166962_interlaces n).toStrictInterl

/-- The downstream A166972 rows. -/
def A166972 : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 =>
      (C 3 * X ^ 2) * (A166972 n).derivative.derivative +
        (C 7 * X + C (-1) * X ^ 2) * (A166972 n).derivative +
        (C 1 + C (1 + (n : ℝ)) * X) * A166972 n

/-- Consecutive A166972 rows interlace by the general Euler-bidiagonal step. -/
theorem A166972_interlaces (n : ℕ) : Interlaces (A166972 n) (A166972 (n + 1)) := by
  rr_row_interlaces (thm := RealRooted.EulerBidiagonal.interlaces_of_generalStep_rec)

/-- Consecutive A166972 rows are in strict interlacing position. -/
theorem A166972_prec (n : ℕ) : StrictInterl (A166972 n) (A166972 (n + 1)) := by
  exact (A166972_interlaces n).toStrictInterl

/-- The downstream A160562 rows. -/
def A160562 : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 =>
      (4 * X ^ 2) * (A160562 n).derivative.derivative +
        (8 * X) * (A160562 n).derivative + (1 + X) * A160562 n

/-- Consecutive A160562 rows interlace by the general Euler-bidiagonal step. -/
theorem A160562_interlaces (n : ℕ) : Interlaces (A160562 n) (A160562 (n + 1)) := by
  rr_row_interlaces (thm := RealRooted.EulerBidiagonal.interlaces_of_generalStep_rec)

/-- Consecutive A160562 rows are in strict interlacing position. -/
theorem A160562_prec (n : ℕ) : StrictInterl (A160562 n) (A160562 (n + 1)) := by
  exact (A160562_interlaces n).toStrictInterl

/-- The downstream A269945 rows. -/
def A269945 : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 =>
      X ^ 2 * (A269945 n).derivative.derivative +
        X * (A269945 n).derivative + X * A269945 n

/-- Consecutive A269945 rows interlace by the zero-parameter Euler-bidiagonal step. -/
theorem A269945_interlaces (n : ℕ) : Interlaces (A269945 n) (A269945 (n + 1)) := by
  rr_row_interlaces (thm := RealRooted.EulerBidiagonal.interlaces_of_generalStep_rec)

/-- Consecutive A269945 rows are in strict interlacing position. -/
theorem A269945_prec (n : ℕ) : StrictInterl (A269945 n) (A269945 (n + 1)) := by
  exact (A269945_interlaces n).toStrictInterl

end RealRooted.Tactic.EulerBidiagonalOeisExamples
