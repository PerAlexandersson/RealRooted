module

public import RealRooted.Applications.OEIS.A111910
public import RealRooted.Applications.OEIS.A155495
public import RealRooted.Applications.OEIS.A359363
public import RealRooted.Applications.OEIS.ReflectedEulerRows
public import RealRooted.Tactic.RowInterlacing

set_option rr.row.explain true
set_option linter.style.longLine false

/-!
# Downstream registry presentations

Regression examples for recurrence presentations that spell out the registered model operator
literally. The final two families guard against expensive attempts by structurally similar but
incorrect registered models.
-/

@[expose] public section

open RealRooted Polynomial

noncomputable section

namespace RealRooted.Tactic.RegistryDownstreamExamples

/-- The downstream literal recurrence presentation of A111910. -/
def A111910 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1 + X
  | n + 2 =>
      (C ((1 / (10 + 2 * (3 + (n : ℝ)) ^ 2 + 3 * (n : ℝ))) *
          (42 + 18 * (n : ℝ))) * X +
        C ((1 / (10 + 2 * (3 + (n : ℝ)) ^ 2 + 3 * (n : ℝ))) *
          (-42 + -18 * (n : ℝ))) * X ^ 2) * (A111910 (n + 1)).derivative +
      (C ((1 / (10 + 2 * (3 + (n : ℝ)) ^ 2 + 3 * (n : ℝ))) *
          (40 + -2 * (3 + (n : ℝ)) ^ 2 + 17 * (n : ℝ))) +
        C ((1 / (10 + 2 * (3 + (n : ℝ)) ^ 2 + 3 * (n : ℝ))) *
          (-80 + -31 * (n : ℝ) + 16 * (3 + (n : ℝ)) ^ 2)) * X) *
        A111910 (n + 1) +
      (C ((1 / (10 + 2 * (3 + (n : ℝ)) ^ 2 + 3 * (n : ℝ))) *
          (-30 + -14 * (n : ℝ) + 4 * (3 + (n : ℝ)) ^ 2)) +
        C ((1 / (10 + 2 * (3 + (n : ℝ)) ^ 2 + 3 * (n : ℝ))) *
          (-60 + -28 * (n : ℝ) + 8 * (3 + (n : ℝ)) ^ 2)) * X +
        C ((1 / (10 + 2 * (3 + (n : ℝ)) ^ 2 + 3 * (n : ℝ))) *
          (-30 + -14 * (n : ℝ) + 4 * (3 + (n : ℝ)) ^ 2)) * X ^ 2) * A111910 n

example (n : ℕ) : (A111910 n).Splits := by
  rr_row_splits

example (n : ℕ) : Interlaces (A111910 n) (A111910 (n + 1)) := by
  rr_row_interlaces

example (n : ℕ) : (A111910 n).natDegree = n := by
  rr_row_natDegree

/-- The downstream literal recurrence presentation of A155495. -/
def A155495 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1 + X
  | 2 => 1 + 12 * X + X ^ 2
  | n + 3 =>
      (C ((1 / ((-17 / 3) + (-5 / 3) * (n : ℝ) +
          (2 / 3) * (4 + (n : ℝ)) ^ 2)) * (-20 + -18 * (n : ℝ))) * X +
        C ((1 / ((-17 / 3) + (-5 / 3) * (n : ℝ) +
          (2 / 3) * (4 + (n : ℝ)) ^ 2)) * (20 + 18 * (n : ℝ))) * X ^ 2) *
        (A155495 (n + 2)).derivative +
      (C (-16 * (1 / ((-17 / 3) + (-5 / 3) * (n : ℝ) +
          (2 / 3) * (4 + (n : ℝ)) ^ 2))) * X +
        C (16 * (1 / ((-17 / 3) + (-5 / 3) * (n : ℝ) +
          (2 / 3) * (4 + (n : ℝ)) ^ 2))) * X ^ 3) *
        (A155495 (n + 1)).derivative +
      (C ((1 / ((-17 / 3) + (-5 / 3) * (n : ℝ) +
          (2 / 3) * (4 + (n : ℝ)) ^ 2)) *
          (-127 + 10 * (4 + (n : ℝ)) ^ 2 + (-131 / 3) * (n : ℝ))) +
        C ((1 / ((-17 / 3) + (-5 / 3) * (n : ℝ) +
          (2 / 3) * (4 + (n : ℝ)) ^ 2)) *
          (121 + -8 * (4 + (n : ℝ)) ^ 2 + (133 / 3) * (n : ℝ))) * X) *
        A155495 (n + 2) +
      (C ((1 / ((-17 / 3) + (-5 / 3) * (n : ℝ) +
          (2 / 3) * (4 + (n : ℝ)) ^ 2)) *
          ((488 / 3) + -12 * (4 + (n : ℝ)) ^ 2 + (178 / 3) * (n : ℝ))) +
        C ((1 / ((-17 / 3) + (-5 / 3) * (n : ℝ) +
          (2 / 3) * (4 + (n : ℝ)) ^ 2)) *
          ((-1952 / 3) + 48 * (4 + (n : ℝ)) ^ 2 + (-700 / 3) * (n : ℝ))) * X +
        C ((1 / ((-17 / 3) + (-5 / 3) * (n : ℝ) +
          (2 / 3) * (4 + (n : ℝ)) ^ 2)) *
          ((440 / 3) + -12 * (4 + (n : ℝ)) ^ 2 + (130 / 3) * (n : ℝ))) * X ^ 2) *
        A155495 (n + 1) +
      (C ((1 / ((-17 / 3) + (-5 / 3) * (n : ℝ) +
          (2 / 3) * (4 + (n : ℝ)) ^ 2)) *
          ((-124 / 3) + (-52 / 3) * (n : ℝ) + (8 / 3) * (4 + (n : ℝ)) ^ 2)) +
        C ((1 / ((-17 / 3) + (-5 / 3) * (n : ℝ) +
          (2 / 3) * (4 + (n : ℝ)) ^ 2)) *
          (-124 + -52 * (n : ℝ) + 8 * (4 + (n : ℝ)) ^ 2)) * X +
        C ((1 / ((-17 / 3) + (-5 / 3) * (n : ℝ) +
          (2 / 3) * (4 + (n : ℝ)) ^ 2)) *
          (-124 + -52 * (n : ℝ) + 8 * (4 + (n : ℝ)) ^ 2)) * X ^ 2 +
        C ((1 / ((-17 / 3) + (-5 / 3) * (n : ℝ) +
          (2 / 3) * (4 + (n : ℝ)) ^ 2)) *
          ((-124 / 3) + (-52 / 3) * (n : ℝ) + (8 / 3) * (4 + (n : ℝ)) ^ 2)) *
          X ^ 3) * A155495 n

example (n : ℕ) : (A155495 n).Splits := by
  rr_row_splits

example (n : ℕ) : Interlaces (A155495 n) (A155495 (n + 1)) := by
  rr_row_interlaces

example (n : ℕ) : (A155495 n).natDegree = n := by
  rr_row_natDegree

/-- The downstream literal recurrence presentation of A359363. -/
def A359363 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => X
  | n + 2 =>
      (C ((1 / ((11 / 2) + (1 / 2) * (3 + (n : ℝ)) ^ 2 +
          (3 / 2) * (n : ℝ))) * ((21 / 2) + (9 / 2) * (n : ℝ))) * X +
        C ((1 / ((11 / 2) + (1 / 2) * (3 + (n : ℝ)) ^ 2 +
          (3 / 2) * (n : ℝ))) * ((-21 / 2) + (-9 / 2) * (n : ℝ))) * X ^ 2) *
        (A359363 (n + 1)).derivative +
      (C ((1 / ((11 / 2) + (1 / 2) * (3 + (n : ℝ)) ^ 2 +
          (3 / 2) * (n : ℝ))) *
          (4 + 2 * (n : ℝ) + (-1 / 2) * (3 + (n : ℝ)) ^ 2)) +
        C ((1 / ((11 / 2) + (1 / 2) * (3 + (n : ℝ)) ^ 2 +
          (3 / 2) * (n : ℝ))) *
          ((-31 / 2) + 4 * (3 + (n : ℝ)) ^ 2 + (-11 / 2) * (n : ℝ))) * X) *
        A359363 (n + 1) +
      (C ((1 / ((11 / 2) + (1 / 2) * (3 + (n : ℝ)) ^ 2 +
          (3 / 2) * (n : ℝ))) *
          (-9 + (3 + (n : ℝ)) ^ 2 + -5 * (n : ℝ))) +
        C ((1 / ((11 / 2) + (1 / 2) * (3 + (n : ℝ)) ^ 2 +
          (3 / 2) * (n : ℝ))) *
          (-18 + -10 * (n : ℝ) + 2 * (3 + (n : ℝ)) ^ 2)) * X +
        C ((1 / ((11 / 2) + (1 / 2) * (3 + (n : ℝ)) ^ 2 +
          (3 / 2) * (n : ℝ))) *
          (-9 + (3 + (n : ℝ)) ^ 2 + -5 * (n : ℝ))) * X ^ 2) * A359363 n

example (n : ℕ) : (A359363 n).Splits := by
  rr_row_splits

example (n : ℕ) : Interlaces (A359363 n) (A359363 (n + 1)) := by
  rr_row_interlaces

example (n : ℕ) : (A359363 n).natDegree = n := by
  rr_row_natDegree

/-- A nonmatching second-derivative family must bypass the registry cheaply. -/
def A160562 : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 =>
      4 * X ^ 2 * (A160562 n).derivative.derivative +
        8 * X * (A160562 n).derivative + (1 + X) * A160562 n

example (n : ℕ) : (A160562 n).Splits := by
  rr_row_splits

example (n : ℕ) : Interlaces (A160562 n) (A160562 (n + 1)) := by
  rr_row_interlaces

example (n : ℕ) : (A160562 n).natDegree = n := by
  rr_row_natDegree

/-- A reflected Euler family must bypass an incorrect matching model cheaply. -/
def A191935 : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 =>
      C 1 * X ^ 3 * (A191935 n).derivative.derivative +
        C (-2 + -2 * (n : ℝ)) * X ^ 2 * (A191935 n).derivative +
          (C 1 + C (-2 + (2 + (n : ℝ)) ^ 2 + -(n : ℝ)) * X) * A191935 n

example (n : ℕ) : (A191935 n).Splits := by
  rr_row_splits

example (n : ℕ) : Interlaces (A191935 n) (A191935 (n + 1)) := by
  rr_row_interlaces

example (n : ℕ) : (A191935 n).natDegree = n := by
  rr_row_natDegree

end RealRooted.Tactic.RegistryDownstreamExamples
