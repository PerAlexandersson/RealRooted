module

public import RealRooted.Applications.OEIS.A056939
public import RealRooted.Applications.OEIS.A111910
public import RealRooted.Applications.OEIS.A181543
public import RealRooted.Applications.OEIS.A359363
public import RealRooted.Tactic.RowInterlacing

@[expose] public section

open RealRooted Polynomial

noncomputable section

namespace RealRooted.Tactic.RowModelFamilyExamples

/-- Recurrence presentation of the A056939 rows. -/
def A056939 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1 + X
  | n + 2 => Applications.OEIS.A056939.nextRow n (A056939 (n + 1)) (A056939 n)

example (n : ℕ) : (A056939 n).Splits := by
  rr_row_splits

/-- Recurrence presentation of the A111910 rows. -/
def A111910 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1 + X
  | n + 2 => Applications.OEIS.A111910.nextRow n (A111910 (n + 1)) (A111910 n)

example (n : ℕ) : (A111910 n).Splits := by
  rr_row_splits

/-- Recurrence presentation of the A359363 rows. -/
def A359363 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => X
  | n + 2 => Applications.OEIS.A359363.nextRow n (A359363 (n + 1)) (A359363 n)

example (n : ℕ) : (A359363 n).Splits := by
  rr_row_splits

/-- Recurrence presentation of the binomial-cube rows. -/
def A181543 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1 + X
  | n + 2 => ((C (((1 / ((-5 + ((3 + (n : ℝ))) ^ (2) + (-2 * (n : ℝ))))) * (12 + (9 * (n :
    ℝ))))) * X + C (((1 / ((-5 + ((3 + (n : ℝ))) ^ (2) + (-2 * (n : ℝ))))) * (-12 + (-9 * (n :
    ℝ))))) * X ^ 2)) * (A181543 (n + 1)).derivative + ((C (((1 / ((-5 + ((3 + (n : ℝ))) ^ (2) +
    (-2 * (n : ℝ))))) *
      (11 + (-1 * ((3 + (n : ℝ))) ^ (2)) + (6 * (n : ℝ))))) + C (((1 / ((-5 +
    ((3 + (n : ℝ))) ^ (2) + (-2 * (n : ℝ))))) *
      (-58 + (-27 * (n : ℝ)) + (8 * ((3 + (n : ℝ))) ^
    (2))))) * X)) * A181543 (n + 1) + ((C (((1 / ((-5 + ((3 + (n : ℝ))) ^ (2) + (-2 * (n :
    ℝ))))) * (-16 + (-8 * (n : ℝ)) + (2 * ((3 + (n : ℝ))) ^ (2))))) + C (((1 / ((-5 +
    ((3 + (n : ℝ))) ^ (2) + (-2 * (n : ℝ))))) *
      (-32 + (-16 * (n : ℝ)) + (4 * ((3 + (n : ℝ))) ^ (2))))) * X
    + C (((1 / ((-5 + ((3 + (n : ℝ))) ^ (2) + (-2 * (n : ℝ))))) * (-16 + (-8 * (n : ℝ)) + (2 *
    ((3 + (n : ℝ))) ^ (2))))) * X ^ 2)) * A181543 n

example (n : ℕ) : (A181543 n).Splits := by
  rr_row_splits

example (n : ℕ) : RealRooted.Interlaces (A181543 n) (A181543 (n + 1)) := by
  rr_row_interlaces

end RealRooted.Tactic.RowModelFamilyExamples
