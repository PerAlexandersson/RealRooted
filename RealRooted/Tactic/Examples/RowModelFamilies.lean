module

public import RealRooted.Applications.OEIS.A056939
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

/-- Recurrence presentation of the A359363 rows. -/
def A359363 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => X
  | n + 2 => Applications.OEIS.A359363.nextRow n (A359363 (n + 1)) (A359363 n)

example (n : ℕ) : (A359363 n).Splits := by
  rr_row_splits

end RealRooted.Tactic.RowModelFamilyExamples
