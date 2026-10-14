import RealRooted.Applications.OEIS.A079508
import RealRooted.Applications.OEIS.A119308
import RealRooted.Applications.OEIS.A155495
import RealRooted.Applications.OEIS.A318397
import RealRooted.Applications.OEIS.A367177
import RealRooted.Tactic.RowInterlacing

open RealRooted Polynomial

noncomputable section

namespace RealRooted.Tactic.RowModelJensenFamilyExamples

/-- Recurrence presentation of the A079508 rows. -/
def A079508 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => X
  | 2 => 2 * X + X ^ 2
  | n + 3 => Applications.OEIS.A079508.nextRow n (A079508 (n + 2))
      (A079508 (n + 1)) (A079508 n)

example (n : ℕ) : (A079508 n).Splits := by
  rr_row_splits

example (n : ℕ) : Interlaces (A079508 n) (A079508 (n + 1)) := by
  rr_row_interlaces

/-- Recurrence presentation of the A119308 rows. -/
def A119308 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 2 + X
  | 2 => 3 + 5 * X + X ^ 2
  | n + 3 => Applications.OEIS.A119308.nextRow n (A119308 (n + 2))
      (A119308 (n + 1)) (A119308 n)

example (n : ℕ) : (A119308 n).Splits := by
  rr_row_splits

example (n : ℕ) : Interlaces (A119308 n) (A119308 (n + 1)) := by
  rr_row_interlaces

/-- Recurrence presentation of the A155495 rows. -/
def A155495 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1 + X
  | 2 => 1 + 12 * X + X ^ 2
  | n + 3 => Applications.OEIS.A155495.nextRow n (A155495 (n + 2))
      (A155495 (n + 1)) (A155495 n)

example (n : ℕ) : (A155495 n).Splits := by
  rr_row_splits

example (n : ℕ) : Interlaces (A155495 n) (A155495 (n + 1)) := by
  rr_row_interlaces

/-- Recurrence presentation of the A318397 rows. -/
def A318397 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 2 + X
  | n + 2 => Applications.OEIS.A318397.nextRow n (A318397 (n + 1)) (A318397 n)

example (n : ℕ) : (A318397 n).Splits := by
  rr_row_splits

example (n : ℕ) : Interlaces (A318397 n) (A318397 (n + 1)) := by
  rr_row_interlaces

/-- Recurrence presentation of the A367177 rows. -/
def A367177 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1 + 2 * X
  | n + 2 => Applications.OEIS.A367177.nextRow n (A367177 (n + 1)) (A367177 n)

example (n : ℕ) : (A367177 n).Splits := by
  rr_row_splits

example (n : ℕ) : Interlaces (A367177 n) (A367177 (n + 1)) := by
  rr_row_interlaces

end RealRooted.Tactic.RowModelJensenFamilyExamples
