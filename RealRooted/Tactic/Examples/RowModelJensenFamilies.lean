module

public import RealRooted.Applications.OEIS.A119308
public import RealRooted.Tactic.RowInterlacing

@[expose] public section

open RealRooted Polynomial

noncomputable section

namespace RealRooted.Tactic.RowModelJensenFamilyExamples

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

end RealRooted.Tactic.RowModelJensenFamilyExamples
