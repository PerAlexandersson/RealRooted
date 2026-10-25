module

public import RealRooted.CombinatorialExamples.Eulerian
public import RealRooted.CombinatorialExamples.Narayana
public import RealRooted.CombinatorialExamples.Simsun
public import RealRooted.CombinatorialExamples.TypeBEulerian
public import RealRooted.Tactic.RowInterlacing

/-!
# Row-reader normalization regressions

These examples check that the row tactics distribute row-independent factors over recurrence
sums and unfold named, non-recursive coefficient blocks whose bodies use the supported
rational-polynomial grammar.
-/

@[expose] public section

open Polynomial

namespace RealRooted.Tactic.RowReaderNormalizationExamples

noncomputable section

/-! ## An outer polynomial factor -/

example (n : ℕ) : (eulerianTilde n).natDegree = n + 1 := by
  rr_row_natDegree

example (n : ℕ) : 0 < (eulerianTilde n).leadingCoeff := by
  rr_row_leadingCoeff_pos

example (n : ℕ) : HasNonnegCoeffs (eulerianTilde n) := by
  rr_row_nonneg_coeffs

example (n : ℕ) : Interlaces (eulerianTilde n) (eulerianTilde (n + 1)) := by
  rr_row_interlaces

/-- A nested recurrence with row-independent factors on both sides of the sum. -/
def twoSidedOuterRows : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => C 2 * ((twoSidedOuterRows n + X * twoSidedOuterRows n) * C 3)

example (n : ℕ) : (twoSidedOuterRows n).natDegree = n := by
  rr_row_natDegree

example (n : ℕ) : 0 < (twoSidedOuterRows n).leadingCoeff := by
  rr_row_leadingCoeff_pos

/-! ## Named coefficient blocks -/

example (n : ℕ) : (narayanaCoeffA n).natDegree ≤ 1 := by
  rr_row_side

example (n : ℕ) : (narayanaQuot (n + 1)).natDegree = n := by
  rr_row_natDegree

example (n : ℕ) : 0 < (narayanaQuot (n + 1)).leadingCoeff := by
  rr_row_leadingCoeff_pos

example (n : ℕ) : (typeBEulerian n).natDegree = n := by
  rr_row_natDegree

example (n : ℕ) : 0 < (typeBEulerian n).leadingCoeff := by
  rr_row_leadingCoeff_pos

example (n : ℕ) : HasNonnegCoeffs (typeBEulerian n) := by
  rr_row_nonneg_coeffs

example (n : ℕ) : Interlaces (typeBEulerian n) (typeBEulerian (n + 1)) := by
  rr_row_interlaces

example (n : ℕ) : (simsun n).natDegree = n / 2 := by
  rr_row_natDegree

example (n : ℕ) : 0 < (simsun n).leadingCoeff := by
  rr_row_leadingCoeff_pos

example (n : ℕ) : (simsun n).Splits := by
  rr_row_splits

/-! ## Refused nonlinear recurrences -/

/-- The row reader must not distribute a factor that itself contains a row. -/
def nonlinearOuterRows : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => nonlinearOuterRows n * (nonlinearOuterRows n + X)

example : True := by
  fail_if_success
    have _ : ∀ n, (nonlinearOuterRows n).natDegree = n := by rr_row_natDegree
  trivial

/-- Composition in the recursive row is nonlinear and remains outside the reader grammar. -/
def composedRows : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => (composedRows n).comp (1 + X)

example : True := by
  fail_if_success
    have _ : ∀ n, (composedRows n).natDegree = n := by rr_row_natDegree
  trivial

end

end RowReaderNormalizationExamples

end Tactic

end RealRooted
