module

public import RealRooted.Tactic.RowInterlacing

set_option rr.row.explain true
set_option linter.style.longLine false

/-!
# Degree laws with zero residue classes

Regression examples for two-step products and a reduced three-term recurrence whose odd rows
vanish.  The latter exercises the residue-class fallback of `rr_row_natDegree`.
-/

@[expose] public section

open Polynomial

namespace RealRooted.Tactic.Examples.RowSubseqDegree

noncomputable section

/-- A two-step product whose odd rows vanish and whose live rows grow by degree one. -/
def zeroOddDegreeOne : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 0
  | n + 2 => X * zeroOddDegreeOne n

/-- A two-step product whose odd rows vanish and whose live rows grow by degree two. -/
def zeroOddDegreeTwo : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 0
  | n + 2 => X ^ 2 * zeroOddDegreeTwo n

/-- A constant two-step product with different degrees in the two residue classes. -/
def alternatingDegree : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1 + X
  | n + 2 => 1 * alternatingDegree n

/-- A reduced three-term recurrence whose odd residue class vanishes. -/
def zeroOddThreeTerm : ℕ → ℝ[X]
  | 0 => 2 * X
  | 1 => 0
  | 2 => 3 * X ^ 2
  | 3 => 0
  | n + 4 => 2 * X * zeroOddThreeTerm (n + 2) - X ^ 2 * zeroOddThreeTerm n

example (n : ℕ) :
    (zeroOddDegreeOne n).natDegree = if n % 2 = 1 then 0 else n / 2 := by
  rr_row_natDegree

example (n : ℕ) :
    (zeroOddDegreeTwo n).natDegree = if n % 2 = 1 then 0 else n := by
  rr_row_natDegree

example (n : ℕ) :
    (alternatingDegree n).natDegree = if n % 2 = 1 then 1 else 0 := by
  rr_row_natDegree

example (n : ℕ) :
    (zeroOddThreeTerm n).natDegree = if n % 2 = 1 then 0 else n / 2 + 1 := by
  rr_row_natDegree

example (n : ℕ) : (zeroOddDegreeTwo n).Splits := by
  rr_row_splits

example (n : ℕ) : (zeroOddDegreeOne n).Splits := by
  rr_row_splits

example (n : ℕ) : (alternatingDegree n).Splits := by
  rr_row_splits

example (n : ℕ) : (zeroOddThreeTerm n).Splits := by
  rr_row_splits

end

end RealRooted.Tactic.Examples.RowSubseqDegree
