module

import RealRooted.Tactic.RowInterlacing
import RealRooted.LiuWang.FiniteFamily
import RealRooted.WagnerX.AffineFactors
import RealRooted.Linear
public import RealRooted.Basic.ProperPosition

/-!
# A derivative--lag OEIS row

This file proves real-rootedness and the nonexceptional consecutive interlacing for A271697.
The row at index one is zero, so the interlacing chain starts at index two.
-/

@[expose] public section

open Polynomial

noncomputable section

namespace RealRooted.Applications.OEIS

/-- The recurrence-defined A271697 row family. -/
def A271697 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 0
  | n + 2 =>
      (X - X ^ 2) * (A271697 (n + 1)).derivative +
        C (1 + (n : ℝ)) * X * A271697 (n + 1) +
          C (1 + (n : ℝ)) * X * A271697 n

/-- The defining derivative--lag recurrence for A271697. -/
theorem A271697_add_two (n : ℕ) :
    A271697 (n + 2) =
      C (1 + (n : ℝ)) * X * A271697 (n + 1) +
        (X - X ^ 2) * (A271697 (n + 1)).derivative +
          C (1 + (n : ℝ)) * X * A271697 n := by
  rw [A271697]
  ring_nf

/-- The degree of A271697, including its exceptional zero row. -/
theorem A271697_natDegree (n : ℕ) : (A271697 n).natDegree = n - 1 := by
  rr_row_natDegree

/-- Consecutive A271697 rows strictly interlace from row two onward. -/
theorem A271697_strictInterl_add_two (m : ℕ) :
    StrictInterl (A271697 (m + 2)) (A271697 (m + 3)) := by
  rr_row_strictInterl

/-- Consecutive A271697 rows interlace from row two onward. -/
theorem A271697_interlaces_add_two (n : ℕ) :
    Interlaces (A271697 (n + 2)) (A271697 (n + 3)) :=
  (A271697_strictInterl_add_two n).toInterlaces (by
    rw [A271697_natDegree, A271697_natDegree]
    lia)

/-- Every A271697 row splits over the reals; row one is the zero polynomial. -/
theorem A271697_splits (n : ℕ) : (A271697 n).Splits := by
  rr_row_splits

end RealRooted.Applications.OEIS
