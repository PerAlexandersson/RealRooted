import RealRooted.Mathlib.Algebra.LinearRecurrence.Annihilator
import RealRooted.TridiagonalDet

/-!
# Linear recurrence for tridiagonal determinants

This opt-in client packages the existing tridiagonal determinant recurrence as
a Mathlib `LinearRecurrence` and applies the generic annihilator bridge.
-/

namespace RealRooted

/-- The constant-coefficient recurrence satisfied by tridiagonal Toeplitz
determinants. -/
def tridiagMDetRecurrence (d s b : ℝ) : LinearRecurrence ℝ :=
  ⟨2, ![-s * b, d]⟩

/-- The tridiagonal Toeplitz determinant sequence solves its characteristic
recurrence. -/
theorem tridiagM_det_isSolution (d s b : ℝ) :
    (tridiagMDetRecurrence d s b).IsSolution (fun n ↦ (tridiagM d s b n).det) := by
  intro n
  unfold tridiagMDetRecurrence
  simp only [Fin.sum_univ_two, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.vecEmpty, Fin.val_zero, Fin.val_one]
  rw [tridiagM_det_rec]
  simp
  ring

/-- The characteristic polynomial of the tridiagonal determinant recurrence
annihilates its determinant sequence under the forward shift. -/
theorem tridiagM_det_aeval_charPoly_eq_zero (d s b : ℝ) :
    Polynomial.aeval LinearRecurrence.forwardShift (tridiagMDetRecurrence d s b).charPoly
      (fun n ↦ (tridiagM d s b n).det) = 0 :=
  LinearRecurrence.isSolution_iff_aeval_charPoly_eq_zero _ _ |>.mp
    (tridiagM_det_isSolution d s b)

end RealRooted
