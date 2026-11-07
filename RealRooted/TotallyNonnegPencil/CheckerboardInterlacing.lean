module

public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Determinant.TotallyNonneg
public import RealRooted.Basic.ProperPosition
import RealRooted.TotallyNonnegPencil.Interlacing
public import RealRooted.Mathlib.LinearAlgebra.Matrix.Checkerboard
import RealRooted.Mathlib.LinearAlgebra.Matrix.JacobiComplementaryMinor
import Mathlib.Tactic

/-! # Consecutive checkerboard-signed determinant pencils -/

public section

namespace Matrix

/-- Invertible lower triangular TN variable matrices give consecutive
checkerboard pencil determinant interlacing. -/
theorem IsLowerTriangular.leading_det_map_add_X_smul_checkerboard_interlaces
    {n : ℕ} {L M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hLtri : L.IsLowerTriangular) (hL : L.IsTotallyNonneg)
    (hdet : 0 < L.det) (hM : M.IsTotallyNonneg) :
    RealRooted.Interlaces
      (det ((M.submatrix Fin.castSucc Fin.castSucc).map Polynomial.C +
        (Polynomial.X : Polynomial ℝ) •
          (checkerboard (L.submatrix Fin.castSucc Fin.castSucc)).map Polynomial.C))
      (det (M.map Polynomial.C +
        (Polynomial.X : Polynomial ℝ) • (checkerboard L).map Polynomial.C)) := by
  have hunit : IsUnit L.det := isUnit_iff_ne_zero.mpr hdet.ne'
  have hLI : L * L⁻¹ = 1 := L.mul_nonsing_inv hunit
  have hAI : checkerboard L * checkerboard L⁻¹ = 1 := by
    rw [← checkerboard_mul, hLI, checkerboard_one]
  have hAtri : (checkerboard L).IsLowerTriangular := by
    intro i j hij
    simp [checkerboard, hLtri hij]
  have hAunit : IsUnit (checkerboard L).det :=
    Matrix.isUnit_det_of_right_inverse hAI
  have hAinv : (checkerboard L)⁻¹ = checkerboard L⁻¹ :=
    Matrix.inv_eq_right_inv hAI
  have hAinvTN : (checkerboard L)⁻¹.IsTotallyNonneg := by
    rw [hAinv]
    exact IsTotallyNonneg.checkerboard_inverse L L⁻¹ hLI hdet hL
  simpa only [checkerboard_submatrix_castSucc] using
    hAtri.leading_det_map_add_X_smul_interlaces hAunit hAinvTN hM

end Matrix
