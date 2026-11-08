module

public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Determinant.TotallyNonneg
public import RealRooted.Basic.ProperPosition
import RealRooted.TotallyNonnegPencil.Interlacing
public import RealRooted.Mathlib.LinearAlgebra.Matrix.Checkerboard
import RealRooted.Mathlib.LinearAlgebra.Matrix.CheckerboardAdjacent
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
  simpa only [checkerboard_submatrix_castSucc] using
    (isLowerTriangular_checkerboard hLtri).leading_det_map_add_X_smul_interlaces
      (isUnit_det_checkerboard L hdet.ne'.isUnit) (hL.checkerboard_nonsing_inv hdet) hM

end Matrix
