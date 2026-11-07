module

public import RealRooted.TotallyNonnegPencil
public import RealRooted.Mathlib.LinearAlgebra.Matrix.Checkerboard
import RealRooted.Mathlib.LinearAlgebra.Matrix.Charpoly.DeterminantPencil
import RealRooted.Mathlib.LinearAlgebra.Matrix.JacobiComplementaryMinor
import RealRooted.Mathlib.LinearAlgebra.Matrix.TotallyNonneg.Mul

/-! # Pólya-frequency determinant pencils with checkerboard signs -/

public section

open Polynomial

namespace Matrix

/-- A totally nonnegative constant matrix with positive determinant and a
checkerboard-signed totally nonnegative variable matrix give a PF determinant. -/
theorem IsTotallyNonneg.isPFPolynomial_det_map_add_X_smul_checkerboard
    {n : ℕ} {M L : Matrix (Fin n) (Fin n) ℝ}
    (hM : M.IsTotallyNonneg) (hL : L.IsTotallyNonneg) (hdet : 0 < M.det) :
    RealRooted.IsPFPolynomial
      (det (M.map C + (X : ℝ[X]) • (checkerboard L).map C)) := by
  have hMB : M * M⁻¹ = 1 := M.mul_nonsing_inv (isUnit_iff_ne_zero.mpr hdet.ne')
  have hN : (checkerboard M⁻¹).IsTotallyNonneg :=
    IsTotallyNonneg.checkerboard_inverse M M⁻¹ hMB hdet hM
  have hproduct := (hN.mul hL).isPFPolynomial_det_one_add_X_smul
  let S : Matrix (Fin n) (Fin n) ℝ := diagonal (fun i ↦ (-1 : ℝ) ^ i.val)
  rw [checkerboard_eq_diagonal_mul L]
  rw [det_map_add_X_smul_of_mul_eq_one M M⁻¹ L S hMB]
  have hfactor : S * M⁻¹ * S * L = checkerboard M⁻¹ * L := by
    rw [checkerboard_eq_diagonal_mul]
  rw [hfactor]
  exact hproduct.const_mul hdet

end Matrix
