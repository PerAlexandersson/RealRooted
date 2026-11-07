module

public import RealRooted.TotallyNonnegInterlacing
public import RealRooted.Mathlib.LinearAlgebra.Matrix.LeadingSections
public import RealRooted.Mathlib.LinearAlgebra.Matrix.Charpoly.DeterminantPencil
import RealRooted.Mathlib.LinearAlgebra.Matrix.TotallyNonneg.Mul
import RealRooted.Basic.AffineInterlacing
import RealRooted.Interlacing.ReversalCommonFactor

/-! # Interlacing for leading sections of a triangular determinant pencil

No Hessenberg assumption is needed.
-/

public section

open Polynomial

namespace Matrix

/-- Consecutive leading positive characteristic determinant polynomials of a
TN matrix interlace. -/
theorem IsTotallyNonneg.leading_det_X_smul_one_add_map_interlaces
    {n : ℕ} {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hH : H.IsTotallyNonneg) :
    RealRooted.Interlaces
      (det ((X : ℝ[X]) • (1 : Matrix (Fin n) (Fin n) ℝ[X]) +
        (H.submatrix Fin.castSucc Fin.castSucc).map C))
      (det ((X : ℝ[X]) • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ[X]) +
        H.map C)) := by
  rw [det_X_smul_one_add_map_eq_C_mul_charpoly_comp_neg_X,
    det_X_smul_one_add_map_eq_C_mul_charpoly_comp_neg_X]
  exact (RealRooted.interlaces_comp_neg_X hH.leading_charpoly_interlaces).C_mul_both
    (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
    (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))

/-- Invertible lower triangular left factors with TN inverse produce
interlacing determinant polynomials on consecutive leading sections.

The affine pencil is normalized by multiplying it on the left by the inverse
of its linear coefficient matrix. -/
theorem IsLowerTriangular.leading_det_X_smul_one_add_inv_mul_interlaces
    {n : ℕ} {A M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hA : A.IsLowerTriangular) (hdet : IsUnit A.det)
    (hinv : A⁻¹.IsTotallyNonneg) (hM : M.IsTotallyNonneg) :
    RealRooted.Interlaces
      (det ((X : ℝ[X]) • (1 : Matrix (Fin n) (Fin n) ℝ[X]) +
        ((A.submatrix Fin.castSucc Fin.castSucc)⁻¹ *
          M.submatrix Fin.castSucc Fin.castSucc).map C))
      (det ((X : ℝ[X]) • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ[X]) +
        (A⁻¹ * M).map C)) := by
  have hH := (hinv.mul hM).leading_det_X_smul_one_add_map_interlaces
  rw [hA.leading_submatrix_inv_mul hdet M] at hH
  exact hH

/-- Dividing an affine determinant by the determinant of its invertible linear
coefficient matrix normalizes it to a positive characteristic determinant. -/
theorem C_inv_det_mul_det_map_add_X_smul
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M A : Matrix ι ι ℝ) (hdet : IsUnit A.det) :
    C A.det⁻¹ * det (M.map C + (X : ℝ[X]) • A.map C) =
      det ((X : ℝ[X]) • (1 : Matrix ι ι ℝ[X]) + (A⁻¹ * M).map C) := by
  rw [Matrix.det_map_add_X_smul_eq_det_mul_of_mul_eq_one M A A⁻¹
      (Matrix.mul_nonsing_inv A hdet),
    ← mul_assoc, ← C_mul, inv_mul_cancel₀ hdet.ne_zero, C_1, one_mul]

/-- Consecutive leading affine determinant pencils interlace after normalizing
by the determinant of the linear coefficient matrix. It suffices that this
matrix is invertible lower triangular with TN inverse, and that the constant
coefficient matrix is TN; no Hessenberg condition is needed. -/
theorem IsLowerTriangular.leading_normalized_det_map_add_X_smul_interlaces
    {n : ℕ} {A M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hA : A.IsLowerTriangular) (hdet : IsUnit A.det)
    (hinv : A⁻¹.IsTotallyNonneg) (hM : M.IsTotallyNonneg) :
    RealRooted.Interlaces
      (C (A.submatrix Fin.castSucc Fin.castSucc).det⁻¹ *
        det ((M.submatrix Fin.castSucc Fin.castSucc).map C +
          (X : ℝ[X]) • (A.submatrix Fin.castSucc Fin.castSucc).map C))
      (C A.det⁻¹ * det (M.map C + (X : ℝ[X]) • A.map C)) := by
  rw [C_inv_det_mul_det_map_add_X_smul _ _
      (hA.isUnit_det_leading_submatrix hdet),
    C_inv_det_mul_det_map_add_X_smul M A hdet]
  exact hA.leading_det_X_smul_one_add_inv_mul_interlaces hdet hinv hM

/-- Leading affine determinant polynomials interlace when their linear
coefficient matrix is invertible lower triangular with TN inverse and their
constant coefficient matrix is TN. -/
theorem IsLowerTriangular.leading_det_map_add_X_smul_interlaces
    {n : ℕ} {A M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hA : A.IsLowerTriangular) (hdet : IsUnit A.det)
    (hinv : A⁻¹.IsTotallyNonneg) (hM : M.IsTotallyNonneg) :
    RealRooted.Interlaces
      (det ((M.submatrix Fin.castSucc Fin.castSucc).map C +
        (X : ℝ[X]) • (A.submatrix Fin.castSucc Fin.castSucc).map C))
      (det (M.map C + (X : ℝ[X]) • A.map C)) := by
  have hdet₀ := hA.isUnit_det_leading_submatrix hdet
  rw [Matrix.det_map_add_X_smul_eq_det_mul_of_mul_eq_one _ _ _
      (Matrix.mul_nonsing_inv _ hdet₀),
    Matrix.det_map_add_X_smul_eq_det_mul_of_mul_eq_one M A A⁻¹
      (Matrix.mul_nonsing_inv A hdet)]
  exact (hA.leading_det_X_smul_one_add_inv_mul_interlaces hdet hinv hM).C_mul_both
    hdet₀.ne_zero hdet.ne_zero

end Matrix
