module

public import Mathlib.LinearAlgebra.Matrix.Block

/-! # Leading sections of block lower triangular matrices

Leading sections commute with products and inverses under triangularity.
-/

public section

namespace Matrix

variable {R : Type*}

/-- The leading section of a product is the product of the leading sections
when every omitted summand vanishes. -/
theorem leading_submatrix_mul_of_last_product_eq_zero [NonUnitalNonAssocSemiring R]
    {n : ℕ} (A B : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (hzero : ∀ i j : Fin n, A i.castSucc (Fin.last n) *
      B (Fin.last n) j.castSucc = 0) :
    (A * B).submatrix Fin.castSucc Fin.castSucc =
      A.submatrix Fin.castSucc Fin.castSucc *
        B.submatrix Fin.castSucc Fin.castSucc := by
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  rw [Fin.sum_univ_castSucc]
  simp [hzero]

/-- A zero upper-right block allows a leading section to commute with
multiplication on the right by an arbitrary matrix. -/
theorem leading_submatrix_mul_of_upperRight_eq_zero [NonUnitalNonAssocSemiring R]
    {n : ℕ} (A B : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (hzero : ∀ i : Fin n, A i.castSucc (Fin.last n) = 0) :
    (A * B).submatrix Fin.castSucc Fin.castSucc =
      A.submatrix Fin.castSucc Fin.castSucc *
        B.submatrix Fin.castSucc Fin.castSucc := by
  apply leading_submatrix_mul_of_last_product_eq_zero
  intro i j
  rw [hzero i, zero_mul]

/-- Inversion commutes with removing the last row and column of an invertible
matrix whose upper-right block is zero. -/
theorem leading_submatrix_inv_of_upperRight_eq_zero [CommRing R]
    {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (hdet : IsUnit A.det)
    (hzero : ∀ i : Fin n, A i.castSucc (Fin.last n) = 0) :
    (A.submatrix Fin.castSucc Fin.castSucc)⁻¹ =
      A⁻¹.submatrix Fin.castSucc Fin.castSucc := by
  apply Matrix.inv_eq_right_inv
  rw [← leading_submatrix_mul_of_upperRight_eq_zero A A⁻¹ hzero,
    Matrix.mul_nonsing_inv A hdet,
    Matrix.submatrix_one Fin.castSucc (Fin.castSucc_injective n)]

/-- The leading section of a product with a lower triangular left factor is
obtained by multiplying the leading sections. -/
theorem IsLowerTriangular.leading_submatrix_mul [NonUnitalNonAssocSemiring R]
    {n : ℕ} {A : Matrix (Fin (n + 1)) (Fin (n + 1)) R}
    (hA : A.IsLowerTriangular) (B : Matrix (Fin (n + 1)) (Fin (n + 1)) R) :
    (A * B).submatrix Fin.castSucc Fin.castSucc =
      A.submatrix Fin.castSucc Fin.castSucc *
        B.submatrix Fin.castSucc Fin.castSucc := by
  apply leading_submatrix_mul_of_upperRight_eq_zero
  intro i
  exact hA i.castSucc_lt_last

/-- Leading sections of the inverse of an invertible lower triangular matrix
are inverses of its leading sections. -/
theorem IsLowerTriangular.leading_submatrix_inv [CommRing R]
    {n : ℕ} {A : Matrix (Fin (n + 1)) (Fin (n + 1)) R}
    (hA : A.IsLowerTriangular) (hdet : IsUnit A.det) :
    (A.submatrix Fin.castSucc Fin.castSucc)⁻¹ =
      A⁻¹.submatrix Fin.castSucc Fin.castSucc := by
  apply leading_submatrix_inv_of_upperRight_eq_zero A hdet
  intro i
  exact hA i.castSucc_lt_last

/-- Left multiplication by the inverse of a lower triangular matrix commutes
with taking leading sections. -/
theorem IsLowerTriangular.leading_submatrix_inv_mul [CommRing R]
    {n : ℕ} {A : Matrix (Fin (n + 1)) (Fin (n + 1)) R}
    (hA : A.IsLowerTriangular) (hdet : IsUnit A.det)
    (B : Matrix (Fin (n + 1)) (Fin (n + 1)) R) :
    (A⁻¹ * B).submatrix Fin.castSucc Fin.castSucc =
      (A.submatrix Fin.castSucc Fin.castSucc)⁻¹ *
        B.submatrix Fin.castSucc Fin.castSucc := by
  let : Invertible A := A.invertibleOfIsUnitDet hdet
  have hinv : A⁻¹.IsLowerTriangular :=
    Matrix.blockTriangular_inv_of_blockTriangular hA
  rw [hinv.leading_submatrix_mul, ← hA.leading_submatrix_inv hdet]

/-- The leading section of an invertible lower triangular matrix has unit
determinant. -/
theorem IsLowerTriangular.isUnit_det_leading_submatrix
    {R : Type*} [CommRing R]
    {m : ℕ} {A : Matrix (Fin (m + 1)) (Fin (m + 1)) R}
    (hA : A.IsLowerTriangular) (hdet : IsUnit A.det) :
    IsUnit (A.submatrix Fin.castSucc Fin.castSucc).det := by
  apply Matrix.isUnit_det_of_right_inverse
    (B := A⁻¹.submatrix Fin.castSucc Fin.castSucc)
  rw [← hA.leading_submatrix_mul A⁻¹, Matrix.mul_nonsing_inv A hdet,
    Matrix.submatrix_one Fin.castSucc (Fin.castSucc_injective m)]


end Matrix
