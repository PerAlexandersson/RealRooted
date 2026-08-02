import RealRooted.Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Cauchy-Binet determinant expansions

This file develops the rectangular Cauchy-Binet formula. The first theorem
expands a selected minor of a rectangular product into the Leibniz sum over
permutations and all intermediate-index maps. The remaining Cauchy-Binet step
groups the injective maps by their ordered image and proves that noninjective
terms cancel.
-/

open scoped BigOperators

namespace Matrix

/-- Leibniz expansion of a selected minor of a rectangular matrix product. -/
theorem det_submatrix_mul_eq_sum_perm_fun
    {R : Type*} [CommRing R] {l n m q : ℕ}
    (L : Matrix (Fin l) (Fin n) R)
    (A : Matrix (Fin n) (Fin m) R)
    (rows : Fin q → Fin l) (cols : Fin q → Fin m) :
    ((L * A).submatrix rows cols).det =
      ∑ σ : Equiv.Perm (Fin q), Equiv.Perm.sign σ •
        ∑ f : Fin q → Fin n,
          ∏ i, L (rows (σ i)) (f i) * A (f i) (cols i) := by
  rw [Matrix.det_apply]
  simp only [Matrix.submatrix_apply, Matrix.mul_apply, Finset.prod_univ_sum]
  simp

/-- Reassemble the permutation sum for each intermediate-index map. -/
theorem det_submatrix_mul_eq_sum_fun_det
    {R : Type*} [CommRing R] {l n m q : ℕ}
    (L : Matrix (Fin l) (Fin n) R)
    (A : Matrix (Fin n) (Fin m) R)
    (rows : Fin q → Fin l) (cols : Fin q → Fin m) :
    ((L * A).submatrix rows cols).det =
      ∑ f : Fin q → Fin n,
        (L.submatrix rows f).det * ∏ i, A (f i) (cols i) := by
  rw [det_submatrix_mul_eq_sum_perm_fun]
  simp_rw [Finset.smul_sum]
  rw [Finset.sum_comm]
  apply Fintype.sum_congr
  intro f
  rw [Matrix.det_apply]
  simp only [Matrix.submatrix_apply, Finset.prod_mul_distrib]
  rw [Finset.sum_mul]
  simp_rw [smul_mul_assoc]

end Matrix
