/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import RealRooted.Mathlib.Algebra.Polynomial.Orthogonal.MomentAlgebra
public import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Hankel factorization by monic orthogonal coefficients

The lower unitriangular matrix of the monic orthogonal polynomial
coefficients diagonalizes the finite Hankel moment matrix. Its diagonal
entries are the squared norms. Taking determinants gives the norm-product
formula, and therefore the determinant ratio for each successive norm.
-/

public section

open Matrix
open scoped BigOperators

namespace Polynomial

variable {R : Type*} [CommRing R] [Nontrivial R] [DecidableEq R]

/-- Lower unitriangular coefficient matrix of the first monic moment polynomials. -/
@[expose] noncomputable def momentOrthogonalMatrix (μ : ℕ → R) (n : ℕ) :
    Matrix (Fin n) (Fin n) R :=
  fun i j => (monicMomentPolynomial μ i.val).coeff j.val

/-- Monicity places one on the diagonal of the orthogonal coefficient matrix. -/
@[simp] theorem momentOrthogonalMatrix_diag (μ : ℕ → R) (n : ℕ) (i : Fin n) :
    momentOrthogonalMatrix μ n i i = 1 := by
  change (monicMomentPolynomial μ i.val).coeff i.val = 1
  simpa only [(isMonicOfDegree_monicMomentPolynomial μ i.val).natDegree_eq] using
    (isMonicOfDegree_monicMomentPolynomial μ i.val).monic.coeff_natDegree

/-- The degree bound makes the orthogonal coefficient matrix lower triangular. -/
theorem isLowerTriangular_momentOrthogonalMatrix (μ : ℕ → R) (n : ℕ) :
    (momentOrthogonalMatrix μ n).IsLowerTriangular := by
  intro i j hij
  apply coeff_eq_zero_of_natDegree_lt
  rw [(isMonicOfDegree_monicMomentPolynomial μ i.val).natDegree_eq]
  exact hij

/-- The change of basis to monic orthogonal coefficients has determinant one. -/
@[simp] theorem det_momentOrthogonalMatrix (μ : ℕ → R) (n : ℕ) :
    (momentOrthogonalMatrix μ n).det = 1 := by
  rw [Matrix.det_of_isLowerTriangular _ (isLowerTriangular_momentOrthogonalMatrix μ n)]
  simp

/-- Orthogonality of two monic moment polynomials needs only their defining
Hankel matrices to be invertible. -/
theorem momentPairing_monicMomentPolynomial_eq_ite_of_isUnit (μ : ℕ → R)
    (i j : ℕ) (hi : IsUnit (momentHankelMatrix μ i).det)
    (hj : IsUnit (momentHankelMatrix μ j).det) :
    momentPairing μ (monicMomentPolynomial μ i) (monicMomentPolynomial μ j) =
      if i = j then momentNormSq μ i else 0 := by
  by_cases hij : i = j
  · subst j
    simp only [ite_true, momentNormSq]
  · rw [ite_eq_right hij]
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · apply momentPairing_monicMomentPolynomial μ j hj
      apply lt_of_le_of_lt degree_le_natDegree
      rw [(isMonicOfDegree_monicMomentPolynomial μ i).natDegree_eq]
      exact_mod_cast hlt
    · rw [momentPairing_comm]
      apply momentPairing_monicMomentPolynomial μ i hi
      apply lt_of_le_of_lt degree_le_natDegree
      rw [(isMonicOfDegree_monicMomentPolynomial μ j).natDegree_eq]
      exact_mod_cast hgt

/-- Orthogonality diagonalizes the pairings between monic moment polynomials. -/
theorem momentPairing_monicMomentPolynomial_eq_ite (μ : ℕ → R)
    (hdet : ∀ n, IsUnit (momentHankelMatrix μ n).det) (i j : ℕ) :
    momentPairing μ (monicMomentPolynomial μ i) (monicMomentPolynomial μ j) =
      if i = j then momentNormSq μ i else 0 :=
  momentPairing_monicMomentPolynomial_eq_ite_of_isUnit μ i j (hdet i) (hdet j)

/-- Each coefficient row reconstructs its monic orthogonal polynomial. -/
private theorem ofFn_momentOrthogonalMatrix_row (μ : ℕ → R) (n : ℕ) (i : Fin n) :
    ofFn n (momentOrthogonalMatrix μ n i) = monicMomentPolynomial μ i.val := by
  change ofFn n (toFn n (monicMomentPolynomial μ i.val)) = _
  apply ofFn_comp_toFn_eq_id_of_natDegree_lt
  rw [(isMonicOfDegree_monicMomentPolynomial μ i.val).natDegree_eq]
  exact i.is_lt

/-- A finite nondegenerate prefix suffices to diagonalize the next Hankel matrix.
The matrix being diagonalized may itself be singular. -/
theorem momentOrthogonalMatrix_mul_hankel_mul_transpose_of_isUnit (μ : ℕ → R)
    (n : ℕ) (hdet : ∀ i < n, IsUnit (momentHankelMatrix μ i).det) :
    momentOrthogonalMatrix μ n * momentHankelMatrix μ n *
        (momentOrthogonalMatrix μ n)ᵀ =
      Matrix.diagonal (fun i : Fin n => momentNormSq μ i.val) := by
  ext i j
  have hpair :
      (momentOrthogonalMatrix μ n * momentHankelMatrix μ n *
        (momentOrthogonalMatrix μ n)ᵀ) i j =
      momentPairing μ (monicMomentPolynomial μ i.val)
        (monicMomentPolynomial μ j.val) := by
    rw [← ofFn_momentOrthogonalMatrix_row μ n i,
      ← ofFn_momentOrthogonalMatrix_row μ n j, momentPairing_ofFn_ofFn,
      Matrix.dotProduct_mulVec]
    rfl
  rw [hpair, momentPairing_monicMomentPolynomial_eq_ite_of_isUnit μ i.val j.val
    (hdet i.val i.is_lt) (hdet j.val j.is_lt)]
  by_cases hij : i = j
  · subst j
    simp
  · have hv : i.val ≠ j.val := fun h => hij (Fin.ext h)
    simp [hij, hv]

/-- The coefficient change of basis diagonalizes each finite Hankel matrix. -/
theorem momentOrthogonalMatrix_mul_hankel_mul_transpose (μ : ℕ → R)
    (hdet : ∀ n, IsUnit (momentHankelMatrix μ n).det) (n : ℕ) :
    momentOrthogonalMatrix μ n * momentHankelMatrix μ n *
        (momentOrthogonalMatrix μ n)ᵀ =
      Matrix.diagonal (fun i : Fin n => momentNormSq μ i.val) :=
  momentOrthogonalMatrix_mul_hankel_mul_transpose_of_isUnit μ n (fun i _ => hdet i)

/-- A finite Hankel determinant is the product of the squared norms of the
preceding monic moment polynomials, assuming only the preceding determinants
are units. The determinant in the conclusion may vanish. -/
theorem det_momentHankelMatrix_eq_prod_norm_of_isUnit (μ : ℕ → R)
    (n : ℕ) (hdet : ∀ i < n, IsUnit (momentHankelMatrix μ i).det) :
    (momentHankelMatrix μ n).det = ∏ i : Fin n, momentNormSq μ i.val := by
  have h := congrArg Matrix.det
    (momentOrthogonalMatrix_mul_hankel_mul_transpose_of_isUnit μ n hdet)
  simpa only [Matrix.det_mul, Matrix.det_transpose, det_momentOrthogonalMatrix,
    one_mul, mul_one, Matrix.det_diagonal] using h

/-- A finite Hankel determinant is the product of the squared norms of the
preceding monic moment polynomials. -/
theorem det_momentHankelMatrix_eq_prod_norm (μ : ℕ → R)
    (hdet : ∀ n, IsUnit (momentHankelMatrix μ n).det) (n : ℕ) :
    (momentHankelMatrix μ n).det = ∏ i : Fin n, momentNormSq μ i.val :=
  det_momentHankelMatrix_eq_prod_norm_of_isUnit μ n (fun i _ => hdet i)

/-- Consecutive Hankel determinants differ by the next squared norm, including
the first vanishing norm after a nondegenerate prefix. -/
theorem det_momentHankelMatrix_succ_of_isUnit (μ : ℕ → R)
    (n : ℕ) (hdet : ∀ i ≤ n, IsUnit (momentHankelMatrix μ i).det) :
    (momentHankelMatrix μ (n + 1)).det =
      (momentHankelMatrix μ n).det * momentNormSq μ n := by
  rw [det_momentHankelMatrix_eq_prod_norm_of_isUnit μ (n + 1)
      (fun i hi => hdet i (by lia)), Fin.prod_univ_castSucc,
    det_momentHankelMatrix_eq_prod_norm_of_isUnit μ n
      (fun i hi => hdet i (by lia))]
  rfl

/-- Consecutive Hankel determinants differ by the next squared norm. -/
theorem det_momentHankelMatrix_succ (μ : ℕ → R)
    (hdet : ∀ n, IsUnit (momentHankelMatrix μ n).det) (n : ℕ) :
    (momentHankelMatrix μ (n + 1)).det =
      (momentHankelMatrix μ n).det * momentNormSq μ n :=
  det_momentHankelMatrix_succ_of_isUnit μ n (fun i _ => hdet i)

end Polynomial
