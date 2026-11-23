/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import RealRooted.Mathlib.Algebra.Polynomial.MomentTranslation
public import RealRooted.Mathlib.Algebra.Polynomial.Orthogonal.Moment
public import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Translation of Hankel matrices and monic orthogonal polynomials

The coefficient matrix of translated monomials is lower triangular with
diagonal one. Its Gram identity preserves every finite Hankel determinant.
For a nondegenerate moment system, the monic orthogonal polynomial therefore
translates with the opposite sign. Degree zero is included.
-/

public section

open Matrix

namespace Polynomial

variable {R : Type*} [CommRing R] [Nontrivial R]

/-- Rows of coefficients of the translated monomial basis below degree `n`. -/
@[expose] noncomputable def momentTranslationMatrix (c : R) (n : ℕ) :
    Matrix (Fin n) (Fin n) R :=
  fun i j => (taylor c (X ^ i.val)).coeff j.val

/-- Translation of a monomial preserves its leading coefficient. -/
@[simp] theorem momentTranslationMatrix_diag (c : R) (n : ℕ) (i : Fin n) :
    momentTranslationMatrix c n i i = 1 := by
  change (taylor c ((X : R[X]) ^ i.val)).coeff i.val = 1
  simpa using coeff_taylor_natDegree c ((X : R[X]) ^ i.val)

/-- The translated monomial coefficient matrix is lower triangular. -/
theorem isLowerTriangular_momentTranslationMatrix (c : R) (n : ℕ) :
    (momentTranslationMatrix c n).IsLowerTriangular := by
  intro i j hij
  apply coeff_eq_zero_of_natDegree_lt
  rw [natDegree_taylor, natDegree_X_pow]
  exact hij

/-- Translation is a change of basis with determinant one. -/
@[simp] theorem det_momentTranslationMatrix (c : R) (n : ℕ) :
    (momentTranslationMatrix c n).det = 1 := by
  rw [Matrix.det_of_isLowerTriangular _ (isLowerTriangular_momentTranslationMatrix c n)]
  simp

/-- A coefficient row recovers the corresponding translated monomial. -/
private theorem ofFn_momentTranslationMatrix_row [DecidableEq R]
    (c : R) (n : ℕ) (i : Fin n) :
    ofFn n (momentTranslationMatrix c n i) = taylor c (X ^ i.val) := by
  change ofFn n (toFn n (taylor c ((X : R[X]) ^ i.val))) = _
  apply ofFn_comp_toFn_eq_id_of_natDegree_lt
  simpa only [natDegree_taylor, natDegree_X_pow] using i.is_lt

/-- The Hankel matrix of translated moments is the corresponding Gram congruence. -/
theorem momentTranslationMatrix_mul_hankel_mul_transpose
    (c : R) (m : ℕ → R) (n : ℕ) :
    momentTranslationMatrix c n * momentHankelMatrix m n *
        (momentTranslationMatrix c n)ᵀ =
      momentHankelMatrix (momentTranslate c m) n := by
  classical
  ext i j
  have hpair :
      (momentTranslationMatrix c n * momentHankelMatrix m n *
        (momentTranslationMatrix c n)ᵀ) i j =
      momentPairing m (taylor c (X ^ i.val)) (taylor c (X ^ j.val)) := by
    rw [← ofFn_momentTranslationMatrix_row c n i,
      ← ofFn_momentTranslationMatrix_row c n j, momentPairing_ofFn_ofFn,
      Matrix.dotProduct_mulVec]
    rfl
  rw [hpair, ← momentPairing_momentTranslate]
  change momentFunctional (momentTranslate c m) (X ^ i.val * X ^ j.val) = _
  rw [← pow_add, momentFunctional_X_pow]
  rfl

/-- Every finite Hankel determinant is invariant under moment translation. -/
@[simp] theorem det_momentHankelMatrix_momentTranslate (c : R) (m : ℕ → R) (n : ℕ) :
    (momentHankelMatrix (momentTranslate c m) n).det =
      (momentHankelMatrix m n).det := by
  have h := congrArg Matrix.det
    (momentTranslationMatrix_mul_hankel_mul_transpose c m n)
  simpa only [Matrix.det_mul, Matrix.det_transpose, det_momentTranslationMatrix,
    one_mul, mul_one] using h.symm

variable [DecidableEq R]

/-- For a nondegenerate moment system, the monic orthogonal polynomial
translates by the negative of the moment translation parameter. -/
theorem monicMomentPolynomial_momentTranslate (c : R) (m : ℕ → R) (n : ℕ)
    (hdet : IsUnit (momentHankelMatrix m n).det) :
    monicMomentPolynomial (momentTranslate c m) n =
      taylor (-c) (monicMomentPolynomial m n) := by
  have hdet' : IsUnit (momentHankelMatrix (momentTranslate c m) n).det := by
    simpa only [det_momentHankelMatrix_momentTranslate] using hdet
  have hp := isMonicOfDegree_monicMomentPolynomial m n
  symm
  apply eq_monicMomentPolynomial (momentTranslate c m) hdet'
  · refine ⟨?_, ?_⟩
    · simpa only [natDegree_taylor] using hp.natDegree_eq
    · simpa only [Monic, leadingCoeff_taylor] using hp.monic
  · intro i
    rw [momentPairing_momentTranslate, taylor_taylor, add_neg_cancel, taylor_zero]
    apply momentPairing_monicMomentPolynomial m n hdet
    rw [degree_taylor, degree_X_pow]
    exact WithBot.coe_lt_coe.mpr i.is_lt

/-- The squared norm of the monic orthogonal polynomial is unchanged by translation. -/
theorem momentPairing_monicMomentPolynomial_momentTranslate
    (c : R) (m : ℕ → R) (n : ℕ)
    (hdet : IsUnit (momentHankelMatrix m n).det) :
    momentPairing (momentTranslate c m)
        (monicMomentPolynomial (momentTranslate c m) n)
        (monicMomentPolynomial (momentTranslate c m) n) =
      momentPairing m (monicMomentPolynomial m n) (monicMomentPolynomial m n) := by
  rw [monicMomentPolynomial_momentTranslate c m n hdet, momentPairing_momentTranslate]
  simp only [taylor_taylor, add_neg_cancel, taylor_zero]

end Polynomial
