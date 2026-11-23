/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import RealRooted.Mathlib.Algebra.Polynomial.Orthogonal.MomentChristoffel
import RealRooted.Mathlib.Algebra.Polynomial.Orthogonal.MomentHankelFactorization

/-!
# Hankel determinant ratios for orthogonal norms and Stieltjes numerators

The unitriangular Hankel factorization identifies each squared norm with a
quotient of consecutive determinants. Substituting this into the paired
Christoffel ratios gives the classical even and odd Stieltjes numerators.
Invertibility is the algebraic hypothesis; positive definite moment matrices
supply it in applications.
-/

public section

namespace Polynomial

/-- A finite nondegenerate prefix gives the next norm as a determinant quotient.
The numerator determinant and the norm may vanish. -/
theorem momentNormSq_eq_det_div_of_isUnit {K : Type*} [Field K] [DecidableEq K]
    (μ : ℕ → K) (n : ℕ) (hdet : ∀ i ≤ n, IsUnit (momentHankelMatrix μ i).det) :
    momentNormSq μ n = (momentHankelMatrix μ (n + 1)).det /
      (momentHankelMatrix μ n).det := by
  rw [det_momentHankelMatrix_succ_of_isUnit μ n hdet, mul_comm,
    mul_div_cancel_right₀ _ (hdet n le_rfl).ne_zero]

/-- An orthogonal norm is the quotient of consecutive Hankel determinants. -/
theorem momentNormSq_eq_det_div {K : Type*} [Field K] [DecidableEq K]
    (μ : ℕ → K) (hdet : ∀ n, IsUnit (momentHankelMatrix μ n).det) (n : ℕ) :
    momentNormSq μ n = (momentHankelMatrix μ (n + 1)).det /
      (momentHankelMatrix μ n).det :=
  momentNormSq_eq_det_div_of_isUnit μ n (fun i _ => hdet i)

/-- The even numerator uses only finite shifted and unshifted nondegenerate
prefixes. The two next determinants need not be nonzero. -/
theorem momentStieltjesEven_eq_det_ratio_of_isUnit (μ : ℕ → ℝ) (n : ℕ)
    (hdet : ∀ i ≤ n, IsUnit (momentHankelMatrix μ i).det)
    (hshift : ∀ i ≤ n, IsUnit (momentHankelMatrix (fun k => μ (k + 1)) i).det) :
    momentStieltjesEven μ n =
      (momentHankelMatrix (fun k => μ (k + 1)) (n + 1)).det *
        (momentHankelMatrix μ n).det /
      ((momentHankelMatrix (fun k => μ (k + 1)) n).det *
        (momentHankelMatrix μ (n + 1)).det) := by
  rw [momentStieltjesEven, momentNormSq_eq_det_div_of_isUnit _ n hshift,
    momentNormSq_eq_det_div_of_isUnit μ n hdet, div_div_div_eq]

/-- The even Stieltjes numerator is a ratio of shifted and unshifted Hankel determinants. -/
theorem momentStieltjesEven_eq_det_ratio (μ : ℕ → ℝ)
    (hdet : ∀ n, IsUnit (momentHankelMatrix μ n).det)
    (hshift : ∀ n, IsUnit (momentHankelMatrix (fun k => μ (k + 1)) n).det) (n : ℕ) :
    momentStieltjesEven μ n =
      (momentHankelMatrix (fun k => μ (k + 1)) (n + 1)).det *
        (momentHankelMatrix μ n).det /
      ((momentHankelMatrix (fun k => μ (k + 1)) n).det *
        (momentHankelMatrix μ (n + 1)).det) :=
  momentStieltjesEven_eq_det_ratio_of_isUnit μ n (fun i _ => hdet i)
    (fun i _ => hshift i)

/-- The odd numerator also admits a finite-prefix determinant formula. No
nonvanishing condition is imposed on either next determinant. -/
theorem momentStieltjesOdd_eq_det_ratio_of_isUnit (μ : ℕ → ℝ) (n : ℕ)
    (hdet : ∀ i ≤ n + 1, IsUnit (momentHankelMatrix μ i).det)
    (hshift : ∀ i ≤ n, IsUnit (momentHankelMatrix (fun k => μ (k + 1)) i).det) :
    momentStieltjesOdd μ n =
      (momentHankelMatrix μ (n + 2)).det *
        (momentHankelMatrix (fun k => μ (k + 1)) n).det /
      ((momentHankelMatrix μ (n + 1)).det *
        (momentHankelMatrix (fun k => μ (k + 1)) (n + 1)).det) := by
  rw [momentStieltjesOdd, momentNormSq_eq_det_div_of_isUnit μ (n + 1) hdet,
    momentNormSq_eq_det_div_of_isUnit _ n hshift, div_div_div_eq]

/-- The odd Stieltjes numerator uses the next unshifted Hankel determinant. -/
theorem momentStieltjesOdd_eq_det_ratio (μ : ℕ → ℝ)
    (hdet : ∀ n, IsUnit (momentHankelMatrix μ n).det)
    (hshift : ∀ n, IsUnit (momentHankelMatrix (fun k => μ (k + 1)) n).det) (n : ℕ) :
    momentStieltjesOdd μ n =
      (momentHankelMatrix μ (n + 2)).det *
        (momentHankelMatrix (fun k => μ (k + 1)) n).det /
      ((momentHankelMatrix μ (n + 1)).det *
        (momentHankelMatrix (fun k => μ (k + 1)) (n + 1)).det) :=
  momentStieltjesOdd_eq_det_ratio_of_isUnit μ n (fun i _ => hdet i)
    (fun i _ => hshift i)

end Polynomial
