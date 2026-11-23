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

/-- An orthogonal norm is the quotient of consecutive Hankel determinants. -/
theorem momentNormSq_eq_det_div {K : Type*} [Field K] [DecidableEq K]
    (μ : ℕ → K) (hdet : ∀ n, IsUnit (momentHankelMatrix μ n).det) (n : ℕ) :
    momentNormSq μ n = (momentHankelMatrix μ (n + 1)).det /
      (momentHankelMatrix μ n).det := by
  rw [det_momentHankelMatrix_succ μ hdet n, mul_comm,
    mul_div_cancel_right₀ _ (hdet n).ne_zero]

/-- The even Stieltjes numerator is a ratio of shifted and unshifted Hankel determinants. -/
theorem momentStieltjesEven_eq_det_ratio (μ : ℕ → ℝ)
    (hdet : ∀ n, IsUnit (momentHankelMatrix μ n).det)
    (hshift : ∀ n, IsUnit (momentHankelMatrix (fun k => μ (k + 1)) n).det) (n : ℕ) :
    momentStieltjesEven μ n =
      (momentHankelMatrix (fun k => μ (k + 1)) (n + 1)).det *
        (momentHankelMatrix μ n).det /
      ((momentHankelMatrix (fun k => μ (k + 1)) n).det *
        (momentHankelMatrix μ (n + 1)).det) := by
  rw [momentStieltjesEven, momentNormSq_eq_det_div _ hshift n,
    momentNormSq_eq_det_div μ hdet n]
  field_simp [(hdet n).ne_zero, (hdet (n + 1)).ne_zero, (hshift n).ne_zero]

/-- The odd Stieltjes numerator uses the next unshifted Hankel determinant. -/
theorem momentStieltjesOdd_eq_det_ratio (μ : ℕ → ℝ)
    (hdet : ∀ n, IsUnit (momentHankelMatrix μ n).det)
    (hshift : ∀ n, IsUnit (momentHankelMatrix (fun k => μ (k + 1)) n).det) (n : ℕ) :
    momentStieltjesOdd μ n =
      (momentHankelMatrix μ (n + 2)).det *
        (momentHankelMatrix (fun k => μ (k + 1)) n).det /
      ((momentHankelMatrix μ (n + 1)).det *
        (momentHankelMatrix (fun k => μ (k + 1)) (n + 1)).det) := by
  rw [momentStieltjesOdd, momentNormSq_eq_det_div μ hdet (n + 1),
    momentNormSq_eq_det_div _ hshift n]
  field_simp [(hdet (n + 1)).ne_zero, (hshift n).ne_zero, (hshift (n + 1)).ne_zero]

end Polynomial
