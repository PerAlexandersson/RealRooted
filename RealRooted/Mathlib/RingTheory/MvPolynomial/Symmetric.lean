import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs

/-!
# Finite-variable symmetrization

This file defines permutation summation and normalized symmetrization for
multivariate polynomials. These are the algebraic operators used in the
Grace--Walsh--Szegő symmetrization argument.
-/

open BigOperators

namespace MvPolynomial

/-- Sum all variable permutations of a multivariate polynomial. -/
noncomputable def symmetrizationSum
    {σ R : Type*} [Fintype σ] [CommSemiring R]
    (p : MvPolynomial σ R) : MvPolynomial σ R := by
  classical
  exact ∑ e : Equiv.Perm σ, rename e p

/-- The permutation sum is symmetric. -/
theorem isSymmetric_symmetrizationSum
    {σ R : Type*} [Fintype σ] [CommSemiring R]
    (p : MvPolynomial σ R) :
    IsSymmetric (symmetrizationSum p) := by
  classical
  intro e
  simp only [symmetrizationSum, map_sum, rename_rename]
  simpa [Function.comp_def] using
    Equiv.sum_comp (Equiv.mulLeft e)
      (fun f : Equiv.Perm σ => rename f p)

/-- Average all variable permutations of a complex multivariate polynomial. -/
noncomputable def fullSymmetrization
    {σ : Type*} [Fintype σ] (p : MvPolynomial σ ℂ) :
    MvPolynomial σ ℂ := by
  classical
  exact C (Fintype.card (Equiv.Perm σ) : ℂ)⁻¹ *
    symmetrizationSum p

/-- Full symmetrization is symmetric. -/
theorem isSymmetric_fullSymmetrization
    {σ : Type*} [Fintype σ] (p : MvPolynomial σ ℂ) :
    IsSymmetric (fullSymmetrization p) := by
  classical
  intro e
  simp only [fullSymmetrization, map_mul, rename_C]
  rw [isSymmetric_symmetrizationSum p e]

/-- Full symmetrization preserves evaluation at a constant assignment. -/
theorem eval_const_fullSymmetrization
    {σ : Type*} [Fintype σ] (p : MvPolynomial σ ℂ) (w : ℂ) :
    eval (fun _ : σ => w) (fullSymmetrization p) =
      eval (fun _ : σ => w) p := by
  classical
  have hcard : (Fintype.card (Equiv.Perm σ) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hconst (e : Equiv.Perm σ) :
      (fun _ : σ => w) ∘ e = fun _ : σ => w := by
    rfl
  simp only [fullSymmetrization, map_mul, eval_C,
    symmetrizationSum, map_sum, eval_rename, hconst]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← mul_assoc, inv_mul_cancel₀ hcard, one_mul]

end MvPolynomial
