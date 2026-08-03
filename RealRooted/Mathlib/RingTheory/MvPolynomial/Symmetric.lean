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
theorem symmetrizationSum_isSymmetric
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
    {σ R : Type*} [Fintype σ] [Field R] [CharZero R]
    (p : MvPolynomial σ R) : MvPolynomial σ R := by
  classical
  exact C (Fintype.card (Equiv.Perm σ) : R)⁻¹ *
    symmetrizationSum p

/-- Full symmetrization is symmetric. -/
theorem fullSymmetrization_isSymmetric
    {σ R : Type*} [Fintype σ] [Field R] [CharZero R]
    (p : MvPolynomial σ R) :
    IsSymmetric (fullSymmetrization p) := by
  classical
  intro e
  simp only [fullSymmetrization, map_mul, rename_C]
  rw [symmetrizationSum_isSymmetric p e]

/-- Full symmetrization preserves evaluation at a constant assignment. -/
theorem eval_fullSymmetrization_const
    {σ R : Type*} [Fintype σ] [Field R] [CharZero R]
    (p : MvPolynomial σ R) (w : R) :
    eval (fun _ : σ => w) (fullSymmetrization p) =
      eval (fun _ : σ => w) p := by
  classical
  have hcard : (Fintype.card (Equiv.Perm σ) : R) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hconst (e : Equiv.Perm σ) :
      (fun _ : σ => w) ∘ e = fun _ : σ => w := by
    rfl
  simp only [fullSymmetrization, map_mul, eval_C,
    symmetrizationSum, map_sum, eval_rename, hconst]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← mul_assoc, inv_mul_cancel₀ hcard, one_mul]

end MvPolynomial

namespace MvPolynomial

/-- Convex-form partial symmetrization associated with a permutation. -/
noncomputable def partialSymmetrization
    {σ R : Type*} [CommRing R]
    (t : R) (e : Equiv.Perm σ) (p : MvPolynomial σ R) :
    MvPolynomial σ R :=
  C t * p + C (1 - t) * rename e p

/-- At weight zero, partial symmetrization is variable permutation. -/
@[simp] theorem partialSymmetrization_zero
    {σ R : Type*} [CommRing R]
    (e : Equiv.Perm σ) (p : MvPolynomial σ R) :
    partialSymmetrization 0 e p = rename e p := by
  simp [partialSymmetrization]

/-- At weight one, partial symmetrization is the original polynomial. -/
@[simp] theorem partialSymmetrization_one
    {σ R : Type*} [CommRing R]
    (e : Equiv.Perm σ) (p : MvPolynomial σ R) :
    partialSymmetrization 1 e p = p := by
  simp [partialSymmetrization]

/-- Partial symmetrization preserves evaluation at a constant assignment. -/
theorem eval_partialSymmetrization_const
    {σ R : Type*} [CommRing R]
    (t w : R) (e : Equiv.Perm σ) (p : MvPolynomial σ R) :
    eval (fun _ : σ => w) (partialSymmetrization t e p) =
      eval (fun _ : σ => w) p := by
  have hconst : (fun _ : σ => w) ∘ e = fun _ : σ => w := by
    rfl
  simp only [partialSymmetrization, map_add, map_mul, eval_C,
    eval_rename, hconst]
  ring

end MvPolynomial
