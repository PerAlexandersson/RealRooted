/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/

module

public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.Polynomial.RingDivision
public import Mathlib.Logic.Equiv.Option
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs

/-!
# Divided differences of multivariate polynomials

This file defines the quotient of the antisymmetrization of a multivariate
polynomial under a transposition by the difference of the transposed variables.
-/

@[expose] public noncomputable section

namespace MvPolynomial

variable {σ R : Type*} [CommRing R] [DecidableEq σ]

/-- Regard a multivariate polynomial as a polynomial in the variable `i`, with
coefficients in the polynomial ring on the other variables. -/
def asPolynomial (i : σ) :
    MvPolynomial σ R ≃ₐ[R] Polynomial (MvPolynomial {j : σ // j ≠ i} R) :=
  (renameEquiv R (Equiv.optionSubtypeNe i).symm).trans
    (optionEquivLeft R {j : σ // j ≠ i})

@[simp]
theorem asPolynomial_X_self (i : σ) :
    asPolynomial (R := R) i (X i) = Polynomial.X := by
  simp [asPolynomial]

@[simp]
theorem asPolynomial_X_of_ne (i j : σ) (hji : j ≠ i) :
    asPolynomial (R := R) i (X j) = Polynomial.C (X ⟨j, hji⟩) := by
  rw [asPolynomial, AlgEquiv.trans_apply, renameEquiv_apply, rename_X,
    Equiv.optionSubtypeNe_symm_of_ne hji, optionEquivLeft_X_some]

/-- Identifying the variables `i` and `j` makes a polynomial agree with its
image under the transposition of those variables. -/
theorem eval_asPolynomial_rename_swap (i j : σ) (hij : i ≠ j)
    (P : MvPolynomial σ R) :
    Polynomial.eval (X ⟨j, hij.symm⟩) (asPolynomial (R := R) i P) =
      Polynomial.eval (X ⟨j, hij.symm⟩)
        (asPolynomial (R := R) i (rename (Equiv.swap i j) P)) := by
  let f := (Polynomial.evalRingHom (X ⟨j, hij.symm⟩)).comp
    (asPolynomial (R := R) i).toRingHom
  have hf : f = f.comp (rename (R := R) (Equiv.swap i j)).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [f]
    · intro k
      change Polynomial.eval (X ⟨j, hij.symm⟩)
          (asPolynomial (R := R) i (X k)) =
        Polynomial.eval (X ⟨j, hij.symm⟩)
          (asPolynomial (R := R) i (rename (Equiv.swap i j) (X k)))
      rw [rename_X]
      rcases eq_or_ne k i with rfl | hki
      · rw [asPolynomial_X_self, Equiv.swap_apply_left,
          asPolynomial_X_of_ne k j hij.symm, Polynomial.eval_X,
          Polynomial.eval_C]
      · rcases eq_or_ne k j with rfl | hkj
        · rw [asPolynomial_X_of_ne i k hki, Equiv.swap_apply_right,
            asPolynomial_X_self, Polynomial.eval_C, Polynomial.eval_X]
        · rw [Equiv.swap_apply_of_ne_of_ne hki hkj]
  exact RingHom.congr_fun hf P

/-- The divided difference `(P - swap i j P) / (X i - X j)`, defined by
univariate exact division in the variable `i`. -/
def swapDividedDifference (i j : σ) (hij : i ≠ j) :
    MvPolynomial σ R →ₗ[R] MvPolynomial σ R :=
  let e := asPolynomial (R := R) i
  let a : MvPolynomial {k : σ // k ≠ i} R := X ⟨j, hij.symm⟩
  e.symm.toLinearMap.comp <|
    ((Polynomial.divByMonicHom (Polynomial.X - Polynomial.C a)).restrictScalars R).comp <|
      e.toLinearMap.comp <|
        LinearMap.id - (rename (R := R) (Equiv.swap i j)).toLinearMap

@[simp]
theorem swapDividedDifference_apply (i j : σ) (hij : i ≠ j)
    (P : MvPolynomial σ R) :
    swapDividedDifference i j hij P =
      (asPolynomial (R := R) i).symm
        ((asPolynomial (R := R) i
          (P - rename (Equiv.swap i j) P)) /ₘ
            (Polynomial.X - Polynomial.C (X ⟨j, hij.symm⟩))) := by
  rfl

/-- Multiplying a swap divided difference by its variable difference recovers
the antisymmetrization. -/
theorem X_sub_X_mul_swapDividedDifference (i j : σ) (hij : i ≠ j)
    (P : MvPolynomial σ R) :
    (X i - X j) * swapDividedDifference i j hij P =
      P - rename (Equiv.swap i j) P := by
  apply (asPolynomial (R := R) i).injective
  rw [map_mul, map_sub, asPolynomial_X_self,
    asPolynomial_X_of_ne i j hij.symm, swapDividedDifference_apply,
    AlgEquiv.apply_symm_apply]
  apply Polynomial.mul_divByMonic_eq_iff_isRoot.mpr
  rw [Polynomial.IsRoot.def, map_sub, Polynomial.eval_sub,
    eval_asPolynomial_rename_swap i j hij P, sub_self]

/-- The variable difference `X i - X j` divides the antisymmetrization of
every multivariate polynomial. -/
theorem X_sub_X_dvd_sub_rename_swap (i j : σ) (hij : i ≠ j)
    (P : MvPolynomial σ R) :
    X i - X j ∣ P - rename (Equiv.swap i j) P := by
  refine ⟨swapDividedDifference i j hij P, ?_⟩
  exact (X_sub_X_mul_swapDividedDifference i j hij P).symm

/-- The linear operator `P ↦ X i ^ 2 * ∂ᵢ P`. -/
def squaredPDeriv (i : σ) : MvPolynomial σ R →ₗ[R] MvPolynomial σ R :=
  (LinearMap.mulLeft R (X i ^ 2)).comp (pderiv i).toLinearMap

omit [DecidableEq σ] in
@[simp]
theorem squaredPDeriv_apply (i : σ) (P : MvPolynomial σ R) :
    squaredPDeriv i P = X i ^ 2 * pderiv i P :=
  rfl

/-- One pair summand in the multivariate operator built from the quotients
`(X i ^ 2 * ∂ᵢ P - X j ^ 2 * ∂ⱼ P) / (X i - X j)`. -/
def squaredPDerivDividedDifference (i j : σ) (hij : i ≠ j) :
    MvPolynomial σ R →ₗ[R] MvPolynomial σ R :=
  (swapDividedDifference i j hij).comp (squaredPDeriv i)

/-- On a symmetric polynomial, swapping `i` and `j` sends
`X i ^ 2 * ∂ᵢ P` to `X j ^ 2 * ∂ⱼ P`. -/
theorem rename_swap_squaredPDeriv_of_isSymmetric {P : MvPolynomial σ R}
    (hP : P.IsSymmetric) (i j : σ) :
    rename (Equiv.swap i j) (squaredPDeriv i P) = squaredPDeriv j P := by
  rw [squaredPDeriv_apply, map_mul, map_pow, rename_X,
    Equiv.swap_apply_left, squaredPDeriv_apply]
  rw [← pderiv_rename (R := R) (Equiv.swap i j).injective i P,
    Equiv.swap_apply_left, hP (Equiv.swap i j)]

/-- Exact polynomiality of a pair summand of the squared-partial-derivative
operator on symmetric polynomials. -/
theorem X_sub_X_mul_squaredPDerivDividedDifference_of_isSymmetric
    {P : MvPolynomial σ R} (hP : P.IsSymmetric) (i j : σ) (hij : i ≠ j) :
    (X i - X j) * squaredPDerivDividedDifference i j hij P =
      X i ^ 2 * pderiv i P - X j ^ 2 * pderiv j P := by
  rw [squaredPDerivDividedDifference, LinearMap.comp_apply,
    X_sub_X_mul_swapDividedDifference,
    rename_swap_squaredPDeriv_of_isSymmetric hP, squaredPDeriv_apply i,
    squaredPDeriv_apply j]

end MvPolynomial
