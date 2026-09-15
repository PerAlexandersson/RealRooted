import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Polynomial.Derivative
import RealRooted.Mathlib.RingTheory.MvPolynomial.EulerIdentity

/-!
# Diagonal restriction of a multivariate polynomial

This file defines the univariate restriction obtained by identifying every
multivariate coordinate with `X`.  It proves the finite-variable chain rule
and the corresponding diagonal formula for the Euler operator.
-/

namespace MvPolynomial

open Polynomial
open scoped BigOperators

noncomputable section

/-- Identify every variable of a multivariate polynomial with the univariate
variable `X`. -/
def diagonal {R σ : Type*} [CommSemiring R]
    (P : MvPolynomial σ R) : Polynomial R :=
  MvPolynomial.eval₂Hom Polynomial.C (fun _ => Polynomial.X) P

@[simp] theorem diagonal_C {R σ : Type*} [CommSemiring R] (a : R) :
    diagonal (MvPolynomial.C a : MvPolynomial σ R) = Polynomial.C a := by
  simp [diagonal]

@[simp] theorem diagonal_X {R σ : Type*} [CommSemiring R] (i : σ) :
    diagonal (MvPolynomial.X i : MvPolynomial σ R) = Polynomial.X := by
  simp [diagonal]

@[simp] theorem diagonal_add {R σ : Type*} [CommSemiring R]
    (P Q : MvPolynomial σ R) :
    diagonal (P + Q) = diagonal P + diagonal Q := by
  simp [diagonal]

@[simp] theorem diagonal_mul {R σ : Type*} [CommSemiring R]
    (P Q : MvPolynomial σ R) :
    diagonal (P * Q) = diagonal P * diagonal Q := by
  simp [diagonal]

@[simp] theorem diagonal_sum {R σ ι : Type*} [CommSemiring R]
    [Fintype ι] (P : ι → MvPolynomial σ R) :
    diagonal (∑ i, P i) = ∑ i, diagonal (P i) := by
  simp [diagonal]

@[simp] theorem diagonal_sub {R σ : Type*} [CommRing R]
    (P Q : MvPolynomial σ R) :
    diagonal (P - Q) = diagonal P - diagonal Q := by
  simp [diagonal]

@[simp] theorem diagonal_zero {R σ : Type*} [CommSemiring R] :
    diagonal (0 : MvPolynomial σ R) = 0 := by
  simp [diagonal]

@[simp] theorem diagonal_one {R σ : Type*} [CommSemiring R] :
    diagonal (1 : MvPolynomial σ R) = 1 := by
  simp [diagonal]

/-- Diagonal restriction commutes with a coefficient-ring homomorphism. -/
@[simp] theorem diagonal_map {R S σ : Type*} [CommSemiring R]
    [CommSemiring S] (f : R →+* S) (P : MvPolynomial σ R) :
    diagonal (MvPolynomial.map f P) = Polynomial.map f (diagonal P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add P Q hP hQ => simp [hP, hQ]
  | mul_X P i hP => simp [hP]

/-- Evaluating the diagonal restriction at `x` is the same as evaluating the
multivariate polynomial with every coordinate equal to `x`. -/
@[simp] theorem eval_diagonal {R σ : Type*} [CommSemiring R]
    (P : MvPolynomial σ R) (x : R) :
    (diagonal P).eval x = MvPolynomial.eval (fun _ : σ => x) P := by
  unfold diagonal
  change Polynomial.evalRingHom x
      (MvPolynomial.eval₂Hom Polynomial.C
        (fun _ : σ => Polynomial.X) P) = _
  rw [MvPolynomial.map_eval₂Hom]
  simp only [Polynomial.coe_evalRingHom, Polynomial.eval_X]
  have hC : (Polynomial.evalRingHom x).comp Polynomial.C =
      RingHom.id R := by
    ext r
    simp
  rw [hC]
  rfl

/-- Diagonal restriction is unchanged by any variable renaming. -/
@[simp] theorem diagonal_rename {R σ τ : Type*} [CommSemiring R]
    (f : σ → τ) (P : MvPolynomial σ R) :
    diagonal (MvPolynomial.rename f P) = diagonal P := by
  unfold diagonal
  rw [MvPolynomial.eval₂Hom_rename]
  apply MvPolynomial.eval₂Hom_congr rfl
  · funext i
    rfl
  · rfl

/-- On a finite coordinate type, differentiating the diagonal restriction is
the sum of the diagonal restrictions of all partial derivatives. -/
theorem derivative_diagonal {R σ : Type*} [CommSemiring R]
    [Fintype σ] (P : MvPolynomial σ R) :
    (diagonal P).derivative =
      ∑ i : σ, diagonal (MvPolynomial.pderiv i P) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add P Q hP hQ => simp [hP, hQ, Finset.sum_add_distrib]
  | mul_X P i hP =>
      rw [diagonal_mul, diagonal_X, Polynomial.derivative_mul,
        hP, Polynomial.derivative_X, mul_one]
      simp_rw [MvPolynomial.pderiv_mul, diagonal_add, diagonal_mul]
      rw [Finset.sum_add_distrib, Finset.sum_mul]
      simp [diagonal, MvPolynomial.pderiv_X, Pi.single_apply]

/-- The diagonal restriction of the Euler operator is `X` times the
derivative of the diagonal restriction. -/
@[simp] theorem diagonal_eulerOperator {R σ : Type*} [CommSemiring R]
    [Fintype σ] (P : MvPolynomial σ R) :
    diagonal (eulerOperator P) = Polynomial.X * (diagonal P).derivative := by
  classical
  calc
    diagonal (eulerOperator P) =
        ∑ i : σ, diagonal (MvPolynomial.X i * MvPolynomial.pderiv i P) := by
      simp [eulerOperator, diagonal]
    _ = Polynomial.X *
        ∑ i : σ, diagonal (MvPolynomial.pderiv i P) := by
      simp [Finset.mul_sum]
    _ = Polynomial.X * (diagonal P).derivative := by
      rw [derivative_diagonal]

end

end MvPolynomial
