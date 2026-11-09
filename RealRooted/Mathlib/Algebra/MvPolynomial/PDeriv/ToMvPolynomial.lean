/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.Polynomial.Derivative

/-!
# Partial derivatives of univariate polynomials viewed as multivariate polynomials

`Polynomial.toMvPolynomial i` sends a univariate polynomial to the same polynomial in the
variable `i`; the partial derivative in `i` corresponds to the derivative of `Polynomial`.
-/

public section

open Polynomial

namespace MvPolynomial

variable {R σ : Type*} [CommSemiring R]

/-- The partial derivative in the variable `i` of `p.toMvPolynomial i` is the image of the
derivative of `p`. -/
theorem pderiv_toMvPolynomial (i : σ) (p : R[X]) :
    pderiv i (p.toMvPolynomial i) = (derivative p).toMvPolynomial i := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [derivative_add, map_add, map_add, map_add, hp, hq]
  | monomial n a =>
      rw [← Polynomial.C_mul_X_pow_eq_monomial, derivative_C_mul_X_pow]
      simp only [map_mul, map_pow, Polynomial.toMvPolynomial_C, Polynomial.toMvPolynomial_X,
        map_natCast, pderiv_C_mul, Derivation.leibniz_pow, pderiv_X_self, smul_eq_mul,
        nsmul_eq_mul, mul_one]
      ring

/-- Iterated partial derivatives of `p.toMvPolynomial i` in the variable `i` are the images of the
iterated derivatives of `p`. -/
theorem iterate_pderiv_toMvPolynomial (i : σ) (j : ℕ) (p : R[X]) :
    (pderiv i)^[j] (p.toMvPolynomial i) = (derivative^[j] p).toMvPolynomial i := by
  induction j generalizing p with
  | zero => rfl
  | succ j ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, pderiv_toMvPolynomial, ih]

end MvPolynomial
