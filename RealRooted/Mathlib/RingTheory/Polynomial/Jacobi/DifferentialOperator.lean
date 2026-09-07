/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.Algebra.Polynomial.Derivative

import Mathlib.Tactic

/-!
# The shifted Jacobi differential operator

This file defines the algebraic differential operator for shifted Jacobi
polynomials over a commutative ring. It is independent of the explicit Jacobi
family, its root theory, and its orthogonality theory.
-/

@[expose] public section

noncomputable section

namespace Polynomial

/-- The differential part of a shifted Jacobi equation:
`X(1-X)p'' + (b-cX)p'`.

For the classical parameters `α` and `β`, take `b = α + 1` and
`c = α + β + 2`. -/
def jacobiDifferentialOperator {R : Type*} [CommRing R]
    (b c : R) (p : R[X]) : R[X] :=
  X * (1 - X) * p.derivative.derivative +
    (C b - C c * X) * p.derivative

@[simp]
theorem jacobiDifferentialOperator_zero {R : Type*} [CommRing R]
    (b c : R) : jacobiDifferentialOperator b c (0 : R[X]) = 0 := by
  simp [jacobiDifferentialOperator]

@[simp]
theorem jacobiDifferentialOperator_add {R : Type*} [CommRing R]
    (b c : R) (p q : R[X]) :
    jacobiDifferentialOperator b c (p + q) =
      jacobiDifferentialOperator b c p + jacobiDifferentialOperator b c q := by
  simp only [jacobiDifferentialOperator, derivative_add]
  ring

@[simp]
theorem jacobiDifferentialOperator_neg {R : Type*} [CommRing R]
    (b c : R) (p : R[X]) :
    jacobiDifferentialOperator b c (-p) =
      -jacobiDifferentialOperator b c p := by
  simp only [jacobiDifferentialOperator, derivative_neg]
  ring

@[simp]
theorem jacobiDifferentialOperator_C_mul {R : Type*} [CommRing R]
    (b c s : R) (p : R[X]) :
    jacobiDifferentialOperator b c (C s * p) =
      C s * jacobiDifferentialOperator b c p := by
  simp only [jacobiDifferentialOperator, derivative_mul, derivative_C,
    zero_mul, zero_add]
  ring

/-- Coefficients of the shifted Jacobi differential operator. -/
theorem coeff_jacobiDifferentialOperator {R : Type*} [CommRing R]
    (b c : R) (p : R[X]) (k : ℕ) :
    (jacobiDifferentialOperator b c p).coeff k =
      ((k : R) + 1) * ((k : R) + b) * p.coeff (k + 1) -
        (k : R) * ((k : R) + c - 1) * p.coeff k := by
  rw [show jacobiDifferentialOperator b c p =
      X * p.derivative.derivative - X * (X * p.derivative.derivative) +
        C b * p.derivative - C c * (X * p.derivative) by
    simp only [jacobiDifferentialOperator]
    ring]
  cases k with
  | zero =>
      simp [coeff_derivative]
  | succ k =>
      simp only [coeff_add, coeff_sub, coeff_C_mul]
      rw [coeff_X_mul, coeff_X_mul, coeff_X_mul]
      cases k with
      | zero =>
          simp [coeff_derivative]
          ring
      | succ k =>
          rw [coeff_X_mul]
          simp [coeff_derivative]
          ring

/-- Coefficients after adjoining the eigenvalue term to the shifted Jacobi
differential operator. -/
theorem coeff_jacobiDifferentialOperator_add_C_mul
    {R : Type*} [CommRing R]
    (b c D : R) (p : R[X]) (k : ℕ) :
    (jacobiDifferentialOperator b c p + C D * p).coeff k =
      ((k : R) + 1) * ((k : R) + b) * p.coeff (k + 1) +
        (D - (k : R) * ((k : R) + c - 1)) * p.coeff k := by
  rw [coeff_add, coeff_jacobiDifferentialOperator, coeff_C_mul]
  ring

/-- The shifted Jacobi operator on a power of `X`. -/
theorem jacobiDifferentialOperator_X_pow {R : Type*} [CommRing R]
    (b c : R) (n : ℕ) :
    jacobiDifferentialOperator b c (X ^ n) =
      C ((n : R) * ((n : R) + b - 1)) * X ^ (n - 1) -
        C ((n : R) * ((n : R) + c - 1)) * X ^ n := by
  cases n with
  | zero => simp [jacobiDifferentialOperator]
  | succ n =>
      rw [jacobiDifferentialOperator, derivative_X_pow_succ, derivative_mul,
        derivative_C, zero_mul, zero_add]
      cases n with
      | zero =>
          simp
      | succ n =>
          rw [derivative_X_pow_succ]
          push_cast
          simp only [map_add, map_sub, map_mul, map_one]
          ring

/-- The shifted Jacobi operator on a monomial. -/
theorem jacobiDifferentialOperator_monomial {R : Type*} [CommRing R]
    (b c a : R) (n : ℕ) :
    jacobiDifferentialOperator b c (monomial n a) =
      monomial (n - 1) (a * (n : R) * ((n : R) + b - 1)) -
        monomial n (a * (n : R) * ((n : R) + c - 1)) := by
  rw [← C_mul_X_pow_eq_monomial, jacobiDifferentialOperator_C_mul,
    jacobiDifferentialOperator_X_pow]
  simp only [← C_mul_X_pow_eq_monomial, map_mul, map_sub]
  ring

end Polynomial
