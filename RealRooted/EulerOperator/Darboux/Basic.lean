/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import RealRooted.EulerOperator.Shift

import Mathlib.Tactic

/-!
# Darboux operators on the unit interval

This file defines the first-order operator

`D_{a,b}(p) = X(1-X)p' + (a-bX)p`

and develops its coefficientwise and algebraic API over a commutative ring.
The ordered-root consequences live in `RealRooted.EulerOperator.Darboux.Interlacing`.
-/

@[expose] public section

open Polynomial

noncomputable section

namespace RealRooted

/-- The first-order Darboux operator
`D_{a,b}(p) = X(1-X)p' + (a-bX)p`. -/
def darbouxOperator {R : Type*} [CommRing R] (a b : R) (p : R[X]) : R[X] :=
  X * (1 - X) * p.derivative + (C a - C b * X) * p

@[simp]
theorem darbouxOperator_zero {R : Type*} [CommRing R] (a b : R) :
    darbouxOperator a b (0 : R[X]) = 0 := by
  simp [darbouxOperator]

@[simp]
theorem darbouxOperator_add {R : Type*} [CommRing R]
    (a b : R) (p q : R[X]) :
    darbouxOperator a b (p + q) =
      darbouxOperator a b p + darbouxOperator a b q := by
  simp only [darbouxOperator, derivative_add]
  ring

@[simp]
theorem darbouxOperator_neg {R : Type*} [CommRing R]
    (a b : R) (p : R[X]) :
    darbouxOperator a b (-p) = -darbouxOperator a b p := by
  simp only [darbouxOperator, derivative_neg]
  ring

/-- The Darboux operator commutes with multiplication by constants. -/
@[simp]
theorem darbouxOperator_C_mul {R : Type*} [CommRing R]
    (a b c : R) (p : R[X]) :
    darbouxOperator a b (C c * p) = C c * darbouxOperator a b p := by
  simp only [darbouxOperator, derivative_mul, derivative_C, zero_mul, zero_add]
  ring

@[simp]
theorem darbouxOperator_eval_zero {R : Type*} [CommRing R]
    (a b : R) (p : R[X]) :
    (darbouxOperator a b p).eval 0 = a * p.eval 0 := by
  simp [darbouxOperator]

@[simp]
theorem darbouxOperator_eval_one {R : Type*} [CommRing R]
    (a b : R) (p : R[X]) :
    (darbouxOperator a b p).eval 1 = (a - b) * p.eval 1 := by
  simp [darbouxOperator]

/-- At a root of the input, only the derivative term of the Darboux operator
survives. -/
theorem darbouxOperator_eval_isRoot {R : Type*} [CommRing R]
    (a b : R) {p : R[X]} {r : R} (hr : p.IsRoot r) :
    (darbouxOperator a b p).eval r = r * (1 - r) * p.derivative.eval r := by
  simp only [darbouxOperator, eval_add, eval_mul, eval_sub, eval_X, eval_one, eval_C]
  rw [show p.eval r = 0 from hr]
  ring

/-- Coefficients of the Darboux operator away from the constant term. -/
theorem coeff_darbouxOperator_succ {R : Type*} [CommRing R]
    (a b : R) (p : R[X]) (k : ℕ) :
    (darbouxOperator a b p).coeff (k + 1) =
      ((k : R) + 1 + a) * p.coeff (k + 1) -
        ((k : R) + b) * p.coeff k := by
  have hform :
      darbouxOperator a b p =
        X * p.derivative - X * (X * p.derivative) +
          C a * p - C b * (X * p) := by
    simp only [darbouxOperator]
    ring
  rw [hform, coeff_sub, coeff_add, coeff_sub, coeff_X_mul,
    coeff_C_mul, coeff_C_mul, coeff_X_mul, coeff_derivative]
  cases k with
  | zero =>
      simp
      ring
  | succ k =>
      rw [coeff_X_mul, coeff_derivative,
        show k + 1 + 1 = (k + 1) + 1 by rfl, coeff_X_mul]
      push_cast
      ring

/-- Differentiating a Darboux operator shifts both parameters and contributes
the scalar correction `-b`. -/
theorem derivative_darbouxOperator {R : Type*} [CommRing R]
    (a b : R) (p : R[X]) :
    (darbouxOperator a b p).derivative =
      darbouxOperator (a + 1) (b + 2) p.derivative - C b * p := by
  simp only [darbouxOperator, derivative_sub, derivative_mul, derivative_C,
    derivative_X, derivative_one, zero_mul, one_mul, map_add, map_one,
    map_ofNat]
  ring

/-- Shifting both parameters adds a multiple of `(1-X)p`. -/
theorem darbouxOperator_add_parameters {R : Type*} [CommRing R]
    (a b s : R) (p : R[X]) :
    darbouxOperator (a + s) (b + s) p =
      darbouxOperator a b p + C s * (1 - X) * p := by
  simp only [darbouxOperator, map_add]
  ring

/-- Difference form of `darbouxOperator_add_parameters`. -/
theorem darbouxOperator_shift_sub {R : Type*} [CommRing R]
    (a b s : R) (p : R[X]) :
    darbouxOperator (a + s) (b + s) p - darbouxOperator a b p =
      C s * (1 - X) * p := by
  rw [darbouxOperator_add_parameters]
  abel

/-- Abstract Darboux-square identity. The displayed scalar relation is the
only compatibility required between the four parameters. -/
theorem darbouxOperator_comp_commute {R : Type*} [CommRing R]
    (a b A B : R) (h : B - A = b - a + 1) (p : R[X]) :
    darbouxOperator a b (darbouxOperator A B p) =
      darbouxOperator A (B - 1) (darbouxOperator a (b + 1) p) := by
  have hB : B = A + b - a + 1 := by
    linear_combination h
  rw [hB]
  simp only [darbouxOperator, derivative_mul, derivative_C, derivative_X,
    derivative_one, one_mul, map_add, map_sub, map_one]
  ring

/-- A Darboux-square identity remains valid after scaling its outer input. -/
theorem darbouxOperator_C_mul_comp_commute {R : Type*} [CommRing R]
    (a b A B c : R) (h : B - A = b - a + 1) (p : R[X]) :
    darbouxOperator a b (C c * darbouxOperator A B p) =
      C c * darbouxOperator A (B - 1) (darbouxOperator a (b + 1) p) := by
  rw [darbouxOperator_C_mul, darbouxOperator_comp_commute a b A B h]

/-- Commuting a shifted Euler operator through a positive power of `1-X`
produces a Darboux operator. -/
theorem eulerShift_one_sub_X_pow {R : Type*} [CommRing R]
    (a : R) (r : ℕ) (p : R[X]) :
    eulerShift a ((1 - X) ^ (r + 1) * p) =
      (1 - X) ^ r * darbouxOperator a (a + r + 1) p := by
  simp only [eulerShift, darbouxOperator, derivative_mul, derivative_pow_succ,
    derivative_sub, derivative_one, derivative_X, zero_sub, map_add, map_one,
    map_natCast]
  ring

end RealRooted
