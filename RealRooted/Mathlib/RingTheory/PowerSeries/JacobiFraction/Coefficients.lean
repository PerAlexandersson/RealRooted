/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import RealRooted.Mathlib.RingTheory.PowerSeries.JacobiFraction.Step

import Mathlib.Tactic.TypeStar

/-!
# Recovering the two coefficients of a formal Jacobi step

The linear coefficient is the diagonal. The quadratic coefficient is its
square plus the outgoing numerator times the constant coefficient of the tail.
A nonzero outgoing numerator determines the entire tail over an integral domain.
-/

public section

namespace PowerSeries

variable {R : Type*} [CommRing R]

/-- The Jacobi step recurrence with the first variable factor separated. -/
theorem jacobiStep_eq_one_add (b c : R) (f : R⟦X⟧) :
    jacobiStep b c f =
      1 + X * (C b * jacobiStep b c f + X * (C c * f * jacobiStep b c f)) := by
  linear_combination one_sub_mul_jacobiStep b c f

/-- Coefficients of a Jacobi step satisfy the associated two-term convolution. -/
theorem coeff_succ_jacobiStep (b c : R) (f : R⟦X⟧) (n : ℕ) :
    coeff (n + 1) (jacobiStep b c f) = b * coeff n (jacobiStep b c f) +
      coeff n (X * (C c * f * jacobiStep b c f)) := by
  have h := congrArg (coeff (n + 1)) (jacobiStep_eq_one_add b c f)
  simpa only [map_add, coeff_one, Nat.add_one_ne_zero, ite_false, zero_add,
    coeff_succ_X_mul, coeff_C_mul] using h

/-- The first coefficient recovers the Jacobi diagonal. -/
@[simp] theorem coeff_one_jacobiStep (b c : R) (f : R⟦X⟧) :
    coeff 1 (jacobiStep b c f) = b := by
  simpa only [coeff_zero_eq_constantCoeff_apply, map_mul, constantCoeff_X,
    zero_mul, constantCoeff_jacobiStep, mul_one, add_zero] using
    coeff_succ_jacobiStep b c f 0

/-- The second coefficient recovers the outgoing numerator for a normalized tail. -/
theorem coeff_two_jacobiStep (b c : R) (f : R⟦X⟧) :
    coeff 2 (jacobiStep b c f) = b * b + c * constantCoeff f := by
  simpa only [coeff_one_jacobiStep, coeff_succ_X_mul,
    coeff_zero_eq_constantCoeff_apply, map_mul, constantCoeff_C,
    constantCoeff_jacobiStep, mul_one] using coeff_succ_jacobiStep b c f 1

/-- A Jacobi step with a nonzero outgoing numerator determines its tail. -/
theorem jacobiStep_injective [IsDomain R] (b : R) {c : R} (hc : c ≠ 0) :
    Function.Injective (jacobiStep b c) := by
  intro f g h
  have hs : jacobiStep b c f ≠ 0 := by
    intro hz
    have hconst := congrArg constantCoeff hz
    simp at hconst
  have hC : (C c : R⟦X⟧) ≠ 0 := by
    intro hz
    have hconst := congrArg constantCoeff hz
    exact hc (by simpa using hconst)
  have hmul : (1 - C b * X - C c * X ^ 2 * f) * jacobiStep b c f =
      (1 - C b * X - C c * X ^ 2 * g) * jacobiStep b c f := by
    rw [one_sub_mul_jacobiStep, h, one_sub_mul_jacobiStep]
  have hd := mul_right_cancel₀ hs hmul
  apply mul_left_cancel₀ (mul_ne_zero hC (pow_ne_zero 2 X_ne_zero))
  linear_combination -hd

end PowerSeries
