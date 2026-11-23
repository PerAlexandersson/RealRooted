/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic.TypeStar

/-!
# Second coefficients of products and powers of formal power series
-/

public section

namespace PowerSeries

variable {R : Type*} [CommSemiring R]

/-- The second coefficient of a product is a three-term convolution. -/
theorem coeff_two_mul (φ ψ : PowerSeries R) :
    coeff 2 (φ * ψ) = coeff 2 φ * constantCoeff ψ +
      coeff 1 φ * coeff 1 ψ + constantCoeff φ * coeff 2 ψ := by
  have h : Finset.antidiagonal 2 = {(0, 2), (1, 1), (2, 0)} := rfl
  simp [coeff_mul, h, coeff_zero_eq_constantCoeff]
  ring

/-- The second coefficient of a power with unit constant coefficient. -/
theorem coeff_two_pow_of_constantCoeff_eq_one {φ : PowerSeries R}
    (h0 : constantCoeff φ = 1) (m : ℕ) :
    coeff 2 (φ ^ m) = (m : R) * coeff 2 φ + (m.choose 2 : R) * coeff 1 φ ^ 2 := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [pow_succ, coeff_two_mul, ih, coeff_one_pow]
      simp only [map_pow, h0, one_pow, mul_one, one_mul,
        Nat.choose_succ_succ, Nat.choose_one_right, Nat.cast_add, Nat.cast_one]
      ring

end PowerSeries
