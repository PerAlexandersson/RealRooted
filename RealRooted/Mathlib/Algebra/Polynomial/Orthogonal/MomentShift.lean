/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import RealRooted.Mathlib.Algebra.Polynomial.Moment
import RealRooted.Mathlib.Algebra.Polynomial.Orthogonal.MomentAlgebra

/-!
# Multiplication and shifted polynomial moments
-/

public section

namespace Polynomial

variable {R : Type*} [CommRing R]

/-- Shifting a moment sequence by one corresponds to multiplying the polynomial by `X`. -/
theorem momentFunctional_shift (μ : ℕ → R) (p : R[X]) :
    momentFunctional (fun k => μ (k + 1)) p = momentFunctional μ (X * p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [mul_add, momentFunctional_add, hp, hq]
  | monomial n a => simp only [X_mul_monomial, momentFunctional_monomial]

/-- A shifted pairing inserts one factor of `X` on its right input. -/
theorem momentPairing_shift (μ : ℕ → R) (p q : R[X]) :
    momentPairing (fun k => μ (k + 1)) p q = momentPairing μ p (X * q) := by
  rw [momentPairing, momentFunctional_shift]
  simp only [momentPairing, mul_left_comm]

/-- A shifted monomial pairing increases the monomial exponent by one. -/
theorem momentPairing_shift_X_pow (μ : ℕ → R) (i : ℕ) (q : R[X]) :
    momentPairing (fun k => μ (k + 1)) (X ^ i) q =
      momentPairing μ (X ^ (i + 1)) q := by
  rw [momentPairing_shift, ← momentPairing_X_mul_left, ← pow_succ']

end Polynomial
