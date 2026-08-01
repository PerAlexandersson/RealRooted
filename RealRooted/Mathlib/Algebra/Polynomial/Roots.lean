import Mathlib.Algebra.Polynomial.Roots

/-!
# Additions to Mathlib.Algebra.Polynomial.Roots

This file contains polynomial-root lemmas intended for upstreaming to Mathlib.
-/

open Polynomial

namespace Polynomial

variable {R : Type*} [CommRing R] [IsDomain R]

/-- Multiplying a polynomial by `X` does not change the sum of its roots. -/
@[simp] theorem sum_roots_X_mul (p : R[X]) :
    (X * p).roots.sum = p.roots.sum := by
  by_cases hp : p = 0
  · simp [hp]
  rw [roots_mul (mul_ne_zero X_ne_zero hp), roots_X]
  simp

end Polynomial
