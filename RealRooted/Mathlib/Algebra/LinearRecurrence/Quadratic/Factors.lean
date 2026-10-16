/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/

module

public import RealRooted.Mathlib.Algebra.LinearRecurrence.Annihilator
public import RealRooted.Mathlib.Algebra.LinearRecurrence.Quadratic

/-!
# Coprime quadratic recurrence factors

This opt-in layer combines the generic annihilator decomposition with the
explicit Vieta factorization of a quadratic recurrence. It deliberately keeps
coprimality of the polynomial factors as a caller-supplied hypothesis.
-/

public section

namespace LinearRecurrence

variable {R : Type*} [CommRing R]

/-- A quadratic recurrence solution splits into factor-annihilated summands
when its Vieta factors are coprime. -/
theorem quadratic_exists_add_of_isSolution_of_vieta {p q β₁ β₂ : R} {S : ℕ → R}
    (hS : (quadratic p q).IsSolution S)
    (hcoprime : IsCoprime (Polynomial.X - Polynomial.C β₁) (Polynomial.X - Polynomial.C β₂))
    (hsum : β₁ + β₂ = p) (hprod : β₁ * β₂ = -q) :
    ∃ S₁ S₂ : ℕ → R, S = S₁ + S₂ ∧
      Polynomial.aeval forwardShift (Polynomial.X - Polynomial.C β₁) S₁ = 0 ∧
      Polynomial.aeval forwardShift (Polynomial.X - Polynomial.C β₂) S₂ = 0 :=
  exists_add_of_isSolution_of_charPoly_eq_mul (quadratic p q) S hcoprime
    (quadratic_charPoly_eq_mul hsum hprod) hS

end LinearRecurrence
