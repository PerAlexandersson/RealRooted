import Mathlib.Algebra.LinearRecurrence
import Mathlib.Algebra.Polynomial.Module.AEval

/-!
# Annihilators for linear recurrences

This Mathlib-shaped shim identifies a constant-coefficient recurrence with
annihilation by its characteristic polynomial under the forward shift.
Construction and uniqueness of recurrence solutions remain in Mathlib's
`LinearRecurrence` API; factor decomposition is a separate client of the
existing polynomial-action kernel theorems.
-/

open Finset Polynomial

namespace LinearRecurrence

variable {R : Type*}

section Semiring

variable [Semiring R]

/-- The forward shift on sequences. -/
def forwardShift : (ℕ → R) →ₗ[R] ℕ → R :=
  LinearMap.funLeft R R Nat.succ

@[simp]
theorem forwardShift_apply (u : ℕ → R) (n : ℕ) :
    forwardShift u n = u (n + 1) :=
  rfl

@[simp]
theorem forwardShift_pow_apply (k : ℕ) (u : ℕ → R) (n : ℕ) :
    (forwardShift ^ k) u n = u (n + k) := by
  induction k generalizing u n with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, Module.End.mul_apply]
      rw [ih (forwardShift u) n]
      simp only [forwardShift_apply]
      congr 1

end Semiring

section CommRing

variable [CommRing R]

/-- A sequence solves a recurrence exactly when its characteristic polynomial
annihilates it under the forward shift. -/
theorem isSolution_iff_aeval_charPoly_eq_zero (E : LinearRecurrence R) (u : ℕ → R) :
    E.IsSolution u ↔ Polynomial.aeval forwardShift E.charPoly u = 0 := by
  have hcalc (n : ℕ) :
      Polynomial.aeval forwardShift E.charPoly u n =
        u (n + E.order) - ∑ i, E.coeffs i * u (n + i) := by
    simp [LinearRecurrence.charPoly, ← C_mul_X_pow_eq_monomial,
      forwardShift_pow_apply]
  constructor
  · intro h
    ext n
    rw [hcalc]
    exact sub_eq_zero.mpr (h n)
  · intro h n
    have := congr_fun h n
    rw [hcalc] at this
    exact sub_eq_zero.mp this

end CommRing

end LinearRecurrence
