import Mathlib.Algebra.LinearRecurrence
import Mathlib.Algebra.Polynomial.Module.AEval
import Mathlib.RingTheory.Polynomial.Basic

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

/-- If a recurrence's characteristic polynomial is a product of coprime
factors, each solution is a sum of sequences annihilated by the two factors
under the forward shift. -/
theorem exists_add_of_isSolution_of_charPoly_eq_mul (E : LinearRecurrence R)
    (u : ℕ → R) {p q : R[X]} (hpq : IsCoprime p q) (hchar : E.charPoly = p * q)
    (hu : E.IsSolution u) :
    ∃ up uq : ℕ → R, u = up + uq ∧
      Polynomial.aeval forwardShift p up = 0 ∧ Polynomial.aeval forwardShift q uq = 0 := by
  have hann : Polynomial.aeval forwardShift (p * q) u = 0 := by
    rw [← hchar]
    exact E.isSolution_iff_aeval_charPoly_eq_zero u |>.mp hu
  have hmem : u ∈ LinearMap.ker (Polynomial.aeval forwardShift (p * q)) :=
    LinearMap.mem_ker.mpr hann
  rw [← Polynomial.sup_ker_aeval_eq_ker_aeval_mul_of_coprime forwardShift hpq] at hmem
  rcases Submodule.mem_sup.mp hmem with ⟨up, hup, uq, huq, hsum⟩
  exact ⟨up, uq, hsum.symm, LinearMap.mem_ker.mp hup, LinearMap.mem_ker.mp huq⟩

end CommRing

end LinearRecurrence
