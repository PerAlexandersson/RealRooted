import Mathlib.RingTheory.PowerSeries.Catalan
import Mathlib.RingTheory.PowerSeries.Substitution

/-!
# Catalan quadratic substitution

This transports Mathlib's Catalan power series to an arbitrary commutative
ring and records its quadratic equation after a valid substitution.
-/

namespace PowerSeries

variable (R : Type*) [CommRing R]

/-- The Catalan series with coefficients mapped into `R`. -/
noncomputable def catalanMap : R⟦X⟧ :=
  map (Nat.castRingHom R) catalanSeries

/-- Substituting a series satisfying `HasSubst` into `catalanMap` preserves
the Catalan quadratic equation. -/
theorem catalanMap_subst_eq (q : R⟦X⟧) (hq : HasSubst q) :
    (catalanMap R).subst q = 1 + q * ((catalanMap R).subst q) ^ 2 := by
  have hcat : catalanMap R ^ 2 * X + 1 = catalanMap R := by
    have h := congrArg (map (Nat.castRingHom R)) catalanSeries_sq_mul_X_add_one
    simpa only [catalanMap, map_pow, map_mul, map_add, map_one, map_X] using h
  have h := congrArg (substAlgHom hq) hcat
  rw [← coe_substAlgHom hq]
  simpa [substAlgHom_X hq, mul_comm, add_comm] using h.symm

end PowerSeries
