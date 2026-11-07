/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import RealRooted.Mathlib.RingTheory.PowerSeries.BinomialDerivative
import Mathlib.Tactic.Ring

/-! # Negative exponent one gives the formal inverse -/

public section

namespace PowerSeries

/-- The binomial series at exponent negative one is a right inverse to
`1 + X`, over any commutative binomial ring. -/
theorem one_add_X_mul_binomialSeries_neg_one
    {R : Type*} [CommRing R] [BinomialRing R] :
    (1 + X) * binomialSeries R (-1 : R) = 1 := by
  have hone : binomialSeries R (1 : R) = 1 + X := by
    simpa using (binomialSeries_nat (A := R) (R := R) 1)
  calc
    _ = binomialSeries R (1 : R) * binomialSeries R (-1 : R) := by rw [hone]
    _ = binomialSeries R ((1 : R) + (-1)) := (binomialSeries_add 1 (-1)).symm
    _ = 1 := by simp [binomialSeries_zero]

/-- The canonical binomial substitution for exponent negative one is a right
inverse to every formal power series with constant coefficient one. -/
theorem mul_subst_binomialSeries_neg_one
    {R : Type*} [CommRing R] [BinomialRing R]
    (H : PowerSeries R) (hH : constantCoeff H = 1) :
    H * subst (H - 1) (binomialSeries R (-1 : R)) = 1 := by
  let g : PowerSeries R := H - 1
  have hg : HasSubst g := HasSubst.of_constantCoeff_zero' (by simp [g, hH])
  have hmapH : substAlgHom (R := R) hg (1 + X) = H := by
    rw [map_add, map_one, substAlgHom_X]
    dsimp [g]
    ring
  have hid := congrArg (substAlgHom (R := R) hg)
    (one_add_X_mul_binomialSeries_neg_one (R := R))
  rw [map_mul, map_one, hmapH] at hid
  simpa only [coe_substAlgHom] using hid

end PowerSeries
