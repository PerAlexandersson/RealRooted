/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.RingTheory.Polynomial.Vieta

import Mathlib.Tactic.Ring

/-!
# Additional Vieta identities

This file gives receiver-style rearrangements of Mathlib's coefficient Vieta
identity that solve directly for an elementary symmetric function of the roots.
-/

@[expose] public section

noncomputable section

namespace Polynomial

variable {R : Type*} [CommRing R] [IsDomain R]

/-- Denominator-free Vieta identity solved for the elementary symmetric
function of a full root multiset. -/
theorem leadingCoeff_mul_esymm_roots_eq_coeff_of_card
    {p : R[X]} (hcard : p.roots.card = p.natDegree)
    {k : ℕ} (hk : k ≤ p.natDegree) :
    p.leadingCoeff * p.roots.esymm k =
      (-1 : R) ^ k * p.coeff (p.natDegree - k) := by
  have hv := Polynomial.coeff_eq_esymm_roots_of_card hcard
    (k := p.natDegree - k) (Nat.sub_le _ _)
  rw [Nat.sub_sub_self hk] at hv
  rw [hv]
  have hsign : (-1 : R) ^ k * (-1 : R) ^ k = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    simp
  calc
    p.leadingCoeff * p.roots.esymm k =
        1 * (p.leadingCoeff * p.roots.esymm k) := by rw [one_mul]
    _ = ((-1 : R) ^ k * (-1 : R) ^ k) *
        (p.leadingCoeff * p.roots.esymm k) := by rw [hsign]
    _ = (-1 : R) ^ k *
        (p.leadingCoeff * (-1 : R) ^ k * p.roots.esymm k) := by ring

variable {K : Type*} [Field K]

/-- A coefficient determines the corresponding elementary symmetric function
of a full root multiset. -/
theorem esymm_roots_eq_coeff_div_leadingCoeff_of_card
    {p : K[X]} (hcard : p.roots.card = p.natDegree) (hp : p ≠ 0)
    {k : ℕ} (hk : k ≤ p.natDegree) :
    p.roots.esymm k =
      (-1 : K) ^ k * p.coeff (p.natDegree - k) / p.leadingCoeff := by
  have hlc : p.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hp
  apply (eq_div_iff hlc).2
  calc
    p.roots.esymm k * p.leadingCoeff =
        p.leadingCoeff * p.roots.esymm k := mul_comm _ _
    _ = _ := leadingCoeff_mul_esymm_roots_eq_coeff_of_card hcard hk

/-- Vieta's identity solved for an elementary symmetric function of the roots
of a split, nonzero polynomial. -/
theorem Splits.esymm_roots_eq_coeff_div_leadingCoeff
    {p : K[X]} (hp : p.Splits) (hne : p ≠ 0) {k : ℕ}
    (hk : k ≤ p.natDegree) :
    p.roots.esymm k =
      (-1 : K) ^ k * p.coeff (p.natDegree - k) / p.leadingCoeff :=
  esymm_roots_eq_coeff_div_leadingCoeff_of_card
    hp.natDegree_eq_card_roots.symm hne hk

end Polynomial
