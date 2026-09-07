/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
import RealRooted.DegreeDropReversal
import RealRooted.Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
import RealRooted.Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.Ring

/-!
# Newton identities for reversed polynomial roots

This file combines the evaluated Newton recurrence with Vieta's formulas for
polynomial roots. It gives a high-coefficient recurrence for ordinary roots
and an all-order low-coefficient recurrence for reciprocal roots.
-/

open Polynomial

noncomputable section

namespace RealRooted.RootVieta

variable {K : Type*} [Field K]

/-- The elementary symmetric functions of the reversed roots are the low
coefficient ratios of the original polynomial. This all-index form also covers
indices above the degree, where both sides vanish. -/
theorem reverse_roots_esymm_eq_coeff_div
    {p : K[X]} (hp : p.Splits) (h0 : p.coeff 0 ≠ 0) (k : ℕ) :
    p.reverse.roots.esymm k = (-1 : K) ^ k * p.coeff k / p.coeff 0 := by
  by_cases hk : k ≤ p.natDegree
  · have hqsplit : p.reverse.Splits := DegreeDropReversal.splits_reverse hp
    have hqdeg : p.reverse.natDegree = p.natDegree := by
      calc
        p.reverse.natDegree = p.reverse.roots.card :=
          hqsplit.natDegree_eq_card_roots
        _ = p.roots.card := DegreeDropReversal.card_roots_reverse hp h0
        _ = p.natDegree := hp.natDegree_eq_card_roots.symm
    have hqlc : p.reverse.leadingCoeff = p.coeff 0 := by
      rw [Polynomial.reverse_leadingCoeff,
        Polynomial.trailingCoeff_eq_coeff_zero h0]
    have hqcoeff :
        p.reverse.coeff (p.reverse.natDegree - k) = p.coeff k := by
      rw [hqdeg, Polynomial.coeff_reverse,
        Polynomial.revAt_le (Nat.sub_le _ _), Nat.sub_sub_self hk]
    have hkq : k ≤ p.reverse.natDegree := by rw [hqdeg]; exact hk
    rw [hqsplit.esymm_roots_eq_coeff_div_leadingCoeff
      (DegreeDropReversal.reverse_ne_zero_of_coeff_zero_ne h0) hkq,
      hqcoeff, hqlc]
  · have hkn : p.natDegree < k := Nat.lt_of_not_ge hk
    have hcard : p.reverse.roots.card < k := by
      rw [DegreeDropReversal.card_roots_reverse hp h0,
        ← hp.natDegree_eq_card_roots]
      exact hkn
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt hkn]
    simp only [mul_zero, zero_div]
    simp [Multiset.esymm, Multiset.powersetCard_eq_empty k hcard]

/-- Power sums of the reversed roots are reciprocal-root power sums of the
original polynomial, with multiplicities preserved. -/
theorem reverse_roots_powerSum_eq_sum_inv_pow
    {p : K[X]} (hp : p.Splits) (h0 : p.coeff 0 ≠ 0) (k : ℕ) :
    p.reverse.roots.powerSum k =
      (p.roots.map fun r => r⁻¹ ^ k).sum := by
  rw [DegreeDropReversal.roots_reverse_eq_map_inv_of_splits_coeff_zero_ne
    hp h0]
  simp [Multiset.powerSum]

/-- Newton recurrence for root power sums, expressed through the high
coefficients of a split polynomial. -/
theorem leadingCoeff_mul_roots_powerSum
    {p : K[X]} (hp : p.Splits) (hne : p ≠ 0)
    (k : ℕ) (hk : 0 < k) (hkdeg : k ≤ p.natDegree) :
    p.leadingCoeff * p.roots.powerSum k =
      -(k : K) * p.coeff (p.natDegree - k) -
        ∑ a ∈ Finset.antidiagonal k with a.1 ∈ Set.Ioo 0 k,
          p.coeff (p.natDegree - a.1) * p.roots.powerSum a.2 := by
  have hn := Multiset.powerSum_eq_mul_esymm_sub_sum p.roots k hk
  have hlc : p.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hne
  have hsign (n : ℕ) : (-1 : K) ^ n * (-1 : K) ^ n = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    simp
  have hfirst :
      (-1 : K) ^ (k + 1) * (k : K) * p.roots.esymm k =
        (-(k : K) * p.coeff (p.natDegree - k)) / p.leadingCoeff := by
    rw [hp.esymm_roots_eq_coeff_div_leadingCoeff hne hkdeg,
      pow_succ, div_eq_mul_inv]
    calc
      _ = -(((-1 : K) ^ k * (-1 : K) ^ k) *
          ((k : K) * p.coeff (p.natDegree - k) *
            p.leadingCoeff⁻¹)) := by ring
      _ = _ := by rw [hsign]; ring
  have hsummand (i j : ℕ) (hi : i ≤ p.natDegree) :
      (-1 : K) ^ i * p.roots.esymm i * p.roots.powerSum j =
        (p.coeff (p.natDegree - i) * p.roots.powerSum j) /
          p.leadingCoeff := by
    rw [hp.esymm_roots_eq_coeff_div_leadingCoeff hne hi,
      div_eq_mul_inv]
    calc
      _ = ((-1 : K) ^ i * (-1 : K) ^ i) *
          (p.coeff (p.natDegree - i) * p.roots.powerSum j *
            p.leadingCoeff⁻¹) := by ring
      _ = _ := by rw [hsign]; ring
  rw [hfirst] at hn
  have hsum :
      (∑ a ∈ Finset.antidiagonal k with a.1 ∈ Set.Ioo 0 k,
          (-1 : K) ^ a.1 * p.roots.esymm a.1 *
            p.roots.powerSum a.2) =
        ∑ a ∈ Finset.antidiagonal k with a.1 ∈ Set.Ioo 0 k,
          (p.coeff (p.natDegree - a.1) * p.roots.powerSum a.2) /
            p.leadingCoeff := by
    apply Finset.sum_congr rfl
    intro a ha
    simp only [Finset.mem_filter] at ha
    apply hsummand
    exact (Set.mem_Ioo.mp ha.2).2.le.trans hkdeg
  rw [hsum, ← Finset.sum_div, ← sub_div] at hn
  have hscaled := (eq_div_iff hlc).mp hn
  calc
    p.leadingCoeff * p.roots.powerSum k =
        p.roots.powerSum k * p.leadingCoeff := mul_comm _ _
    _ = _ := hscaled

/-- Newton recurrence for power sums of the reversed roots, expressed through
the low coefficients of the original polynomial. -/
theorem coeff_zero_mul_reverse_roots_powerSum
    {p : K[X]} (hp : p.Splits) (h0 : p.coeff 0 ≠ 0)
    (k : ℕ) (hk : 0 < k) :
    p.coeff 0 * p.reverse.roots.powerSum k =
      -(k : K) * p.coeff k -
        ∑ a ∈ Finset.antidiagonal k with a.1 ∈ Set.Ioo 0 k,
          p.coeff a.1 * p.reverse.roots.powerSum a.2 := by
  have hn := Multiset.powerSum_eq_mul_esymm_sub_sum
    p.reverse.roots k hk
  simp_rw [reverse_roots_esymm_eq_coeff_div hp h0] at hn
  have hsign (n : ℕ) : (-1 : K) ^ n * (-1 : K) ^ n = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    simp
  have hfirst :
      (-1 : K) ^ (k + 1) * (k : K) *
          ((-1 : K) ^ k * p.coeff k / p.coeff 0) =
        (-(k : K) * p.coeff k) / p.coeff 0 := by
    rw [pow_succ, div_eq_mul_inv]
    calc
      _ = -(((-1 : K) ^ k * (-1 : K) ^ k) *
          ((k : K) * p.coeff k * (p.coeff 0)⁻¹)) := by ring
      _ = _ := by rw [hsign]; ring
  have hsummand (i j : ℕ) :
      (-1 : K) ^ i *
          ((-1 : K) ^ i * p.coeff i / p.coeff 0) *
          p.reverse.roots.powerSum j =
        (p.coeff i * p.reverse.roots.powerSum j) / p.coeff 0 := by
    rw [div_eq_mul_inv]
    calc
      _ = ((-1 : K) ^ i * (-1 : K) ^ i) *
          (p.coeff i * p.reverse.roots.powerSum j *
            (p.coeff 0)⁻¹) := by ring
      _ = _ := by rw [hsign]; ring
  rw [hfirst] at hn
  simp_rw [hsummand] at hn
  rw [← Finset.sum_div, ← sub_div] at hn
  have hscaled := (eq_div_iff h0).mp hn
  calc
    p.coeff 0 * p.reverse.roots.powerSum k =
        p.reverse.roots.powerSum k * p.coeff 0 := mul_comm _ _
    _ = _ := hscaled

/-- Consumer-facing reciprocal-root form of
`coeff_zero_mul_reverse_roots_powerSum`. -/
theorem coeff_zero_mul_sum_inv_roots_pow
    {p : K[X]} (hp : p.Splits) (h0 : p.coeff 0 ≠ 0)
    (k : ℕ) (hk : 0 < k) :
    p.coeff 0 * (p.roots.map fun r => r⁻¹ ^ k).sum =
      -(k : K) * p.coeff k -
        ∑ a ∈ Finset.antidiagonal k with a.1 ∈ Set.Ioo 0 k,
          p.coeff a.1 * (p.roots.map fun r => r⁻¹ ^ a.2).sum := by
  simpa only [reverse_roots_powerSum_eq_sum_inv_pow hp h0] using
    coeff_zero_mul_reverse_roots_powerSum hp h0 k hk

end RealRooted.RootVieta
