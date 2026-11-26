/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import RealRooted.CombinatorialExamples.CycleTypeDescents.NecklaceProduct
public import RealRooted.RootLocation.Basic
import RealRooted.CombinatorialExamples.LongCycleDescents.AllSizes
import RealRooted.Transforms.BrandenE.Products
import RealRooted.RootLocation.Mobius
import Mathlib.Tactic

/-!
# Distinct cycle lengths give real-rooted class descent polynomials

The alphabet of distinct parts is an ordinary product of the single-cycle necklace polynomials.
Each transformed factor is rooted in `[-1,0]` by the all-size long-cycle theorem at cutoff `n`.
Brändén's diamond theorem (arXiv:math/0403364v2, Theorem 3.13 and equation (4.1))
then applies repeatedly. The existing exterior-ray argument preserves the interval at each step.
-/

public section

noncomputable section

open Polynomial Finset Set

namespace RealRooted.CycleTypeDescents

/-- The transformed alphabet of a single cycle has every root in `[-1,0]`. -/
theorem isRealRootedIn_brandenE_necklacePolynomial {j : ℕ} (hj : 3 ≤ j) :
    IsRealRootedIn (Set.Icc (-1) 0) (brandenE (necklacePolynomial j)) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by lia : j ≠ 0)
  have ha : alphabetPolynomial (n + 1) {(n + 1)} = necklacePolynomial (n + 1) := by
    rw [alphabetPolynomial_eq_prod_of_nodup (by simp) (by simp; lia) (by simp)]
    simp
  rw [← ha, brandenE_alphabetPolynomial, realDescentPolynomial_singleton (by lia)]
  have hD : IsRealRootedIn (Iic 0) (LongCycleDescents.realDescentPolynomial (n + 1) (n + 1)) :=
    ⟨LongCycleDescents.realDescentPolynomial_ne_zero le_rfl,
      LongCycleDescents.realDescentPolynomial_splits hj le_rfl,
      roots_nonpos_of_hasNonnegCoeffs
        (LongCycleDescents.realDescentPolynomial_hasNonnegCoeffs _ _)⟩
  have hdeg : (LongCycleDescents.realDescentPolynomial (n + 1) (n + 1)).natDegree ≤ n := by
    rw [← realDescentPolynomial_singleton (by lia)]
    exact natDegree_realDescentPolynomial_le n _
  exact (IsRealRootedIn.X (by norm_num : (0 : ℝ) ∈ Set.Icc (-1) 0)).mul
    (hD.mobiusTransform_one_zero_one_one hdeg).1

/-- Every nonempty conjugacy class with distinct parts at least three has a real-rooted
ordinary descent polynomial, with its faithful permutation-sum definition. -/
theorem realDescentPolynomial_splits_of_nodup {n : ℕ} {parts : Multiset ℕ}
    (hs : parts.sum = n + 1) (hl : ∀ j ∈ parts, 3 ≤ j) (hd : parts.Nodup) :
    (realDescentPolynomial (n + 1) parts).Splits := by
  apply realDescentPolynomial_splits_of_brandenE
  rw [alphabetPolynomial_eq_prod_of_nodup hs (fun j hj => (hl j hj).trans' (by decide)) hd]
  exact (isRealRootedIn_brandenE_prod parts.toFinset necklacePolynomial
    (fun j hj => isRealRootedIn_brandenE_necklacePolynomial (hl j
      (Multiset.mem_toFinset.mp hj)))).splits

/-- Every cycle type with distinct parts at least three has a real-rooted class descent
polynomial; this includes the empty type and its constant enumerator. -/
theorem realDescentPolynomial_splits {n : ℕ} {parts : Multiset ℕ}
    (hs : parts.sum = n) (hl : ∀ j ∈ parts, 3 ≤ j) (hd : parts.Nodup) :
    (realDescentPolynomial n parts).Splits := by
  cases n with
  | zero =>
    have hp : parts = 0 := by
      apply Multiset.eq_zero_iff_forall_notMem.mpr
      intro j hj
      have hb := Multiset.le_sum_of_mem hj
      rw [hs] at hb
      have ha := hl j hj
      lia
    rw [hp, realDescentPolynomial_zero]
    exact Splits.one
  | succ n => exact realDescentPolynomial_splits_of_nodup hs hl hd

/-- Distinct cycle lengths at least three give a nonzero polynomial with only nonpositive roots. -/
theorem realDescentPolynomial_isRealRootedIn {n : ℕ} {parts : Multiset ℕ}
    (hs : parts.sum = n) (hl : ∀ j ∈ parts, 3 ≤ j) (hd : parts.Nodup) :
    IsRealRootedIn (Set.Iic 0) (realDescentPolynomial n parts) := by
  have hsplit := realDescentPolynomial_splits hs hl hd
  refine ⟨?_, hsplit, roots_nonpos_of_hasNonnegCoeffs
    (realDescentPolynomial_hasNonnegCoeffs n parts)⟩
  cases n with
  | zero =>
    have hp : parts = 0 := by
      apply Multiset.eq_zero_iff_forall_notMem.mpr
      intro j hj
      have hb := Multiset.le_sum_of_mem hj
      rw [hs] at hb
      have ha := hl j hj
      lia
    rw [hp, realDescentPolynomial_zero]
    exact one_ne_zero
  | succ n =>
    apply realDescentPolynomial_ne_zero_of_brandenE
    rw [alphabetPolynomial_eq_prod_of_nodup hs (fun j hj => (hl j hj).trans' (by decide)) hd]
    exact (isRealRootedIn_brandenE_prod parts.toFinset necklacePolynomial
      (fun j hj => isRealRootedIn_brandenE_necklacePolynomial (hl j
        (Multiset.mem_toFinset.mp hj)))).ne_zero

end RealRooted.CycleTypeDescents
