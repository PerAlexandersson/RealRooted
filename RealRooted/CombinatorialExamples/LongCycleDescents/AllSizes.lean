/-
Copyright (c) 2026 Bowen Zuo and Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bowen Zuo, Per Alexandersson
-/
module

public import RealRooted.CombinatorialExamples.LongCycleDescents.Finite
public import RealRooted.CombinatorialExamples.LongCycleDescents.Structural.RankBounds
public import RealRooted.CommonInterleaver.IsolatingIntervals
import Mathlib.Tactic

/-!
# All-size long-cycle descent polynomials

The kernel checker covers ranks through 17. The independent structural bound
covers every rank from 18 onward. Both refer to the original permutation sums.

Adapted from Bowen Zuo, cycle-minimum-descent-real-roots v1.0.0 (Apache-2.0)
-/

public section

noncomputable section

open Polynomial Finset

namespace RealRooted.LongCycleDescents

/-- Every long-cycle descent row splits, at every permutation size. -/
theorem realDescentPolynomial_splits {n k : ℕ} (hk : 3 ≤ k) (hkn : k ≤ n) :
    (realDescentPolynomial n k).Splits := by
  by_cases hn : n ≤ 17
  · exact Finite.realDescentPolynomial_splits hk hkn hn
  · exact (Structural.realDescentPolynomial_roots_of_rank (by lia) hk hkn).2.1

/-- All original cutoffs split, including the Eulerian and derangement endpoints. -/
theorem all_cutoffs_splits {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) :
    (realDescentPolynomial n k).Splits := by
  by_cases h1 : k = 1
  · subst k
    exact realDescentPolynomial_one_splits (by lia)
  · by_cases h2 : k = 2
    · subst k
      exact realDescentPolynomial_two_splits hkn
    · exact realDescentPolynomial_splits (by lia) hkn

/-- Outside rank five, every long-cutoff row has simple nonpositive roots and degree `n-2`. -/
theorem realDescentPolynomial_roots {n k : ℕ} (hk : 3 ≤ k) (hkn : k ≤ n) (h5 : n ≠ 5) :
    (realDescentPolynomial n k).roots.Nodup ∧
      0 ∈ (realDescentPolynomial n k).roots ∧
      (realDescentPolynomial n k).natDegree = n - 2 ∧
      ∀ r ∈ (realDescentPolynomial n k).roots, r ≤ 0 := by
  by_cases hn : n ≤ 17
  · exact Finite.realDescentPolynomial_roots hk hkn hn h5
  · exact (Structural.realDescentPolynomial_roots_of_rank (by lia) hk hkn).2.2

private theorem long_mixture_natDegree {n : ℕ} (h5 : n ≠ 5)
    {w : ℕ → ℝ} (hw : ∀ k ∈ Icc 3 n, 0 ≤ w k) (hp : ∃ k ∈ Icc 3 n, 0 < w k) :
    (∑ k ∈ Icc 3 n, C (w k) * realDescentPolynomial n k).natDegree = n - 2 := by
  have hdegree k (hk : k ∈ Icc 3 n) :=
    (realDescentPolynomial_roots (mem_Icc.mp hk).1 (mem_Icc.mp hk).2 h5).2.2.1
  have hlc k (hk : k ∈ Icc 3 n) :
      0 < (realDescentPolynomial n k).coeff (n - 2) := by
    rw [← hdegree k hk, ← leadingCoeff]
    exact (realDescentPolynomial_hasNonnegCoeffs n k).pos_leadingCoeff
      (realDescentPolynomial_ne_zero (mem_Icc.mp hk).2)
  have hcoeff : 0 < (∑ k ∈ Icc 3 n, C (w k) * realDescentPolynomial n k).coeff (n - 2) := by
    simp only [finsetSum_coeff, coeff_C_mul]
    exact sum_pos' (fun k hk => mul_nonneg (hw k hk) (hlc k hk).le)
      (hp.imp fun k hk => ⟨hk.1, mul_pos hk.2 (hlc k hk.1)⟩)
  apply le_antisymm
  · apply natDegree_sum_le_of_forall_le
    intro k hk
    exact (natDegree_C_mul_le _ _).trans_eq (hdegree k hk)
  · exact le_natDegree_of_ne_zero hcoeff.ne'

/-- Every nonzero nonnegative long-cutoff mixture has simple nonpositive roots,
except at rank five, uniformly over all weights and all sizes. -/
theorem long_mixture_roots {n : ℕ} (hn : 3 ≤ n) (h5 : n ≠ 5)
    {w : ℕ → ℝ} (hw : ∀ k ∈ Icc 3 n, 0 ≤ w k) (hp : ∃ k ∈ Icc 3 n, 0 < w k) :
    let p := ∑ k ∈ Icc 3 n, C (w k) * realDescentPolynomial n k
    p ≠ 0 ∧ p.Splits ∧ p.roots.Nodup ∧ 0 ∈ p.roots ∧
      p.natDegree = n - 2 ∧ ∀ r ∈ p.roots, r ≤ 0 := by
  by_cases hi : n ≤ 17
  · have hh := Finite.mixture_splits hn hi h5 w hw hp
    exact ⟨ne_zero_of_mem_roots hh.2.2.1, hh.1, hh.2.1, hh.2.2.1,
      long_mixture_natDegree h5 hw hp, hh.2.2.2⟩
  · exact Structural.mixture_roots_of_rank (by lia) (fun k hk => mem_Icc.mp hk) hw hp

/-- The exceptional rank-five mixtures are explicit scalar multiples of one cubic. -/
theorem long_mixture_five (w : ℕ → ℝ) :
    (∑ k ∈ Icc 3 5, C (w k) * realDescentPolynomial 5 k) =
      C (6 * ∑ k ∈ Icc 3 5, w k) * X * (X + C 1) ^ 2 := by
  simp only [mul_sum, map_sum]
  rw [sum_mul, sum_mul]
  apply sum_congr rfl
  intro k hk
  rw [realDescentPolynomial_five (mem_Icc.mp hk).1 (mem_Icc.mp hk).2]
  simp only [map_mul]
  ring

/-- Nonzero nonnegative long-cutoff mixtures split at every size, including rank five. -/
theorem long_mixture_splits {n : ℕ} (hn : 3 ≤ n) {w : ℕ → ℝ}
    (hw : ∀ k ∈ Icc 3 n, 0 ≤ w k) (hp : ∃ k ∈ Icc 3 n, 0 < w k) :
    (∑ k ∈ Icc 3 n, C (w k) * realDescentPolynomial n k).Splits := by
  by_cases h5 : n = 5
  · subst n
    rw [long_mixture_five]
    exact ((Splits.C _).mul Splits.X).mul ((Splits.X_add_C _).pow _)
  · exact (long_mixture_roots hn h5 hw hp).2.1

/-- Every nonzero nonnegative rank-five long-cutoff mixture has the same double root. -/
theorem long_mixture_five_roots {w : ℕ → ℝ}
    (hw : ∀ k ∈ Icc 3 5, 0 ≤ w k) (hp : ∃ k ∈ Icc 3 5, 0 < w k) :
    let p := ∑ k ∈ Icc 3 5, C (w k) * realDescentPolynomial 5 k
    p ≠ 0 ∧ p.roots = {0} + 2 • ({-1} : Multiset ℝ) := by
  have hsum : 0 < ∑ k ∈ Icc 3 5, w k := sum_pos' hw hp
  have ha : (6 * ∑ k ∈ Icc 3 5, w k) ≠ 0 := ne_of_gt (by positivity)
  rw [long_mixture_five, mul_assoc]
  have hq : (X + C 1 : ℝ[X]) ^ 2 ≠ 0 := pow_ne_zero _ (monic_X_add_C 1).ne_zero
  refine ⟨mul_ne_zero (C_ne_zero.mpr ha) (mul_ne_zero X_ne_zero hq), ?_⟩
  rw [roots_C_mul _ ha, roots_mul (mul_ne_zero X_ne_zero hq), roots_X,
    roots_pow, roots_X_add_C]

/-- Long-cutoff mixtures are nonzero for every admissible nonnegative choice of weights. -/
theorem long_mixture_ne_zero {n : ℕ} (hn : 3 ≤ n) {w : ℕ → ℝ}
    (hw : ∀ k ∈ Icc 3 n, 0 ≤ w k) (hp : ∃ k ∈ Icc 3 n, 0 < w k) :
    (∑ k ∈ Icc 3 n, C (w k) * realDescentPolynomial n k) ≠ 0 := by
  by_cases h5 : n = 5
  · subst n
    exact (long_mixture_five_roots hw hp).1
  · exact (long_mixture_roots hn h5 hw hp).1

/-- The long-cutoff mixture has simple roots exactly outside rank five. -/
theorem long_mixture_roots_nodup_iff {n : ℕ} (hn : 3 ≤ n) {w : ℕ → ℝ}
    (hw : ∀ k ∈ Icc 3 n, 0 ≤ w k) (hp : ∃ k ∈ Icc 3 n, 0 < w k) :
    (∑ k ∈ Icc 3 n, C (w k) * realDescentPolynomial n k).roots.Nodup ↔ n ≠ 5 := by
  constructor
  · intro hroots h5
    subst n
    rw [(long_mixture_five_roots hw hp).2] at hroots
    simp [two_nsmul] at hroots
  · intro h5
    exact (long_mixture_roots hn h5 hw hp).2.2.1

/-- Common open intervals, with uniqueness and all root conclusions for every
nonzero nonnegative mixture of the long cutoffs. -/
def CommonIsolatingIntervals (n : ℕ) : Prop :=
  ∃ lower upper : Fin (n - 3) → ℝ, (∀ i, upper i < 0) ∧
    Pairwise (fun i j => Disjoint (Set.Ioo (lower i) (upper i))
      (Set.Ioo (lower j) (upper j))) ∧
    ∀ w : ℕ → ℝ, (∀ k ∈ Icc 3 n, 0 ≤ w k) → (∃ k ∈ Icc 3 n, 0 < w k) →
      let p := ∑ k ∈ Icc 3 n, C (w k) * realDescentPolynomial n k
      (∀ i, ∃! y, y ∈ Set.Ioo (lower i) (upper i) ∧ p.IsRoot y) ∧
      p.Splits ∧ p.roots.Nodup ∧ 0 ∈ p.roots ∧ p.natDegree = n - 2 ∧
        (p.roots.filter (· < 0)).card = n - 3

/-- Theorem 1: the same isolating intervals work for all long cutoffs and all
nonzero nonnegative mixtures, at every size except five. -/
theorem common_isolating_intervals {n : ℕ} (hn : 3 ≤ n) (h5 : n ≠ 5) :
    CommonIsolatingIntervals n := by
  classical
  let s := Icc 3 n
  have hs : s.Nonempty := ⟨3, mem_Icc.mpr ⟨le_rfl, hn⟩⟩
  let : Nonempty ↥s := hs.to_subtype
  have hall (w : ↥s → ℝ) (hw : ∀ i, 0 ≤ w i) (hp : ∃ i, 0 < w i) := by
    let v k := if h : k ∈ s then w ⟨k, h⟩ else 0
    have hvEq (i : ↥s) : v i.val = w i := by
      dsimp only [v]
      rw [dite_eq_left i.property]
    have hv : ∀ k ∈ Icc 3 n, 0 ≤ v k := by
      intro k hk
      exact (hvEq ⟨k, hk⟩).symm ▸ hw ⟨k, hk⟩
    have hvp : ∃ k ∈ Icc 3 n, 0 < v k := by
      obtain ⟨i, hi⟩ := hp
      exact ⟨i.val, i.property, by rwa [hvEq]⟩
    have hh := (long_mixture_roots hn h5 hv hvp).2
    have he : (∑ k ∈ Icc 3 n, C (v k) * realDescentPolynomial n k) =
        ∑ i : ↥s, C (w i) * realDescentPolynomial n i.val := by
      rw [← s.sum_coe_sort]
      apply sum_congr rfl
      intro i _
      rw [hvEq]
    rw [he] at hh
    exact hh
  have hfamily : ∀ i : ↥s, HasNonnegCoeffs (realDescentPolynomial n i.val) :=
    fun i => realDescentPolynomial_hasNonnegCoeffs n i.val
  obtain ⟨lower, upper, hu, hdisj, hisolate⟩ :=
    exists_common_isolating_intervals_of_simple_mixtures
      (fun i : ↥s => realDescentPolynomial n i.val) (m := n - 3) hfamily (by
        intro w hw hp
        have hh := hall w hw hp
        simpa only [show n - 3 + 1 = n - 2 by lia] using hh)
  refine ⟨lower, upper, hu, hdisj, ?_⟩
  intro w hw hp
  have hh := (long_mixture_roots hn h5 hw hp).2
  have hfinite := hisolate (fun i => w i.val) (fun i => hw i.val i.property)
    (by obtain ⟨k, hk, hp⟩ := hp; exact ⟨⟨k, hk⟩, hp⟩)
  have he := s.sum_coe_sort (fun k => C (w k) * realDescentPolynomial n k)
  rw [he] at hfinite
  refine ⟨hfinite, hh.1, hh.2.1, hh.2.2.1, hh.2.2.2.1, ?_⟩
  rw [card_negative_roots_eq_sub_one hh.1 hh.2.1 hh.2.2.1 hh.2.2.2.2, hh.2.2.2.1]
  lia

end RealRooted.LongCycleDescents
