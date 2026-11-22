/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Davidson, Yury Kudryashov, The RealRooted contributors
-/
module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Basic.Real.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Tactic.TypeStar

/-!
# Positive roots of an Euler differential operator

The operator `p ↦ X * p.derivative - a * p` decreases the multiplicity of
each root by at most one. For a natural parameter, Rolle's theorem applied
to `p(x) / x^a` supplies a new positive root between two positive roots of
`p`. Together these facts show that at most one positive root is lost,
counting multiplicities, provided the output is nonzero.

The counting argument follows Mathlib's proof of
`Polynomial.card_roots_le_derivative`.
-/

public section

open Set

namespace Polynomial

/-- An Euler differential operator lowers root multiplicities by at most one
whenever its output is nonzero. -/
theorem rootMultiplicity_sub_one_le_euler_sub
    {R : Type*} [CommRing R] (p : R[X]) (a x : R)
    (hq : X * p.derivative - C a * p ≠ 0) :
    p.rootMultiplicity x - 1 ≤ (X * p.derivative - C a * p).rootMultiplicity x := by
  rw [le_rootMultiplicity_iff hq]
  have hp := p.pow_rootMultiplicity_dvd x
  exact (dvd_mul_of_dvd_right (pow_sub_one_dvd_derivative_of_pow_dvd hp) X).sub
    (dvd_mul_of_dvd_right ((pow_dvd_pow _ (Nat.sub_le _ _)).trans hp) (C a))

/-- Two positive roots enclose a root of the natural-parameter Euler operator. -/
theorem exists_euler_sub_isRoot_between {p : ℝ[X]} (a : ℕ) {s t : ℝ}
    (hspos : 0 < s) (hst : s < t) (hs : p.IsRoot s) (ht : p.IsRoot t) :
    ∃ x ∈ Ioo s t, (X * p.derivative - C (a : ℝ) * p).IsRoot x := by
  cases a with
  | zero =>
    obtain ⟨x, hx, hd⟩ := exists_deriv_eq_zero hst p.continuousOn
      (hs.eq_zero.trans ht.eq_zero.symm)
    refine ⟨x, hx, ?_⟩
    simp [IsRoot, ← p.deriv, hd]
  | succ a =>
    have hne (x : ℝ) (hx : x ∈ Icc s t) : x ≠ 0 := ne_of_gt (hspos.trans_le hx.1)
    have hc : ContinuousOn (fun x => p.eval x / x ^ (a + 1)) (Icc s t) :=
      p.continuous.continuousOn.div (continuous_id.pow _).continuousOn
        (fun x hx => pow_ne_zero _ (hne x hx))
    have he : p.eval s / s ^ (a + 1) = p.eval t / t ^ (a + 1) := by
      rw [hs.eq_zero, ht.eq_zero, zero_div, zero_div]
    obtain ⟨x, hx, hd⟩ := exists_hasDerivAt_eq_zero hst hc he
      (fun x hx => (p.hasDerivAt x).div ((hasDerivAt_id x).pow (a + 1))
        (pow_ne_zero _ (hne x ⟨hx.1.le, hx.2.le⟩)))
    have hx0 : x ≠ 0 := hne x ⟨hx.1.le, hx.2.le⟩
    have hnum : p.derivative.eval x * x ^ (a + 1) -
        p.eval x * ((a + 1 : ℝ) * x ^ a) = 0 := by
      simpa [pow_ne_zero _ hx0] using hd
    have hmul : x ^ a * (x * p.derivative.eval x - (a + 1 : ℝ) * p.eval x) = 0 := by
      rw [pow_succ] at hnum
      linear_combination hnum
    refine ⟨x, hx, ?_⟩
    simpa [IsRoot] using (mul_eq_zero.mp hmul).resolve_left (pow_ne_zero _ hx0)

/-- Distinct positive roots of `p` require almost as many new positive roots
of a nonzero natural-parameter Euler differential operator. -/
theorem card_pos_roots_toFinset_le_euler_sub_sdiff_add_one (p : ℝ[X]) (a : ℕ)
    (hq : X * p.derivative - C (a : ℝ) * p ≠ 0) :
    (p.roots.filter (0 < ·)).toFinset.card ≤
      (((X * p.derivative - C (a : ℝ) * p).roots.filter (0 < ·)).toFinset \
        (p.roots.filter (0 < ·)).toFinset).card + 1 := by
  classical
  have hp : p ≠ 0 := by rintro rfl; simp at hq
  refine Finset.card_le_sdiff_of_interleaved fun s hs t ht hst _ => ?_
  simp only [Multiset.mem_toFinset, Multiset.mem_filter, mem_roots hp] at hs ht
  obtain ⟨x, hx, hroot⟩ := exists_euler_sub_isRoot_between a hs.2 hst hs.1 ht.1
  refine ⟨x, ?_, hx⟩
  simp only [Multiset.mem_toFinset, Multiset.mem_filter, mem_roots hq]
  exact ⟨hroot, hs.2.trans hx.1⟩

/-- A nonzero natural-parameter Euler differential operator loses at most one
positive root, with roots counted according to multiplicity. -/
theorem card_pos_roots_le_euler_sub_add_one (p : ℝ[X]) (a : ℕ)
    (hq : X * p.derivative - C (a : ℝ) * p ≠ 0) :
    (p.roots.filter (0 < ·)).card ≤
      ((X * p.derivative - C (a : ℝ) * p).roots.filter (0 < ·)).card + 1 := by
  classical
  let s := p.roots.filter (0 < ·)
  let t := (X * p.derivative - C (a : ℝ) * p).roots.filter (0 < ·)
  have hcount (x : ℝ) : s.count x - 1 ≤ t.count x := by
    by_cases hx : 0 < x
    · simpa [s, t, hx] using p.rootMultiplicity_sub_one_le_euler_sub (a : ℝ) x hq
    · simp [s, t, hx]
  have hcard : s.toFinset.card ≤ (t.toFinset \ s.toFinset).card + 1 :=
    p.card_pos_roots_toFinset_le_euler_sub_sdiff_add_one a hq
  change s.card ≤ t.card + 1
  calc
    s.card = ∑ x ∈ s.toFinset, s.count x := (Multiset.toFinset_sum_count_eq _).symm
    _ = ∑ x ∈ s.toFinset, (s.count x - 1 + 1) :=
      (Eq.symm <| Finset.sum_congr rfl fun _ hx => tsub_add_cancel_of_le <|
        Nat.succ_le_iff.2 <| Multiset.count_pos.2 <| Multiset.mem_toFinset.1 hx)
    _ = (∑ x ∈ s.toFinset, (s.count x - 1)) + s.toFinset.card := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one]
    _ ≤ (∑ x ∈ s.toFinset, t.count x) + ((t.toFinset \ s.toFinset).card + 1) :=
      add_le_add (Finset.sum_le_sum fun x _ => hcount x) hcard
    _ ≤ (∑ x ∈ s.toFinset, t.count x) + ((∑ x ∈ t.toFinset \ s.toFinset,
        t.count x) + 1) := by
      simp only [Finset.card_eq_sum_ones]
      gcongr with x hx
      rw [Nat.succ_le_iff, Multiset.count_pos, ← Multiset.mem_toFinset]
      exact (Finset.mem_sdiff.1 hx).1
    _ = t.card + 1 := by
      rw [← add_assoc, ← Finset.sum_union Finset.disjoint_sdiff,
        Finset.union_sdiff_self_eq_union, ← Multiset.toFinset_sum_count_eq,
        ← Finset.sum_subset Finset.subset_union_right]
      intro x _ hx
      simpa only [Multiset.mem_toFinset, Multiset.count_eq_zero] using hx

end Polynomial
