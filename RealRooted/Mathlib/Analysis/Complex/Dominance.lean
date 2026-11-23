/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Analytic.Basic
import Mathlib.Topology.GDelta.Basic
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.AbsMax

/-!
# Nondegenerate dominance of analytic functions

We use Sokal's no-degenerate-dominance condition: two distinct bases that are globally unit
multiples cannot dominate on a nonempty open subset. Unique dominance, with nonzero bases
and coefficients, is dense under this condition. The condition permits proportional bases
which never dominate on an open subset.

Reference: A. D. Sokal, *Chromatic roots are dense in the whole complex plane*,
arXiv:cond-mat/0012369v3, Theorem 1.5 and the proof of Theorem 3.2.
-/

@[expose] public section

open Filter Topology Metric Set

namespace Complex

/-- Sokal's no-degenerate-dominance condition for a finite analytic exponential sum.
A pair of distinct globally unimodular-proportional bases has no open dominance region. -/
def HasNondegenerateDominance {κ : Type*} (s : Finset κ) (β : κ → ℂ → ℂ)
    (D : Set ℂ) : Prop :=
  ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ∀ ω : ℂ, ‖ω‖ = 1 →
    EqOn (β i) (fun z => ω * β j z) D →
    interior {z | z ∈ D ∧ ∀ k ∈ s, ‖β k z‖ ≤ ‖β i z‖} = ∅

end Complex

/-- A nonzero analytic function on a connected domain is nonzero somewhere in every nonempty
open subset of the domain. -/
theorem AnalyticOnNhd.exists_ne_zero_on_open {f : ℂ → ℂ} {D V : Set ℂ}
    (hf : AnalyticOnNhd ℂ f D) (hD : IsPreconnected D)
    (hne : ∃ z ∈ D, f z ≠ 0) (hV : IsOpen V) (hVD : V ⊆ D) (hVne : V.Nonempty) :
    ∃ z ∈ V, f z ≠ 0 := by
  by_contra h
  push Not at h
  obtain ⟨z, hz⟩ := hVne
  have heq : ∀ᶠ w in 𝓝 z, f w = 0 := by
    filter_upwards [hV.mem_nhds hz] with w hw
    exact h w hw
  obtain ⟨w, hw, hfw⟩ := hne
  exact hfw (hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero hD (hVD hz) heq hw)

namespace Complex

/-- Two analytic functions with equal modulus on an open subset of a connected domain are
unit multiples throughout the domain, provided the second function is not identically zero. -/
theorem exists_norm_eq_one_eqOn_mul {f g : ℂ → ℂ} {D V : Set ℂ}
    (hf : AnalyticOnNhd ℂ f D) (hg : AnalyticOnNhd ℂ g D) (hD : IsPreconnected D)
    (hgne : ∃ z ∈ D, g z ≠ 0) (hV : IsOpen V) (hVD : V ⊆ D) (hVne : V.Nonempty)
    (heq : ∀ z ∈ V, ‖f z‖ = ‖g z‖) :
    ∃ ω : ℂ, ‖ω‖ = 1 ∧ EqOn f (fun z => ω * g z) D := by
  obtain ⟨w, hw, hgw⟩ := hg.exists_ne_zero_on_open hD hgne hV hVD hVne
  have hev : ∀ᶠ z in 𝓝 w, z ∈ V ∧ g z ≠ 0 :=
    Filter.Eventually.and (hV.mem_nhds hw)
      ((hg w (hVD hw)).continuousAt.eventually_ne hgw)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hev
  have hnorm : ∀ z ∈ ball w r, ‖f z / g z‖ = 1 := by
    intro z hz
    rw [norm_div, heq z (hball hz).1, div_self (norm_ne_zero_iff.mpr (hball hz).2)]
  have hd : DifferentiableOn ℂ (fun z => f z / g z) (ball w r) := by
    intro z hz
    exact ((hf z (hVD (hball hz).1)).div (hg z (hVD (hball hz).1))
      (hball hz).2).differentiableAt.differentiableWithinAt
  have hc := eqOn_of_isPreconnected_of_isMaxOn_norm (convex_ball w r).isPreconnected
    isOpen_ball hd (mem_ball_self hr) (fun z hz => by
      change ‖f z / g z‖ ≤ ‖f w / g w‖
      rw [hnorm z hz, hnorm w (mem_ball_self hr)])
  refine ⟨f w / g w, hnorm w (mem_ball_self hr), ?_⟩
  apply hf.eqOn_of_preconnected_of_eventuallyEq
    (analyticOnNhd_const.mul hg) hD (hVD hw)
  filter_upwards [ball_mem_nhds w hr] with z hz
  exact (div_eq_iff (hball hz).2).mp (hc hz)

/-- The complement of the zero set of a nonzero analytic function is dense in its open,
connected domain. -/
private theorem dense_ne_zero {f : ℂ → ℂ} {D : Set ℂ} (hDo : IsOpen D)
    (hDc : IsPreconnected D) (hf : AnalyticOnNhd ℂ f D) (hne : ∃ z ∈ D, f z ≠ 0) :
    Dense {z : D | f z ≠ 0} := by
  refine dense_iff_inter_open.mpr fun V hV hVne => ?_
  have ho : IsOpen ((Subtype.val : D → ℂ) '' V) := hDo.isOpenMap_subtype_val _ hV
  obtain ⟨z, ⟨w, hw, rfl⟩, hfw⟩ := hf.exists_ne_zero_on_open hDc hne ho
    (by rintro _ ⟨w, _, rfl⟩; exact w.2) (hVne.image _)
  exact ⟨w, hw, hfw⟩

/-- The set on which a prescribed pair of distinct bases both dominate is nowhere dense
in a nondegenerate analytic family. -/
private theorem nowhereDense_two_dominant {κ : Type*} (s : Finset κ) (β : κ → ℂ → ℂ)
    {D : Set ℂ} (hDo : IsOpen D) (hDc : IsPreconnected D)
    (hβ : ∀ k ∈ s, AnalyticOnNhd ℂ (β k) D)
    (hβne : ∀ k ∈ s, ∃ z ∈ D, β k z ≠ 0)
    (hnd : HasNondegenerateDominance s β D) {i j : κ}
    (hi : i ∈ s) (hj : j ∈ s) (hij : i ≠ j) :
    IsNowhereDense {z : D | (∀ k ∈ s, ‖β k z‖ ≤ ‖β i z‖) ∧
      (∀ k ∈ s, ‖β k z‖ ≤ ‖β j z‖)} := by
  let T : Set D := {z | (∀ k ∈ s, ‖β k z‖ ≤ ‖β i z‖) ∧
    (∀ k ∈ s, ‖β k z‖ ≤ ‖β j z‖)}
  have hcont : ∀ k ∈ s, Continuous (fun z : D => ‖β k z‖) :=
    fun k hk => ((hβ k hk).continuousOn.norm).domRestrict
  have hc : IsClosed T := by
    have hclosed : ∀ l ∈ s, IsClosed {z : D | ∀ k ∈ s, ‖β k z‖ ≤ ‖β l z‖} := by
      intro l hl
      simp only [ofPred_forall]
      exact isClosed_iInter fun k => isClosed_iInter fun hk =>
        isClosed_le (hcont k hk) (hcont l hl)
    exact (hclosed i hi).inter (hclosed j hj)
  apply hc.isNowhereDense_iff.mpr
  apply eq_empty_iff_forall_notMem.mpr
  intro x hx
  let V : Set ℂ := (Subtype.val : D → ℂ) '' interior T
  have ho : IsOpen V := hDo.isOpenMap_subtype_val _ isOpen_interior
  have hVD : V ⊆ D := by rintro _ ⟨z, _, rfl⟩; exact z.2
  have hdom : ∀ z ∈ V, (∀ k ∈ s, ‖β k z‖ ≤ ‖β i z‖) ∧
      (∀ k ∈ s, ‖β k z‖ ≤ ‖β j z‖) := by
    rintro _ ⟨z, hz, rfl⟩
    exact interior_subset hz
  obtain ⟨ω, hω, heq⟩ := exists_norm_eq_one_eqOn_mul (hβ i hi) (hβ j hj) hDc
    (hβne j hj) ho hVD ⟨x, x, hx, rfl⟩
    (fun z hz => le_antisymm ((hdom z hz).2 i hi) ((hdom z hz).1 j hj))
  have hsub : V ⊆ interior {z | z ∈ D ∧ ∀ k ∈ s, ‖β k z‖ ≤ ‖β i z‖} :=
    interior_maximal (fun z hz => ⟨hVD hz, (hdom z hz).1⟩) ho
  have hfalse := hsub (show (x : ℂ) ∈ V from ⟨x, hx, rfl⟩)
  simp only [hnd i hi j hj hij ω hω heq, mem_empty_iff_false] at hfalse

/-- In a finite nondegenerate analytic family on an open connected domain, points where
exactly one base dominates and its coefficient and base are nonzero form a dense set. -/
theorem HasNondegenerateDominance.dense_unique_dominant {κ : Type*}
    (s : Finset κ) (α β : κ → ℂ → ℂ) {D : Set ℂ}
    (hDo : IsOpen D) (hDc : IsPreconnected D) (hs : s.Nonempty)
    (hα : ∀ k ∈ s, AnalyticOnNhd ℂ (α k) D)
    (hβ : ∀ k ∈ s, AnalyticOnNhd ℂ (β k) D)
    (hαne : ∀ k ∈ s, ∃ z ∈ D, α k z ≠ 0)
    (hβne : ∀ k ∈ s, ∃ z ∈ D, β k z ≠ 0)
    (hnd : HasNondegenerateDominance s β D) :
    Dense {z : D | ∃ i ∈ s, α i z ≠ 0 ∧ β i z ≠ 0 ∧
      ∀ k ∈ s, k ≠ i → ‖β k z‖ < ‖β i z‖} := by
  classical
  let t := (s.product s).filter fun ij => ij.1 ≠ ij.2
  let T : κ × κ → Set D := fun ij =>
    {z | (∀ k ∈ s, ‖β k z‖ ≤ ‖β ij.1 z‖) ∧
      (∀ k ∈ s, ‖β k z‖ ≤ ‖β ij.2 z‖)}
  let Z : κ → Set D := fun k => {z | α k z = 0} ∪ {z | β k z = 0}
  have hT : ∀ ij ∈ t, IsNowhereDense (T ij) := by
    intro ij hij
    obtain ⟨hmem, hne⟩ := Finset.mem_filter.mp hij
    obtain ⟨hi, hj⟩ := Finset.mem_product.mp hmem
    exact nowhereDense_two_dominant s β hDo hDc hβ hβne hnd hi hj hne
  have hZ : ∀ k ∈ s, IsNowhereDense (Z k) := by
    intro k hk
    have hzero : ∀ (f : ℂ → ℂ), AnalyticOnNhd ℂ f D → (∃ z ∈ D, f z ≠ 0) →
        IsNowhereDense {z : D | f z = 0} := by
      intro f hf hne
      have hfc : Continuous (fun z : D => f z) := hf.continuousOn.domRestrict
      apply (isClosed_eq hfc continuous_const).isNowhereDense_iff.mpr
      apply interior_eq_empty_iff_dense_compl.mpr
      simpa only [compl_ofPred] using dense_ne_zero hDo hDc hf hne
    exact (hzero (α k) (hα k hk) (hαne k hk)).union
      (hzero (β k) (hβ k hk) (hβne k hk))
  have hbad := (IsNowhereDense.biUnion hT).union (IsNowhereDense.biUnion hZ)
  have hdense : Dense ((⋃ ij ∈ t, T ij) ∪ (⋃ k ∈ s, Z k))ᶜ :=
    interior_eq_empty_iff_dense_compl.mp
      (Set.eq_empty_of_subset_empty (hbad ▸ interior_mono subset_closure))
  apply hdense.mono
  intro z hz
  obtain ⟨i, hi, himax⟩ := s.exists_max_image (fun k => ‖β k z‖) hs
  have hnz : ∀ k ∈ s, α k z ≠ 0 ∧ β k z ≠ 0 := by
    intro k hk
    constructor
    · intro h
      exact hz (Or.inr (mem_iUnion₂.mpr ⟨k, hk, Or.inl h⟩))
    · intro h
      exact hz (Or.inr (mem_iUnion₂.mpr ⟨k, hk, Or.inr h⟩))
  refine ⟨i, hi, (hnz i hi).1, (hnz i hi).2, fun k hk hki => ?_⟩
  apply lt_of_le_of_ne (himax k hk)
  intro heq
  apply hz
  left
  refine mem_iUnion₂.mpr ⟨(k, i), Finset.mem_filter.mpr
    ⟨Finset.mem_product.mpr ⟨hk, hi⟩, hki⟩, ?_⟩
  exact ⟨fun l hl => (himax l hl).trans_eq heq.symm, himax⟩

end Complex
