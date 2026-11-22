/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
import RealRooted.Mathlib.Analysis.Polynomial.OrderedRootPerturbation
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Ordered root families with a prescribed error rate

A coefficient error rate near a fixed simple real-rooted reference polynomial
gives the same rate for the ordered roots. If the error tends to zero, one
chosen family of ordered roots converges coordinatewise. All root properties
are eventual; arbitrary earlier inputs require no splitting hypothesis.
-/

public section

open Filter Topology

namespace Polynomial

/-- A common coefficient error rate transfers to ordered roots near a fixed
simple split reference. The degree-zero case has an empty root family. -/
theorem eventually_exists_ordered_roots_le_mul
    {ι : Type*} {l : Filter ι} {Q : ι → ℝ[X]} {p : ℝ[X]} {n : ℕ}
    (hp : IsMonicOfDegree p n) (hps : p.Splits) (hpnd : p.roots.Nodup)
    (r : Fin n → ℝ) (hr : StrictMono r)
    (hfactor : p = ∏ j : Fin n, (X - C (r j)))
    (hdegree : ∀ᶠ t in l, (Q t).natDegree ≤ n)
    (hcoeff : ∀ k ≤ n, Tendsto (fun t ↦ (Q t).coeff k) l (𝓝 (p.coeff k)))
    {δ : ι → ℝ} (hδ : ∀ᶠ t in l, 0 ≤ δ t)
    (hbound : ∀ᶠ t in l, ∀ k ≤ n, |(Q t).coeff k - p.coeff k| ≤ δ t) :
    ∃ C > 0, ∀ᶠ t in l,
      (Q t).degree = n ∧ (Q t).Splits ∧ (Q t).roots.Nodup ∧
      ∃ s : Fin n → ℝ, StrictMono s ∧ (∀ i, (Q t).IsRoot (s i)) ∧
        ∀ i, |s i - r i| ≤ C * δ t := by
  obtain ⟨C, hC, hroots⟩ := eventually_exists_ordered_roots_abs_sub_le
    hp hps hpnd r hr hfactor hdegree hcoeff
  refine ⟨C, hC, ?_⟩
  filter_upwards [hroots, hδ, hbound] with t ht hδt hbt
  obtain ⟨hdeg, hsplit, hnodup, s, hsmono, hsroots, hsbound⟩ := ht
  exact ⟨hdeg, hsplit, hnodup, s, hsmono, hsroots, hsbound (δ t) hδt hbt⟩

/-- A vanishing coefficient error rate gives a single chosen family of
ordered roots with the same rate and coordinatewise convergence. -/
theorem exists_ordered_roots_tendsto_of_coeff_bound
    {ι : Type*} {l : Filter ι} {Q : ι → ℝ[X]} {p : ℝ[X]} {n : ℕ}
    (hp : IsMonicOfDegree p n) (hps : p.Splits) (hpnd : p.roots.Nodup)
    (r : Fin n → ℝ) (hr : StrictMono r)
    (hfactor : p = ∏ j : Fin n, (X - C (r j)))
    (hdegree : ∀ᶠ t in l, (Q t).natDegree ≤ n)
    (hcoeff : ∀ k ≤ n, Tendsto (fun t ↦ (Q t).coeff k) l (𝓝 (p.coeff k)))
    {δ : ι → ℝ} (hδ : ∀ᶠ t in l, 0 ≤ δ t)
    (hbound : ∀ᶠ t in l, ∀ k ≤ n, |(Q t).coeff k - p.coeff k| ≤ δ t)
    (hδlim : Tendsto δ l (𝓝 0)) :
    ∃ (s : ι → Fin n → ℝ) (C : ℝ), 0 < C ∧
      (∀ᶠ t in l, (Q t).degree = n ∧ (Q t).Splits ∧ (Q t).roots.Nodup ∧
        StrictMono (s t) ∧ (∀ i, (Q t).IsRoot (s t i)) ∧
        ∀ i, |s t i - r i| ≤ C * δ t) ∧
      ∀ i, Tendsto (fun t ↦ s t i) l (𝓝 (r i)) := by
  classical
  obtain ⟨C, hC, hroots⟩ := eventually_exists_ordered_roots_le_mul
    hp hps hpnd r hr hfactor hdegree hcoeff hδ hbound
  let P (t : ι) (s : Fin n → ℝ) : Prop := StrictMono s ∧
    (∀ i, (Q t).IsRoot (s i)) ∧ ∀ i, |s i - r i| ≤ C * δ t
  let s (t : ι) : Fin n → ℝ := if h : ∃ y, P t y then Classical.choose h else r
  have hselected (t : ι) (h : ∃ y, P t y) : P t (s t) := by
    dsimp only [s]
    rw [dite_eq_left h]
    exact Classical.choose_spec h
  have hevent : ∀ᶠ t in l,
      (Q t).degree = n ∧ (Q t).Splits ∧ (Q t).roots.Nodup ∧ P t (s t) := by
    filter_upwards [hroots] with t ht
    exact ⟨ht.1, ht.2.1, ht.2.2.1, hselected t ht.2.2.2⟩
  refine ⟨s, C, hC, hevent, ?_⟩
  intro i
  have hlim : Tendsto (fun t ↦ C * δ t) l (𝓝 0) := by
    simpa only [mul_zero] using hδlim.const_mul C
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [hevent, hlim.eventually (gt_mem_nhds hε)] with t ht hsmall
  rw [Real.dist_eq]
  exact (ht.2.2.2.2.2 i).trans_lt hsmall

end Polynomial
