/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import Mathlib.Topology.MetricSpace.Pseudo.Defs

public import Mathlib.Algebra.Polynomial.Splits

import TauCeti.Analysis.Polynomial.RealRoots.Basic
import Mathlib.Algebra.Polynomial.OfFn
public import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.Tactic.Linarith

/-!
# Coefficient neighborhoods of simple real-rooted polynomials


The existing Tau Ceti root-matching theorem is applied to the finite coefficient
space. At a simple split reference polynomial its complex-root-count assumption
is automatic from the degree bound.
-/

public section

open Filter Topology

noncomputable section

namespace Polynomial

/-- A coefficient neighborhood of a simple split monic polynomial has the same
degree and simple real roots, matched bijectively with the reference roots. -/
theorem exists_coeff_radius_roots_bijection {p : ℝ[X]} {n : ℕ}
    (hp : IsMonicOfDegree p n) (hps : p.Splits) (hpnd : p.roots.Nodup)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ q : ℝ[X], q.natDegree ≤ n →
      (∀ k ≤ n, |q.coeff k - p.coeff k| < δ) →
      q.degree = n ∧ q.Splits ∧ q.roots.Nodup ∧
      ∃ e : ℝ → ℝ, Set.BijOn e p.roots.toFinset q.roots.toFinset ∧
        ∀ x ∈ p.roots, |e x - x| < ε ∧
          q.rootMultiplicity (e x) = p.rootMultiplicity x := by
  let F : (Fin (n + 1) → ℝ) → ℝ[X] := fun v => ofFn (n + 1) v
  let v₀ : Fin (n + 1) → ℝ := fun i => p.coeff i.val
  have hbase : F v₀ = p := by
    change ofFn (n + 1) (toFn (n + 1) p) = p
    apply ofFn_comp_toFn_eq_id_of_natDegree_lt
    rw [hp.natDegree_eq]
    exact Nat.lt_succ_self n
  have hF (k : ℕ) (hk : k ≤ n) : ContinuousAt (fun v => (F v).coeff k) v₀ := by
    simpa only [F, ofFn_coeff_eq_val_of_lt _ (Nat.lt_succ_of_le hk)] using
      (continuous_apply (⟨k, Nat.lt_succ_of_le hk⟩ : Fin (n + 1))).continuousAt
  have hbound (v : Fin (n + 1) → ℝ) : (F v).natDegree ≤ n :=
    Nat.le_of_lt_succ (ofFn_natDegree_lt (Nat.succ_pos n) v)
  have htop : (F v₀).coeff n ≠ 0 := by
    rw [hbase, ← hp.natDegree_eq, hp.monic.coeff_natDegree]
    exact one_ne_zero
  have hdegree : ∀ᶠ v in 𝓝 v₀, (F v).degree = n := by
    filter_upwards [(hF n le_rfl).eventually_ne htop] with v hv
    exact degree_eq_of_le_of_coeff_ne_zero (degree_le_of_natDegree_le (hbound v)) hv
  have hpC : (p.aroots ℂ).Nodup := by
    rw [aroots_def, hps.roots_map (algebraMap ℝ ℂ)]
    exact Multiset.Nodup.map (algebraMap ℝ ℂ).injective hpnd
  have hcard₀ : ((F v₀).aroots ℂ).toFinset.card = n := by
    rw [hbase, Multiset.toFinset_card_of_nodup hpC, aroots_def,
      hps.roots_map (algebraMap ℝ ℂ), Multiset.card_map,
      ← hps.natDegree_eq_card_roots, hp.natDegree_eq]
  have hcard : ∀ᶠ v in 𝓝 v₀,
      ((F v).aroots ℂ).toFinset.card ≤ ((F v₀).aroots ℂ).toFinset.card := by
    apply Filter.Eventually.of_forall
    intro v
    rw [hcard₀, aroots_def]
    calc
      ((F v).map (algebraMap ℝ ℂ)).roots.toFinset.card ≤
          ((F v).map (algebraMap ℝ ℂ)).roots.card := Multiset.toFinset_card_le _
      _ ≤ ((F v).map (algebraMap ℝ ℂ)).natDegree := card_roots' _
      _ ≤ n := by rw [natDegree_map]; exact hbound v
  have hmatch := eventually_exists_bijOn_roots_toFinset_of_card_aroots_le
    hF hdegree hcard hε
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp (hdegree.and hmatch)
  refine ⟨δ, hδ, ?_⟩
  intro q hq hcoeff
  let v : Fin (n + 1) → ℝ := fun i => q.coeff i.val
  have hqF : F v = q := by
    change ofFn (n + 1) (toFn (n + 1) q) = q
    exact ofFn_comp_toFn_eq_id_of_natDegree_lt (Nat.lt_succ_of_le hq)
  have hv : dist v v₀ < δ := by
    apply (dist_pi_lt_iff hδ).mpr
    intro i
    simpa only [Real.dist_eq] using hcoeff i.val (Nat.le_of_lt_succ i.is_lt)
  obtain ⟨hqdegree, e, he, heclose⟩ := hball (y := v) hv
  rw [hqF] at hqdegree
  rw [hbase, hqF] at he heclose
  have hcardp : p.roots.toFinset.card = n := by
    rw [Multiset.toFinset_card_of_nodup hpnd, ← hps.natDegree_eq_card_roots,
      hp.natDegree_eq]
  have hcardq : q.roots.toFinset.card = n := by
    rw [← Finset.card_nbij e he.mapsTo he.injOn he.surjOn, hcardp]
  have hrootcount := card_roots' q
  have hsetcount := Multiset.toFinset_card_le q.roots
  have hqn : q.roots.card = q.natDegree := by lia
  have hqnodup : q.roots.Nodup :=
    Multiset.toFinset_card_eq_card_iff_nodup.mp (by lia)
  exact ⟨hqdegree, splits_iff_card_roots.mpr hqn, hqnodup, e, he, heclose⟩

/-- Finite coefficient convergence to a simple split monic polynomial gives
eventual real-root matching without any nearby real-rootedness assumption. -/
theorem eventually_roots_bijection_of_coeff_tendsto
    {ι : Type*} {l : Filter ι} {Q : ι → ℝ[X]} {p : ℝ[X]} {n : ℕ}
    (hp : IsMonicOfDegree p n) (hps : p.Splits) (hpnd : p.roots.Nodup)
    (hdegree : ∀ᶠ t in l, (Q t).natDegree ≤ n)
    (hcoeff : ∀ k ≤ n, Tendsto (fun t => (Q t).coeff k) l (𝓝 (p.coeff k)))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t in l, (Q t).degree = n ∧ (Q t).Splits ∧ (Q t).roots.Nodup ∧
      ∃ e : ℝ → ℝ, Set.BijOn e p.roots.toFinset (Q t).roots.toFinset ∧
        ∀ x ∈ p.roots, |e x - x| < ε ∧
          (Q t).rootMultiplicity (e x) = p.rootMultiplicity x := by
  obtain ⟨δ, hδ, hmatch⟩ := exists_coeff_radius_roots_bijection hp hps hpnd hε
  have hclose : ∀ᶠ t in l, ∀ i : Fin (n + 1),
      |(Q t).coeff i.val - p.coeff i.val| < δ := by
    apply eventually_all.mpr
    intro i
    have hi : Tendsto (fun t => |(Q t).coeff i.val - p.coeff i.val|) l (𝓝 0) := by
      simpa only [sub_self, abs_zero] using
        ((hcoeff i.val (Nat.le_of_lt_succ i.is_lt)).sub
          (tendsto_const_nhds (x := p.coeff i.val))).abs
    exact hi.eventually_lt tendsto_const_nhds hδ
  filter_upwards [hdegree, hclose] with t ht htc
  apply hmatch (Q t) ht
  intro k hk
  exact htc ⟨k, Nat.lt_succ_of_le hk⟩

end Polynomial
