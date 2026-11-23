/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.Separable
import RealRooted.Mathlib.Analysis.Polynomial.RootMatchingLimit
import TauCeti.Topology.MetricSpace.SeparatedBalls
import Mathlib.Tactic.TypeStar

/-!+# Separability along fixed-degree coefficient limits

A simple limiting root has exactly one nearby root, counting multiplicity.
Consequently separability persists under fixed-degree monic coefficient limits.
The limiting polynomial may be constant.
-/

public section

open Filter Metric Topology

namespace Polynomial

/-- A separable monic coefficient limit forces eventual separability when
the monic approximants have the same degree. -/
theorem eventually_separable_of_coeff_tendsto
    {K : Type*} [NormedField K] [IsAlgClosed K] [ProperSpace K]
    {ι : Type*} {l : Filter ι} {P : ι → K[X]} {Q : K[X]}
    (hQ : Q.Monic) (hsep : Q.Separable)
    (hP : ∀ᶠ i in l, (P i).Monic ∧ (P i).natDegree = Q.natDegree)
    (hcoeff : ∀ k < Q.natDegree,
      Tendsto (fun i ↦ (P i).coeff k) l (𝓝 (Q.coeff k))) :
    ∀ᶠ i in l, (P i).Separable := by
  classical
  obtain ⟨ε, hε, _, hdist⟩ := TauCeti.exists_pos_closedBall_subset_and_lt_dist
    (T := Q.roots.toFinset) (U := fun _ ↦ Set.univ) (fun _ _ ↦ Filter.univ_mem)
  have hballs := eventually_countP_roots_eq_of_coeff_tendsto hQ hP hcoeff hε
    (fun z hz w hw hzw ↦ by
      simpa only [dist_eq_norm] using
        (hdist z (Multiset.mem_toFinset.mpr hz) w (Multiset.mem_toFinset.mpr hw) hzw).le)
  filter_upwards [hP, hballs] with i hi hbi
  apply (nodup_roots_iff_of_splits hi.1.ne_zero (IsAlgClosed.splits _)).mp
  apply Multiset.nodup_iff_count_le_one.mpr
  intro w
  by_cases hw : w ∈ (P i).roots
  · obtain ⟨z, hz, hwz⟩ := hbi.2 w hw
    have hmem : w ∈ ball z ε := by simpa only [mem_ball, dist_eq_norm] using hwz
    calc
      (P i).roots.count w = ((P i).roots.filter (· ∈ ball z ε)).count w :=
        (Multiset.count_filter_of_pos hmem).symm
      _ ≤ ((P i).roots.filter (· ∈ ball z ε)).card := Multiset.count_le_card _ _
      _ = Q.rootMultiplicity z := by rw [← Multiset.countP_eq_card_filter, hbi.1 z hz]
      _ ≤ 1 := rootMultiplicity_le_one_of_separable hsep z
  · simp only [Multiset.count_eq_zero_of_notMem hw, Nat.zero_le]

end Polynomial
