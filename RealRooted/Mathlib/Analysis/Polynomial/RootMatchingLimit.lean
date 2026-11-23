/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import TauCeti.Analysis.Polynomial.ContinuityOfRoots.Basic

import Mathlib.Tactic.TypeStar

/-!
# Root matching along coefficientwise limits

This is the filter form of the existing Tau Ceti coefficient-neighborhood
theorem, including multiplicities and degree zero.
-/

public section

open Filter Metric Topology

namespace Polynomial

variable {K : Type*} [NormedField K] [IsAlgClosed K] [ProperSpace K]
  {ι : Type*} {l : Filter ι} {P : ι → K[X]} {Q : K[X]}

/-- Fixed-degree monic coefficient convergence matches all roots, counting
multiplicity, eventually within any prescribed positive distance. -/
theorem eventually_rel_roots_of_coeff_tendsto
    (hQ : Q.Monic) (hP : ∀ᶠ i in l, (P i).Monic ∧ (P i).natDegree = Q.natDegree)
    (hcoeff : ∀ k < Q.natDegree,
      Tendsto (fun i ↦ (P i).coeff k) l (𝓝 (Q.coeff k)))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ i in l, Q.roots.Rel (fun z w ↦ ‖z - w‖ < ε) (P i).roots := by
  obtain ⟨δ, hδ, hclose⟩ := hQ.exists_rel_roots_norm_sub_lt hε
  have hev : ∀ᶠ i in l, ∀ k : Fin Q.natDegree,
      ‖(P i).coeff k - Q.coeff k‖ < δ := by
    apply eventually_all.mpr
    intro k
    have hk : Tendsto (fun i ↦ ‖(P i).coeff k - Q.coeff k‖) l (𝓝 0) := by
      simpa only [sub_self, norm_zero] using
        ((hcoeff k k.is_lt).sub (tendsto_const_nhds (x := Q.coeff k))).norm
    exact hk.eventually_lt tendsto_const_nhds hδ
  filter_upwards [hP, hev] with i hi hci
  exact hclose (P i) hi.1 hi.2 fun k hk ↦ hci ⟨k, hk⟩

open scoped Classical in
/-- In disjoint root neighborhoods, coefficient convergence preserves the
total number of roots in each neighborhood, including multiplicities. -/
theorem eventually_countP_roots_eq_of_coeff_tendsto
    (hQ : Q.Monic) (hP : ∀ᶠ i in l, (P i).Monic ∧ (P i).natDegree = Q.natDegree)
    (hcoeff : ∀ k < Q.natDegree,
      Tendsto (fun i ↦ (P i).coeff k) l (𝓝 (Q.coeff k)))
    {ε : ℝ} (hε : 0 < ε)
    (hsep : ∀ z ∈ Q.roots, ∀ w ∈ Q.roots, z ≠ w → 2 * ε ≤ ‖z - w‖) :
    ∀ᶠ i in l,
      (∀ z ∈ Q.roots, (P i).roots.countP (· ∈ ball z ε) = Q.rootMultiplicity z) ∧
        ∀ w ∈ (P i).roots, ∃ z ∈ Q.roots, ‖w - z‖ < ε := by
  exact (eventually_rel_roots_of_coeff_tendsto hQ hP hcoeff hε).mono
    fun _ h ↦ (rel_roots_iff_countP_roots_mem_ball hsep).mp h

end Polynomial
