/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.Analysis.Complex.Norm
import RealRooted.Mathlib.Analysis.Polynomial.RootMatchingLimit
import RealRooted.Mathlib.Algebra.Polynomial.Splits.Complex
import Mathlib.Analysis.Complex.Polynomial.Basic

import Mathlib.Tactic.TypeStar

/-!
# Persistence of nonreal roots under coefficientwise convergence
-/

public section

open Filter Topology

namespace Polynomial

/-- Root matching at every positive radius preserves a nonreal root of a
nonzero limit, without degree or simplicity assumptions on the approximants. -/
theorem eventually_not_splits_of_eventually_rel_roots
    {ι : Type*} {l : Filter ι} {P : ι → ℝ[X]} {Q : ℝ[X]} (hQ : Q ≠ 0)
    (hnonsplit : ¬ Q.Splits)
    (hrel : ∀ ε > 0, ∀ᶠ i in l,
      (Q.map Complex.ofRealHom).roots.Rel (fun z w ↦ ‖z - w‖ < ε)
        ((P i).map Complex.ofRealHom).roots) :
    ∀ᶠ i in l, ¬ (P i).Splits := by
  have hex : ∃ z : ℂ, (Q.map Complex.ofRealHom).eval z = 0 ∧ z.im ≠ 0 := by
    by_contra h
    apply hnonsplit
    apply splits_of_all_roots_real
    intro z hz
    by_contra hi
    exact h ⟨z, hz, hi⟩
  obtain ⟨z, hz, hzi⟩ := hex
  have hzroot : z ∈ (Q.map Complex.ofRealHom).roots :=
    (mem_roots (map_ne_zero hQ)).mpr hz
  have hmatch := hrel |z.im| (abs_pos.mpr hzi)
  filter_upwards [hmatch] with i hi hsplit
  obtain ⟨w, hw, hzw⟩ := Multiset.exists_mem_of_rel_of_mem hi hzroot
  rw [hsplit.roots_map Complex.ofRealHom] at hw
  obtain ⟨r, _, rfl⟩ := Multiset.mem_map.mp hw
  have hle : |z.im| ≤ ‖z - Complex.ofRealHom r‖ := by
    simpa only [Complex.sub_im, Complex.ofRealHom_eq_coe, Complex.ofReal_im, sub_zero] using
      Complex.abs_im_le_norm (z - Complex.ofRealHom r)
  exact (not_lt_of_ge hle) hzw

/-- A nonreal root of a monic limit persists along fixed-degree monic
coefficient convergence. The source need not have simple roots. -/
theorem eventually_not_splits_of_coeff_tendsto
    {ι : Type*} {l : Filter ι} {P : ι → ℝ[X]} {Q : ℝ[X]} (hQ : Q.Monic)
    (hP : ∀ᶠ i in l, (P i).Monic ∧ (P i).natDegree = Q.natDegree)
    (hcoeff : ∀ k < Q.natDegree,
      Tendsto (fun i ↦ (P i).coeff k) l (𝓝 (Q.coeff k)))
    (hnonsplit : ¬ Q.Splits) : ∀ᶠ i in l, ¬ (P i).Splits := by
  apply eventually_not_splits_of_eventually_rel_roots hQ.ne_zero hnonsplit
  intro ε hε
  exact eventually_rel_roots_of_coeff_tendsto
    (hQ.map Complex.ofRealHom)
    (hP.mono fun i hi ↦ ⟨hi.1.map Complex.ofRealHom,
      by simpa only [natDegree_map] using hi.2⟩)
    (fun k hk ↦ by
      have hk' : k < Q.natDegree := by simpa only [natDegree_map] using hk
      simpa only [coeff_map, Complex.ofRealHom_eq_coe, Function.comp_def] using
        (Complex.continuous_ofReal.tendsto _).comp (hcoeff k hk')) hε

end Polynomial
