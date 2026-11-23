/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

import Mathlib.Topology.MetricSpace.Algebra
public import Mathlib.Analysis.Normed.Ring.Basic
import RealRooted.Mathlib.Topology.Algebra.IsUniformGroup.FiniteSum
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.Normed.MulAction
import Mathlib.Topology.Algebra.Monoid

/-!
# Finite products of locally uniformly convergent families
-/

public section

open Filter

/-- Finite multiset products preserve locally uniform convergence when the
limit factors are continuous. Repeated factors are retained. -/
theorem TendstoLocallyUniformly.multiset_prod {ι X M A : Type*} [TopologicalSpace X]
    [NormedCommRing M] (s : Multiset A) {F : A → ι → X → M} {f : A → X → M}
    {l : Filter ι} (hF : ∀ a ∈ s, TendstoLocallyUniformly (F a) (f a) l)
    (hf : ∀ a ∈ s, Continuous (f a)) :
    TendstoLocallyUniformly (fun n x ↦ (s.map fun a ↦ F a n x).prod)
      (fun x ↦ (s.map fun a ↦ f a x).prod) l := by
  revert hF hf
  induction s using Multiset.induction_on with
  | empty =>
      intro _ _
      simpa only [Multiset.map_zero, Multiset.prod_zero] using
        tendstoLocallyUniformly_const_family (fun _ : X ↦ (1 : M)) l
  | cons a s ih =>
      intro hF hf
      have hFs := ih (fun b hb ↦ hF b (Multiset.mem_cons_of_mem hb))
        (fun b hb ↦ hf b (Multiset.mem_cons_of_mem hb))
      have hcs : Continuous (fun x ↦ (s.map fun b ↦ f b x).prod) :=
        continuous_multiset_prod s (fun b hb ↦ hf b (Multiset.mem_cons_of_mem hb))
      simpa only [Multiset.map_cons, Multiset.prod_cons, Pi.mul_def] using
        (hF a (Multiset.mem_cons_self a s)).mul₀ hFs
          (hf a (Multiset.mem_cons_self a s)) hcs
