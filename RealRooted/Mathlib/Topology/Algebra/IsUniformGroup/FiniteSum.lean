/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
public import Mathlib.Topology.Algebra.IsUniformGroup.Defs
import Mathlib.Topology.Algebra.IsUniformGroup.Basic

/-!
# Finite sums of locally uniformly convergent families
-/

public section

open Filter

/-- A constant family converges locally uniformly to that same function. -/
theorem tendstoLocallyUniformly_const_family {ι X E : Type*} [TopologicalSpace X]
    [UniformSpace E] (f : X → E) (l : Filter ι) :
    TendstoLocallyUniformly (fun _ : ι => f) f l := by
  intro u hu x
  exact ⟨Set.univ, univ_mem, Eventually.of_forall fun _ _ _ => refl_mem_uniformity hu⟩

/-- Finite sums preserve locally uniform convergence. -/
theorem TendstoLocallyUniformly.finset_sum {ι X E A : Type*} [TopologicalSpace X]
    [AddCommGroup E] [UniformSpace E] [IsUniformAddGroup E] (s : Finset A)
    {F : A → ι → X → E} {f : A → X → E} {l : Filter ι}
    (h : ∀ a ∈ s, TendstoLocallyUniformly (F a) (f a) l) :
    TendstoLocallyUniformly (fun n x => ∑ a ∈ s, F a n x) (fun x => ∑ a ∈ s, f a x) l := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using tendstoLocallyUniformly_const_family (fun _ : X => (0 : E)) l
  | @insert a s ha ih =>
      simpa only [Finset.sum_insert ha, Pi.add_def] using
        (h a (Finset.mem_insert_self a s)).add
          (ih fun b hb => h b (Finset.mem_insert_of_mem hb))
