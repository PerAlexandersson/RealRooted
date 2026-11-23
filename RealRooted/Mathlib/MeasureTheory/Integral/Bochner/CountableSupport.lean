/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import RealRooted.Mathlib.MeasureTheory.Integral.Bochner.Countable

/-!
# Atomic integral sums indexed by the ambient space

A measure carried by a countable set has an integral expansion over all points
of the ambient space. Every summand off the carrying set is zero. This avoids
introducing an enumeration or a nonempty index assumption.
-/

public section

namespace MeasureTheory

/-- A measure carried by a countable set integrates by the sum of its atoms,
indexed over the whole ambient space. The ambient space need not be countable. -/
theorem hasSum_integral_of_ae_mem_countable_ambient
    {X E : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {mu : Measure X} {f : X → E} {s : Set X} (hs : s.Countable)
    (hmu : ∀ᵐ x ∂mu, x ∈ s) (hf : Integrable f mu) :
    HasSum (fun x : X ↦ mu.real {x} • f x) (∫ x, f x ∂mu) := by
  have hsupp : Function.support (fun x : X ↦ mu.real {x} • f x) ⊆ s := by
    intro x hx
    by_contra hxs
    have hmass : mu {x} = 0 :=
      measure_mono_null (Set.singleton_subset_iff.mpr hxs) (ae_iff.mp hmu)
    exact hx (by simp [measureReal_def, hmass])
  exact (hasSum_subtype_iff_of_support_subset hsupp).mp
    (hasSum_integral_of_ae_mem_countable hs hmu hf)

end MeasureTheory
