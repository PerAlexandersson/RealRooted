/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.MeasureTheory.Measure.Dirac.Basic
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Atomic measures on an injective countable range

A measure carried by an injective countable family is the sum of its singleton
masses. A distinguished atom can be separated from the remaining family.
No finiteness assumption on the measure is needed.
-/

public section

open Set

namespace MeasureTheory.Measure

/-- The singleton masses along any injective family are summable for a finite
measure. The index type need not be countable. -/
theorem summable_measureReal_singleton_comp {ι X : Type*}
    [MeasurableSpace X] [MeasurableSingletonClass X] (mu : Measure X)
    [IsFiniteMeasure mu] {a : ι → X} (hi : Function.Injective a) :
    Summable (fun i ↦ mu.real {a i}) := by
  apply summable_of_sum_le (c := mu.real univ) (fun _ ↦ measureReal_nonneg)
  intro s
  apply sum_measureReal_le_measureReal_univ (fun _ _ ↦ measurableSet_singleton _)
  intro i _ j _ hij
  exact disjoint_singleton.mpr (fun h ↦ hij (hi h))

/-- Restricting to an injective countable range is the sum of the corresponding
weighted Dirac measures. -/
theorem restrict_range_eq_sum_smul_dirac {ι X : Type*} [Countable ι]
    [MeasurableSpace X] [MeasurableSingletonClass X] (mu : Measure X)
    {a : ι → X} (hi : Function.Injective a) :
    mu.restrict (range a) = Measure.sum (fun i ↦ mu {a i} • dirac (a i)) := by
  have hr : range a = ⋃ i, ({a i} : Set X) := by ext x; simp
  rw [hr, restrict_iUnion]
  · simp only [restrict_singleton]
  · intro i j hij
    exact disjoint_singleton.mpr (fun h ↦ hij (hi h))
  · intro i
    exact measurableSet_singleton _

/-- A distinguished atom and an injective countable range give an exact atomic
measure decomposition whenever their union carries the measure. -/
theorem eq_smul_dirac_add_sum_of_ae_mem_range {ι X : Type*} [Countable ι]
    [MeasurableSpace X] [MeasurableSingletonClass X] (mu : Measure X)
    {a : ι → X} {x₀ : X} (hi : Function.Injective a) (hzero : ∀ i, a i ≠ x₀)
    (hcarry : ∀ᵐ x ∂mu, x = x₀ ∨ x ∈ range a) :
    mu = mu {x₀} • dirac x₀ + Measure.sum (fun i ↦ mu {a i} • dirac (a i)) := by
  have hc : ∀ᵐ x ∂mu, x ∈ ({x₀} : Set X) ∪ range a := by
    simpa only [mem_union, mem_singleton_iff] using hcarry
  have hd : Disjoint ({x₀} : Set X) (range a) := by
    rw [disjoint_singleton_left]
    rintro ⟨i, hi⟩
    exact hzero i hi
  calc
    mu = mu.restrict ({x₀} ∪ range a) := (restrict_eq_self_of_ae_mem hc).symm
    _ = mu.restrict {x₀} + mu.restrict (range a) :=
      restrict_union' hd (measurableSet_singleton _)
    _ = _ := by rw [restrict_singleton, mu.restrict_range_eq_sum_smul_dirac hi]

end MeasureTheory.Measure
