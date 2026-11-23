/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Measure.Dirac.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import RealRooted.Mathlib.Topology.Algebra.InfiniteSum.SortedEnumeration
import RealRooted.Mathlib.MeasureTheory.Measure.AtomicRange

/-!
# Sorted atoms with integer slope multiplicities

If every positive singleton mass is its location times a natural multiplicity,
and these points together with zero carry a finite measure, the positive atoms
have a strictly decreasing finite or infinite enumeration. Both the distinct
slopes and the slopes counted with multiplicity are summable.
-/

public section

open Set
open scoped NNReal

namespace MeasureTheory.Measure

private abbrev SlopeIndex (m : ℝ≥0 → ℕ) := {a : ℝ≥0 // a ≠ 0 ∧ m a ≠ 0}

/-- Summability of the weighted slopes follows directly from finite mass. -/
private theorem summable_slope_mul_multiplicity (mu : Measure ℝ≥0)
    [IsFiniteMeasure mu] (m : ℝ≥0 → ℕ)
    (hmass : ∀ a : ℝ≥0, a ≠ 0 → mu.real {a} = (a : ℝ) * (m a : ℝ)) :
    Summable (fun a : SlopeIndex m ↦ (a : ℝ) * (m a : ℝ)) := by
  have hs : Summable (fun a : SlopeIndex m ↦ mu.real {(a : ℝ≥0)}) :=
    mu.summable_measureReal_singleton_comp Subtype.coe_injective
  exact hs.congr (fun a ↦ hmass a a.property.1)

/-- Positive natural multiplicities dominate the unweighted distinct slopes. -/
private theorem summable_slope (mu : Measure ℝ≥0) [IsFiniteMeasure mu]
    (m : ℝ≥0 → ℕ) (hmass : ∀ a : ℝ≥0, a ≠ 0 → mu.real {a} = (a : ℝ) * (m a : ℝ)) :
    Summable (fun a : SlopeIndex m ↦ (a : ℝ)) := by
  apply Summable.of_nonneg_of_le (fun a : SlopeIndex m ↦ (a : ℝ≥0).coe_nonneg) _
    (summable_slope_mul_multiplicity mu m hmass)
  intro a
  have hm : (1 : ℝ) ≤ (m a : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr a.property.2
  exact le_mul_of_one_le_right (a : ℝ≥0).coe_nonneg hm

/-- Any countable enumeration of the genuine atoms preserves their exact
measure representation and both summability statements. -/
private theorem atomic_representation_of_equiv {ι : Type*} [Countable ι]
    (mu : Measure ℝ≥0) [IsFiniteMeasure mu] (m : ℝ≥0 → ℕ)
    (hmass : ∀ a : ℝ≥0, a ≠ 0 → mu.real {a} = (a : ℝ) * (m a : ℝ))
    (hcarry : ∀ᵐ a : ℝ≥0 ∂mu, a = 0 ∨ m a ≠ 0) (e : ι ≃ SlopeIndex m) :
    Summable (fun i ↦ ((e i : ℝ≥0) : ℝ)) ∧
      Summable (fun i ↦ ((e i : ℝ≥0) : ℝ) * (m (e i) : ℝ)) ∧
      mu = mu {0} • dirac 0 + Measure.sum (fun i ↦
        ENNReal.ofReal (((e i : ℝ≥0) : ℝ) * (m (e i) : ℝ)) • dirac (e i : ℝ≥0)) := by
  refine ⟨(summable_slope mu m hmass).comp_injective e.injective,
    (summable_slope_mul_multiplicity mu m hmass).comp_injective e.injective, ?_⟩
  have hi : Function.Injective (fun i ↦ (e i : ℝ≥0)) :=
    Subtype.coe_injective.comp e.injective
  have hc : ∀ᵐ a : ℝ≥0 ∂mu, a = 0 ∨ a ∈ range (fun i ↦ (e i : ℝ≥0)) := by
    filter_upwards [hcarry] with a ha
    by_cases ha0 : a = 0
    · exact Or.inl ha0
    · exact Or.inr ⟨e.symm ⟨a, ha0, ha.resolve_left ha0⟩,
        congrArg Subtype.val (e.apply_symm_apply _)⟩
  calc
    mu = mu {0} • dirac 0 + Measure.sum (fun i ↦
        mu {(e i : ℝ≥0)} • dirac (e i : ℝ≥0)) :=
      mu.eq_smul_dirac_add_sum_of_ae_mem_range hi (fun i ↦ (e i).property.1) hc
    _ = _ := by
      congr 1
      apply congrArg Measure.sum
      funext i
      rw [← hmass _ (e i).property.1, ofReal_measureReal]

/-- Infinite genuine atoms have a strictly decreasing natural-number
enumeration with their exact integer multiplicities and atomic measure. -/
theorem exists_strictAnti_atomic_representation_of_infinite
    (mu : Measure ℝ≥0) [IsFiniteMeasure mu] (m : ℝ≥0 → ℕ)
    (hmass : ∀ a : ℝ≥0, a ≠ 0 → mu.real {a} = (a : ℝ) * (m a : ℝ))
    (hcarry : ∀ᵐ a : ℝ≥0 ∂mu, a = 0 ∨ m a ≠ 0)
    (hinf : {a : ℝ≥0 | a ≠ 0 ∧ m a ≠ 0}.Infinite) :
    ∃ a : ℕ → ℝ≥0, StrictAnti a ∧ (∀ i, a i ≠ 0 ∧ m (a i) ≠ 0) ∧
      Summable (fun i ↦ (a i : ℝ)) ∧
      Summable (fun i ↦ (a i : ℝ) * (m (a i) : ℝ)) ∧
      mu = mu {0} • dirac 0 + Measure.sum (fun i ↦
        ENNReal.ofReal ((a i : ℝ) * (m (a i) : ℝ)) • dirac (a i)) ∧
      range a = {a : ℝ≥0 | a ≠ 0 ∧ m a ≠ 0} := by
  have : Infinite (SlopeIndex m) := hinf.to_subtype
  have hi : Function.Injective (fun a : SlopeIndex m ↦ (a : ℝ)) :=
    NNReal.coe_injective.comp Subtype.coe_injective
  obtain ⟨e, he⟩ := (summable_slope mu m hmass).exists_equiv_strictAnti_comp
    (fun a ↦ NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr a.property.1)) hi
  obtain ⟨hs, hms, hmu⟩ := atomic_representation_of_equiv mu m hmass hcarry e
  refine ⟨fun i ↦ e i, he, fun i ↦ (e i).property, hs, hms, hmu, ?_⟩
  ext a
  constructor
  · rintro ⟨i, rfl⟩
    exact (e i).property
  · intro ha
    exact ⟨e.symm ⟨a, ha⟩, congrArg Subtype.val (e.apply_symm_apply _)⟩

/-- Finite genuine atoms have a strictly decreasing finite enumeration with
their exact integer multiplicities and atomic measure. Empty support is allowed. -/
theorem exists_fin_strictAnti_atomic_representation_of_finite
    (mu : Measure ℝ≥0) [IsFiniteMeasure mu] (m : ℝ≥0 → ℕ)
    (hmass : ∀ a : ℝ≥0, a ≠ 0 → mu.real {a} = (a : ℝ) * (m a : ℝ))
    (hcarry : ∀ᵐ a : ℝ≥0 ∂mu, a = 0 ∨ m a ≠ 0)
    (hfin : {a : ℝ≥0 | a ≠ 0 ∧ m a ≠ 0}.Finite) :
    ∃ n : ℕ, ∃ a : Fin n → ℝ≥0, StrictAnti a ∧
      (∀ i, a i ≠ 0 ∧ m (a i) ≠ 0) ∧
      Summable (fun i ↦ (a i : ℝ)) ∧
      Summable (fun i ↦ (a i : ℝ) * (m (a i) : ℝ)) ∧
      mu = mu {0} • dirac 0 + Measure.sum (fun i ↦
        ENNReal.ofReal ((a i : ℝ) * (m (a i) : ℝ)) • dirac (a i)) ∧
      range a = {a : ℝ≥0 | a ≠ 0 ∧ m a ≠ 0} := by
  have : Finite (SlopeIndex m) := hfin.to_subtype
  have hi : Function.Injective (fun a : SlopeIndex m ↦ (a : ℝ)) :=
    NNReal.coe_injective.comp Subtype.coe_injective
  obtain ⟨n, e, he⟩ := hi.exists_fin_equiv_strictAnti_comp
  obtain ⟨hs, hms, hmu⟩ := atomic_representation_of_equiv mu m hmass hcarry e
  refine ⟨n, fun i ↦ e i, he, fun i ↦ (e i).property, hs, hms, hmu, ?_⟩
  ext a
  constructor
  · rintro ⟨i, rfl⟩
    exact (e i).property
  · intro ha
    exact ⟨e.symm ⟨a, ha⟩, congrArg Subtype.val (e.apply_symm_apply _)⟩

end MeasureTheory.Measure
