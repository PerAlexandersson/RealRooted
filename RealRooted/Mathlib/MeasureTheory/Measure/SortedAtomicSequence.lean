/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import RealRooted.Mathlib.MeasureTheory.Measure.SortedAtomicMeasure
import RealRooted.Mathlib.MeasureTheory.Measure.AtomicRange
import RealRooted.Mathlib.Order.Monotone.PositiveExtension

/-!
# Infinite sorted atomic presentations with zero-multiplicity padding

Every finite nonnegative measure with integer slope multiplicities has a
presentation indexed by all natural numbers, even when its genuine positive
support is finite or empty. The padded slopes stay positive and summable;
their natural multiplicities are zero.
-/

public section

open scoped NNReal ENNReal

open Set

namespace MeasureTheory.Measure

/-- Any positive injective enumeration covering the nonzero multiplicities
gives the exact measure and a summable multiplicity-weighted sequence. -/
private theorem atomic_representation_of_cover
    (mu : Measure ℝ≥0) [IsFiniteMeasure mu] (m : ℝ≥0 → ℕ)
    (hmass : ∀ a : ℝ≥0, a ≠ 0 → mu.real {a} = (a : ℝ) * (m a : ℝ))
    (hcarry : ∀ᵐ a : ℝ≥0 ∂mu, a = 0 ∨ m a ≠ 0) {a : ℕ → ℝ≥0}
    (hi : Function.Injective a) (hpos : ∀ i, 0 < a i)
    (hcover : {x : ℝ≥0 | x ≠ 0 ∧ m x ≠ 0} ⊆ range a) :
    Summable (fun i ↦ (a i : ℝ) * (m (a i) : ℝ)) ∧
      mu = mu {0} • dirac 0 + Measure.sum (fun i ↦
        ENNReal.ofReal ((a i : ℝ) * (m (a i) : ℝ)) • dirac (a i)) := by
  have hs : Summable (fun i ↦ mu.real {a i}) := summable_measure_toReal
    (fun _ ↦ measurableSet_singleton _) (fun i j hij ↦
      disjoint_singleton.mpr (fun h ↦ hij (hi h)))
  refine ⟨hs.congr (fun i ↦ hmass _ (hpos i).ne'), ?_⟩
  have hc : ∀ᵐ x : ℝ≥0 ∂mu, x = 0 ∨ x ∈ range a := by
    filter_upwards [hcarry] with x hx
    by_cases hx0 : x = 0
    · exact Or.inl hx0
    · exact Or.inr (hcover ⟨hx0, hx.resolve_left hx0⟩)
  calc
    mu = mu {0} • dirac 0 + Measure.sum (fun i ↦ mu {a i} • dirac (a i)) :=
      mu.eq_smul_dirac_add_sum_of_ae_mem_range hi (fun i ↦ (hpos i).ne') hc
    _ = _ := by
      congr 1
      apply congrArg Measure.sum
      funext i
      rw [← hmass _ (hpos i).ne', ofReal_measureReal]

/-- The literal infinite sorted atomic presentation, with zero multiplicities
allowed at the extra slopes used for finite and empty support. -/
theorem exists_strictAnti_atomic_representation
    (mu : Measure ℝ≥0) [IsFiniteMeasure mu] (m : ℝ≥0 → ℕ)
    (hmass : ∀ a : ℝ≥0, a ≠ 0 → mu.real {a} = (a : ℝ) * (m a : ℝ))
    (hcarry : ∀ᵐ a : ℝ≥0 ∂mu, a = 0 ∨ m a ≠ 0) :
    ∃ a : ℕ → ℝ≥0, StrictAnti a ∧ (∀ i, 0 < a i) ∧
      Summable (fun i ↦ (a i : ℝ)) ∧
      Summable (fun i ↦ (a i : ℝ) * (m (a i) : ℝ)) ∧
      mu = mu {0} • dirac 0 + Measure.sum (fun i ↦
        ENNReal.ofReal ((a i : ℝ) * (m (a i) : ℝ)) • dirac (a i)) ∧
      {x : ℝ≥0 | x ≠ 0 ∧ m x ≠ 0} ⊆ range a := by
  rcases Set.finite_or_infinite {x : ℝ≥0 | x ≠ 0 ∧ m x ≠ 0} with hfin | hinf
  · obtain ⟨n, a, ha, hapos, _, _, _, hrange⟩ :=
      mu.exists_fin_strictAnti_atomic_representation_of_finite m hmass hcarry hfin
    obtain ⟨b, hb, hbpos, hbs, hext⟩ :=
      ha.exists_pos_summable_nat_extension (fun i ↦ pos_iff_ne_zero.mpr (hapos i).1)
    have hcover : {x : ℝ≥0 | x ≠ 0 ∧ m x ≠ 0} ⊆ range b := by
      intro x hx
      obtain ⟨i, rfl⟩ := hrange.symm ▸ hx
      exact ⟨i.val, hext i⟩
    obtain ⟨hms, hmu⟩ := atomic_representation_of_cover mu m hmass hcarry
      hb.injective hbpos hcover
    exact ⟨b, hb, hbpos, hbs, hms, hmu, hcover⟩
  · obtain ⟨a, ha, hapos, hs, hms, hmu, hrange⟩ :=
      mu.exists_strictAnti_atomic_representation_of_infinite m hmass hcarry hinf
    exact ⟨a, ha, fun i ↦ pos_iff_ne_zero.mpr (hapos i).1, hs, hms, hmu,
      hrange.symm.subset⟩

end MeasureTheory.Measure
