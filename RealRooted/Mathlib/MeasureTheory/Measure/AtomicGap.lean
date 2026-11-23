/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

import Mathlib.MeasureTheory.Measure.Dirac.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Tactic.TypeStar

/-!
# Positive support gaps in slope-weighted atomic measures
-/

public section

open Filter MeasureTheory MeasureTheory.Measure Set Topology

namespace MeasureTheory

/-- A positive lower support gap kills the atom at zero and places every
active slope above the gap. Summability then forces finite active support. -/
theorem eq_zero_and_finite_support_of_ae_le_atomic
    {a : ℕ → ℝ} {gamma c : ℝ} (ha : ∀ i, 0 ≤ a i) (hs : Summable a)
    (hg : 0 ≤ gamma) (hc : 0 < c)
    (hgap : ∀ᵐ x ∂(ENNReal.ofReal gamma • Measure.dirac 0 +
      Measure.sum (fun i => ENNReal.ofReal (a i) • Measure.dirac (a i))), c ≤ x) :
    gamma = 0 ∧ (Function.support a).Finite ∧ ∀ i, a i ≠ 0 → c ≤ a i := by
  obtain ⟨hzero, hatoms⟩ := ae_add_measure_iff.mp hgap
  have hg0 : gamma = 0 := by
    by_contra hne
    have hw : ENNReal.ofReal gamma ≠ 0 :=
      (ENNReal.ofReal_pos.mpr (lt_of_le_of_ne hg (Ne.symm hne))).ne'
    have hz : c ≤ (0 : ℝ) := (ae_dirac_iff measurableSet_Ici).mp
      ((ae_ennreal_smul_measure_iff hw).mp hzero)
    exact hc.not_ge hz
  have hbound (i : ℕ) (hi : a i ≠ 0) : c ≤ a i := by
    have hw : ENNReal.ofReal (a i) ≠ 0 :=
      (ENNReal.ofReal_pos.mpr (lt_of_le_of_ne (ha i) (Ne.symm hi))).ne'
    exact (ae_dirac_iff measurableSet_Ici).mp
      ((ae_ennreal_smul_measure_iff hw).mp ((ae_sum_iff.mp hatoms) i))
  have hsmall : ∀ᶠ i in cofinite, a i < c :=
    hs.tendsto_cofinite_zero.eventually_lt_const hc
  refine ⟨hg0, (eventually_cofinite.mp hsmall).subset ?_, hbound⟩
  intro i hi
  exact not_lt.mpr (hbound i hi)

/-- A finite family of positive real numbers has a common positive lower bound,
including the empty family. -/
private theorem exists_pos_le_finset {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (ha : ∀ i ∈ s, 0 < a i) : ∃ c > 0, ∀ i ∈ s, c ≤ a i := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, zero_lt_one, by simp⟩
  | @insert i s hi ih =>
      obtain ⟨c, hc, hcs⟩ := ih (fun j hj => ha j (Finset.mem_insert_of_mem hj))
      refine ⟨min (a i) c, lt_min (ha i (Finset.mem_insert_self _ _)) hc, ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact min_le_left _ _
      · exact (min_le_right _ _).trans (hcs j hj)

/-- Finitely many nonzero nonnegative slopes yield a positive support gap for
their slope-weighted atomic measure. The empty support gives the zero measure. -/
theorem exists_pos_ae_le_sum_smul_dirac_of_finite_support
    {a : ℕ → ℝ} (ha : ∀ i, 0 ≤ a i) (hs : (Function.support a).Finite) :
    ∃ c > 0, ∀ᵐ x ∂Measure.sum
      (fun i => ENNReal.ofReal (a i) • Measure.dirac (a i)), c ≤ x := by
  classical
  obtain ⟨c, hc, hcs⟩ := exists_pos_le_finset hs.toFinset a (fun i hi =>
    lt_of_le_of_ne (ha i) (Ne.symm (hs.mem_toFinset.mp hi)))
  refine ⟨c, hc, ae_sum_iff.mpr fun i => ?_⟩
  by_cases hi : a i = 0
  · simp only [hi, ENNReal.ofReal_zero, zero_smul, ae_zero, Filter.eventually_bot]
  · apply ae_smul_measure
    exact (ae_dirac_iff measurableSet_Ici).mpr (hcs i (hs.mem_toFinset.mpr hi))

end MeasureTheory
