/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import RealRooted.Mathlib.RingTheory.PowerSeries.StieltjesFraction.Tail
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import RealRooted.Mathlib.RingTheory.PowerSeries.StieltjesFraction.FiniteAtomicFraction

/-!
# Stieltjes fractions of finite-carrier measures

Zero-mass nodes are removed from the carrying set. Every retained node then
has positive real mass and is nonnegative by the measure's support premise.
The finite atomic fraction theorem includes the empty measure automatically.
-/

public section

open MeasureTheory

namespace PowerSeries

/-- Discard zero-mass carrier points and integrate over the remaining atoms. -/
private theorem finite_carrier_moment_sum {mu : Measure ℝ} [IsFiniteMeasure mu]
    (hpos : ∀ᵐ x ∂mu, 0 ≤ x) (s₀ : Finset ℝ) (hs₀ : ∀ᵐ x ∂mu, x ∈ s₀) :
    ∃ s : Finset ℝ, (∀ x ∈ s, 0 ≤ x) ∧ (∀ x ∈ s, 0 < mu.real {x}) ∧
      ∀ k : ℕ, (∫ x : ℝ, x ^ k ∂mu) = ∑ x ∈ s, mu.real {x} * x ^ k := by
  classical
  let s := s₀.filter (fun x => mu {x} ≠ 0)
  have hne (x : ℝ) (hx : x ∈ s) : mu {x} ≠ 0 := (Finset.mem_filter.mp hx).2
  have hnode (x : ℝ) (hx : x ∈ s) : 0 ≤ x := by
    by_contra hneg
    exact hne x hx (measure_mono_null (Set.singleton_subset_iff.mpr hneg) (ae_iff.mp hpos))
  have hweight (x : ℝ) (hx : x ∈ s) : 0 < mu.real {x} :=
    lt_of_le_of_ne measureReal_nonneg
      (Ne.symm ((measureReal_ne_zero_iff (measure_ne_top mu {x})).mpr (hne x hx)))
  have hmu : mu = ∑ x ∈ s, mu {x} • Measure.dirac x := by
    calc
      mu = ∑ x ∈ s₀, mu {x} • Measure.dirac x := Measure.ae_mem_finset_iff.mp hs₀
      _ = _ := by
        symm
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro x hx hxs
        have hz : mu {x} = 0 := by
          by_contra hz
          exact hxs (Finset.mem_filter.mpr ⟨hx, hz⟩)
        rw [hz, zero_smul]
  refine ⟨s, hnode, hweight, fun k => ?_⟩
  calc
    (∫ x : ℝ, x ^ k ∂mu) =
        ∫ x : ℝ, x ^ k ∂(∑ y ∈ s, mu {y} • Measure.dirac y) :=
      congrArg (fun ν : Measure ℝ => ∫ x : ℝ, x ^ k ∂ν) hmu
    _ = ∑ x ∈ s, mu.real {x} * x ^ k := by
      rw [integral_finsetSum_measure (fun y _ =>
        (integrable_dirac (by finiteness)).smul_measure (measure_ne_top mu {y}))]
      apply Finset.sum_congr rfl
      intro y _
      rw [integral_smul_measure, integral_dirac, smul_eq_mul]
      rfl

/-- A finite nonnegative measure carried by a finite set has a nonnegative
formal Stieltjes fraction with its exact total mass as outer scalar. -/
theorem exists_stieltjesTail_of_finite_carrier {mu : Measure ℝ} [IsFiniteMeasure mu]
    (hpos : ∀ᵐ x ∂mu, 0 ≤ x) (S : Set ℝ) (hS : S.Finite) (hcarrier : mu Sᶜ = 0) :
    ∃ a : ℕ → ℝ, (∀ k, 0 ≤ a k) ∧
      mk (fun k => ∫ x : ℝ, x ^ k ∂mu) = C (mu.real Set.univ) * stieltjesTail a 0 := by
  classical
  have hs₀ : ∀ᵐ x ∂mu, x ∈ hS.toFinset := by
    simpa only [Set.Finite.mem_toFinset] using (ae_iff.mpr hcarrier : ∀ᵐ x ∂mu, x ∈ S)
  obtain ⟨s, hx, hw, hmom⟩ := finite_carrier_moment_sum hpos hS.toFinset hs₀
  obtain ⟨a, ha, hf⟩ := exists_stieltjesTail_finset_moments s (fun x => mu.real {x}) hx hw
  have hmass : mu.real Set.univ = ∑ x ∈ s, mu.real {x} := by
    simpa only [pow_zero, integral_const, smul_eq_mul, mul_one] using hmom 0
  refine ⟨a, ha, ?_⟩
  rw [funext hmom, hmass]
  exact hf

end PowerSeries
