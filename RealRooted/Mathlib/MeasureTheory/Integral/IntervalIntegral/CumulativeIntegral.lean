/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Integrable tests against finite cumulative sums

The cumulative-sum identity holds for an interval-integrable test, including
integrable endpoint singularities. No positivity of the atomic weights is needed.
-/

public section

open MeasureTheory Set

namespace IntervalIntegrable

/-- Cutting an interval-integrable real function at a lower threshold preserves integrability. -/
theorem ite_le_zero {f : ℝ → ℝ} {a b r : ℝ}
    (hf : IntervalIntegrable f volume a b) :
    IntervalIntegrable (fun t ↦ if r ≤ t then f t else 0) volume a b := by
  change IntervalIntegrable ((Ici r).indicator f) volume a b
  exact ⟨hf.1.indicator measurableSet_Ici, hf.2.indicator measurableSet_Ici⟩

end IntervalIntegrable

namespace intervalIntegral

/-- A lower-threshold indicator restricts an interval integral to the upper subinterval.
The equality at the threshold is immaterial for Lebesgue integration. -/
theorem integral_ite_le_zero {f : ℝ → ℝ} {a b r : ℝ}
    (hr : r ∈ Set.Icc a b) (hf : IntervalIntegrable f volume a b) :
    (∫ t in a..b, if r ≤ t then f t else 0) = ∫ t in r..b, f t := by
  have hi := hf.ite_le_zero (r := r)
  have hparts := (IntervalIntegrable.trans_iff
    (a := a) (b := r) (c := b) (by
      simpa only [uIcc_of_le (hr.1.trans hr.2)] using hr)).mp hi
  have hlo : (∫ t in a..r, if r ≤ t then f t else 0) = 0 := by
    calc
      _ = ∫ _t in a..r, (0 : ℝ) :=
        intervalIntegral.integral_congr_Ioo_of_le hr.1 fun t ht ↦ by
          rw [ite_eq_right (not_le.mpr ht.2)]
      _ = 0 := by simp
  have hhi : (∫ t in r..b, if r ≤ t then f t else 0) = ∫ t in r..b, f t :=
    intervalIntegral.integral_congr_Ioo_of_le hr.2 fun t ht ↦ by
      rw [ite_eq_left ht.1.le]
  rw [← intervalIntegral.integral_add_adjacent_intervals hparts.1 hparts.2, hlo, hhi, zero_add]

end intervalIntegral

namespace Finset

variable {ι : Type*}

/-- A finite cumulative sum times an interval-integrable test is interval integrable.
The node locations and signs of the weights are unrestricted. -/
theorem intervalIntegrable_cumulative_mul (s : Finset ι) (r w : ι → ℝ)
    {a b : ℝ} {g : ℝ → ℝ} (hg : IntervalIntegrable g volume a b) :
    IntervalIntegrable
      (fun t ↦ (∑ i ∈ s, if r i ≤ t then w i else 0) * g t) volume a b := by
  have hi (i : ι) : IntervalIntegrable
      (fun t ↦ if r i ≤ t then w i * g t else 0) volume a b :=
    (hg.const_mul (w i)).ite_le_zero
  convert IntervalIntegrable.sum s (fun i _ ↦ hi i) using 1
  ext t
  simp only [Finset.sum_apply, Finset.sum_mul, ite_mul, zero_mul]

/-- Integration against a finite cumulative sum equals the sum of the weighted tail integrals.
Interval integrability suffices; endpoint-singular derivatives are permitted. -/
theorem integral_cumulative_mul_of_intervalIntegrable (s : Finset ι) (r w : ι → ℝ)
    (hr : ∀ i ∈ s, r i ∈ Set.Icc (0 : ℝ) 1) {g : ℝ → ℝ}
    (hg : IntervalIntegrable g volume 0 1) :
    (∫ t in (0 : ℝ)..1, (∑ i ∈ s, if r i ≤ t then w i else 0) * g t) =
      ∑ i ∈ s, w i * ∫ t in r i..1, g t := by
  classical
  have heq : (fun t ↦ (∑ i ∈ s, if r i ≤ t then w i else 0) * g t) =
      (fun t ↦ ∑ i ∈ s, if r i ≤ t then w i * g t else 0) := by
    funext t
    simp only [Finset.sum_mul, ite_mul, zero_mul]
  rw [heq, intervalIntegral.integral_finsetSum (fun i _ ↦ (hg.const_mul (w i)).ite_le_zero)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [intervalIntegral.integral_ite_le_zero (hr i hi) (hg.const_mul (w i)),
    intervalIntegral.integral_const_mul]

end Finset
