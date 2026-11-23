/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import RealRooted.Mathlib.MeasureTheory.Integral.IntervalIntegral.CumulativeIntegral
import RealRooted.Mathlib.MeasureTheory.Integral.IntervalIntegral.CumulativeMoments
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Finite cumulative discrepancy and integrable derivatives

Continuous endpoint values, derivatives on the open interval, and integrability
of the derivative suffice for summation by parts. No endpoint differentiability
or continuous-derivative hypothesis is required.
-/

public section

open MeasureTheory

namespace Finset

variable {ι : Type*}

private theorem integral_tail_eq_sub {f g : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc (0 : ℝ) 1))
    (hfg : ∀ t ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt f (g t) t)
    (hg : IntervalIntegrable g volume 0 1) {a : ℝ} (ha : a ∈ Set.Icc (0 : ℝ) 1) :
    (∫ t in a..1, g t) = f 1 - f a := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ha.2
  · exact hf.mono (Set.Icc_subset_Icc ha.1 le_rfl)
  · intro t ht
    exact hfg t ⟨lt_of_le_of_lt ha.1 ht.1, ht.2⟩
  · apply hg.mono_set
    rw [Set.uIcc_of_le ha.2, Set.uIcc_of_le zero_le_one]
    exact Set.Icc_subset_Icc ha.1 le_rfl

private theorem integral_eq_endpoint_sub_mul {f g : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc (0 : ℝ) 1))
    (hfg : ∀ t ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt f (g t) t)
    (hg : IntervalIntegrable g volume 0 1) :
    (∫ t in (0 : ℝ)..1, f t) = f 1 - ∫ t in (0 : ℝ)..1, t * g t := by
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (a := (0 : ℝ)) (b := 1) (u := f) (u' := g) (v := fun t : ℝ ↦ t)
    (v' := fun _ : ℝ ↦ 1)
    (by simpa only [Set.uIcc_of_le zero_le_one] using hf) continuous_id.continuousOn
    (by simpa only [min_eq_left zero_le_one, max_eq_right zero_le_one] using hfg)
    (fun t _ ↦ hasDerivAt_id t) hg intervalIntegrable_const
  simpa only [mul_one, one_mul, mul_zero, zero_mul, sub_zero, mul_comm] using h

private theorem integral_cumulative_deriv_eq (s : Finset ι) (r w : ι → ℝ)
    (hr : ∀ i ∈ s, r i ∈ Set.Icc (0 : ℝ) 1) {f g : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc (0 : ℝ) 1))
    (hfg : ∀ t ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt f (g t) t)
    (hg : IntervalIntegrable g volume 0 1) :
    (∫ t in (0 : ℝ)..1, (∑ i ∈ s, if r i ≤ t then w i else 0) * g t) =
      f 1 * (∑ i ∈ s, w i) - ∑ i ∈ s, w i * f (r i) := by
  rw [integral_cumulative_mul_of_intervalIntegrable s r w hr hg]
  calc
    _ = ∑ i ∈ s, w i * (f 1 - f (r i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [integral_tail_eq_sub hf hfg hg (hr i hi)]
    _ = _ := by
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
      ring

private theorem abs_integral_cumulative_sub_mul_le (s : Finset ι) (r w : ι → ℝ)
    {δ : ℝ} (hδ : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      |(∑ i ∈ s, if r i ≤ t then w i else 0) - t| ≤ δ)
    {g : ℝ → ℝ} (hg : IntervalIntegrable g volume 0 1) :
    |∫ t in (0 : ℝ)..1, ((∑ i ∈ s, if r i ≤ t then w i else 0) - t) * g t| ≤
      δ * ∫ t in (0 : ℝ)..1, |g t| := by
  have hint : IntervalIntegrable
      (fun t ↦ ((∑ i ∈ s, if r i ≤ t then w i else 0) - t) * g t) volume 0 1 := by
    simp_rw [sub_mul]
    exact (intervalIntegrable_cumulative_mul s r w hg).sub
      (hg.continuousOn_mul continuous_id.continuousOn)
  calc
    _ ≤ ∫ t in (0 : ℝ)..1, |((∑ i ∈ s, if r i ≤ t then w i else 0) - t) * g t| :=
      intervalIntegral.abs_integral_le_integral_abs zero_le_one
    _ ≤ ∫ t in (0 : ℝ)..1, δ * |g t| := by
      apply intervalIntegral.integral_mono_on zero_le_one hint.abs (hg.abs.const_mul δ)
      intro t ht
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hδ t ht) (abs_nonneg _)
    _ = δ * ∫ t in (0 : ℝ)..1, |g t| := intervalIntegral.integral_const_mul _ _

/-- Finite cumulative discrepancy bounds integration error by the endpoint value plus the
integral of the absolute derivative. Signed atomic weights are allowed; only interior
pointwise derivatives, continuous endpoint values and interval integrability are assumed. -/
theorem abs_sum_mul_sub_integral_le_of_cumulative_bound (s : Finset ι) (r w : ι → ℝ)
    (hr : ∀ i ∈ s, r i ∈ Set.Icc (0 : ℝ) 1) {δ : ℝ}
    (hδ : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      |(∑ i ∈ s, if r i ≤ t then w i else 0) - t| ≤ δ)
    {f g : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc (0 : ℝ) 1))
    (hfg : ∀ t ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt f (g t) t)
    (hg : IntervalIntegrable g volume 0 1) :
    |(∑ i ∈ s, w i * f (r i)) - ∫ t in (0 : ℝ)..1, f t| ≤
      δ * (|f 1| + ∫ t in (0 : ℝ)..1, |g t|) := by
  let F (t : ℝ) := ∑ i ∈ s, if r i ≤ t then w i else 0
  have hsplit : (∫ t in (0 : ℝ)..1, (F t - t) * g t) =
      (∫ t in (0 : ℝ)..1, F t * g t) - ∫ t in (0 : ℝ)..1, t * g t := by
    simp_rw [sub_mul]
    exact intervalIntegral.integral_sub (intervalIntegrable_cumulative_mul s r w hg)
      (hg.continuousOn_mul continuous_id.continuousOn)
  have hidentity : (∑ i ∈ s, w i * f (r i)) - ∫ t in (0 : ℝ)..1, f t =
      f 1 * ((∑ i ∈ s, w i) - 1) - ∫ t in (0 : ℝ)..1, (F t - t) * g t := by
    rw [hsplit, integral_cumulative_deriv_eq s r w hr hf hfg hg,
      integral_eq_endpoint_sub_mul hf hfg hg]
    ring
  rw [hidentity]
  calc
    _ ≤ |f 1 * ((∑ i ∈ s, w i) - 1)| + |∫ t in (0 : ℝ)..1, (F t - t) * g t| := abs_sub _ _
    _ ≤ |f 1| * δ + δ * ∫ t in (0 : ℝ)..1, |g t| := by
      rw [abs_mul]
      exact add_le_add
        (mul_le_mul_of_nonneg_left
          (abs_sum_sub_one_le_of_cumulative_bound s r w hr hδ) (abs_nonneg _))
        (abs_integral_cumulative_sub_mul_le s r w hδ hg)
    _ = _ := by ring

end Finset
