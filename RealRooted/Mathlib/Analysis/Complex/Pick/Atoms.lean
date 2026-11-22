/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import TauCeti.Analysis.Complex.Pick.Nevanlinna
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Atoms of a Nevanlinna measure

The vertical boundary limit of the imaginary part of a Nevanlinna integral
recovers the mass at a real point. Only finiteness of the measure is required;
its support may be arbitrary.
-/

public section

open Complex Filter MeasureTheory Set Topology

namespace TauCeti

/-- The scaled imaginary kernel in real coordinates. -/
private theorem mul_im_nevanlinnaKernel (r y x : ℝ) :
    y * (nevanlinnaKernel ((r : ℂ) + (y : ℂ) * I) x).im =
      y ^ 2 * (1 + x ^ 2) / ((x - r) ^ 2 + y ^ 2) := by
  rw [nevanlinnaKernel_im]
  simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, I_re, mul_one, mul_zero,
    add_zero, zero_add, normSq_apply, sub_re, add_re, mul_re, zero_sub, sub_im]
  ring

/-- A constant bound for the scaled imaginary kernel near the real axis. -/
private theorem norm_mul_im_nevanlinnaKernel_le (r x : ℝ) {y : ℝ}
    (hy : 0 < y) (hy1 : y ≤ 1) :
    ‖y * (nevanlinnaKernel ((r : ℂ) + (y : ℂ) * I) x).im‖ ≤ 4 + 2 * r ^ 2 := by
  rw [mul_im_nevanlinnaKernel, Real.norm_of_nonneg (by positivity),
    div_le_iff₀ (by positivity : 0 < (x - r) ^ 2 + y ^ 2)]
  have hy2 : y ^ 2 ≤ 1 := by nlinarith
  have hx2 : x ^ 2 ≤ 2 * (x - r) ^ 2 + 2 * r ^ 2 := by nlinarith [sq_nonneg (x - 2 * r)]
  have hmul := mul_le_mul_of_nonneg_left hx2 (sq_nonneg y)
  have hdrop := mul_le_mul_of_nonneg_left hy2 (sq_nonneg (x - r))
  nlinarith [mul_nonneg (sq_nonneg r) (sq_nonneg (x - r)), sq_nonneg (x - r)]

/-- Away from its boundary point the scaled imaginary kernel tends to zero. -/
private theorem tendsto_mul_im_nevanlinnaKernel (r x : ℝ) :
    Tendsto (fun y : ℝ => y * (nevanlinnaKernel ((r : ℂ) + (y : ℂ) * I) x).im)
      (𝓝[>] (0 : ℝ)) (𝓝 (if x = r then 1 + r ^ 2 else 0)) := by
  simp only [mul_im_nevanlinnaKernel]
  by_cases hx : x = r
  · subst x
    simp only [ite_true]
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with y hy
    have hy0 : y ≠ 0 := ne_of_gt hy
    simp [hy0]
  · simp only [ite_eq_right hx]
    have hden : (x - r) ^ 2 + (0 : ℝ) ^ 2 ≠ 0 := by
      simpa using pow_ne_zero 2 (sub_ne_zero.mpr hx)
    have h := (((tendsto_id : Tendsto (fun y : ℝ => y) (𝓝[>] (0 : ℝ))
      (𝓝[>] (0 : ℝ))).mono_right nhdsWithin_le_nhds).pow 2).mul_const (1 + x ^ 2)
    have hd := (tendsto_const_nhds (x := (x - r) ^ 2)).add
      (((tendsto_id : Tendsto (fun y : ℝ => y) (𝓝[>] (0 : ℝ))
        (𝓝[>] (0 : ℝ))).mono_right nhdsWithin_le_nhds).pow 2)
    convert h.div hd hden using 1
    · ext y
      rfl
    · simp

/-- The vertical imaginary-part boundary limit of a finite Nevanlinna integral
recovers its atom at the boundary point. -/
theorem tendsto_mul_im_nevanlinna (mu : Measure ℝ) [IsFiniteMeasure mu] (r : ℝ) :
    Tendsto (fun y : ℝ => y *
      (∫ x, nevanlinnaKernel ((r : ℂ) + (y : ℂ) * I) x ∂mu).im)
      (𝓝[>] (0 : ℝ)) (𝓝 ((1 + r ^ 2) * mu.real {r})) := by
  have hlim := tendsto_integral_filter_of_norm_le_const
    (μ := mu) (l := 𝓝[>] (0 : ℝ)) (F := fun y x : ℝ => y *
      (nevanlinnaKernel ((r : ℂ) + (y : ℂ) * I) x).im)
    (f := fun x : ℝ => if x = r then 1 + r ^ 2 else 0) ?_ ?_ ?_
  · have heq : (∫ x : ℝ, (if x = r then 1 + r ^ 2 else 0) ∂mu) =
        (1 + r ^ 2) * mu.real {r} := by
      have heqfun : (fun x : ℝ => if x = r then 1 + r ^ 2 else 0) =
          Set.indicator {r} (fun _ : ℝ => 1 + r ^ 2) := by
        ext x
        by_cases hx : x = r
        · simp [hx]
        · simp [Set.indicator, hx]
      rw [heqfun, integral_indicator (measurableSet_singleton r)]
      simp [mul_comm, Measure.real]
    rw [heq] at hlim
    apply hlim.congr'
    filter_upwards [self_mem_nhdsWithin] with y hy
    have hmem : (r : ℂ) + (y : ℂ) * I ∈ UpperHalfPlane.upperHalfPlaneSet := by
      simpa [UpperHalfPlane.upperHalfPlaneSet] using hy
    have hint := integrable_nevanlinnaKernel hmem mu
    rw [integral_const_mul]
    congr 1
    simpa using Complex.imCLM.integral_comp_comm hint
  · filter_upwards [self_mem_nhdsWithin] with y hy
    have him : ((r : ℂ) + (y : ℂ) * I).im ≠ 0 := by simpa using ne_of_gt hy
    exact (continuous_const.mul
      (Complex.continuous_im.comp (continuous_nevanlinnaKernel him))).aestronglyMeasurable
  · refine ⟨4 + 2 * r ^ 2, ?_⟩
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))] with y hy hy1
    exact Filter.Eventually.of_forall fun x => norm_mul_im_nevanlinnaKernel_le r x hy hy1.le
  · exact Filter.Eventually.of_forall fun x => tendsto_mul_im_nevanlinnaKernel r x

/-- A real affine term does not change the atom recovered from a Nevanlinna
representation. No sign condition on the linear coefficient is needed. -/
theorem tendsto_mul_im_of_eq_nevanlinnaKernel_add
    {F : ℂ → ℂ} (mu : Measure ℝ) [IsFiniteMeasure mu] (b c r : ℝ)
    (hrep : ∀ z ∈ UpperHalfPlane.upperHalfPlaneSet,
      F z = (b : ℂ) * z + ∫ x, nevanlinnaKernel z x ∂mu + c) :
    Tendsto (fun y : ℝ => y * (F ((r : ℂ) + (y : ℂ) * I)).im)
      (𝓝[>] (0 : ℝ)) (𝓝 ((1 + r ^ 2) * mu.real {r})) := by
  have hid : Tendsto (fun y : ℝ => y) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
    tendsto_id.mono_right nhdsWithin_le_nhds
  have hlin : Tendsto (fun y : ℝ => b * y ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa using (hid.pow 2).const_mul b
  have h := hlin.add (tendsto_mul_im_nevanlinna mu r)
  simp only [zero_add] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with y hy
  have hmem : (r : ℂ) + (y : ℂ) * I ∈ UpperHalfPlane.upperHalfPlaneSet := by
    simpa [UpperHalfPlane.upperHalfPlaneSet] using hy
  rw [hrep _ hmem]
  simp only [add_im, mul_im, ofReal_re, ofReal_im, mul_zero, zero_mul, zero_add,
    add_zero, I_im, mul_one, I_re]
  ring

end TauCeti
