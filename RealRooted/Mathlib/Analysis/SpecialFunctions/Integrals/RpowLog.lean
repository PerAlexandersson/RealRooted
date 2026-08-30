import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Topology.Order.ExtendFrom

/-!
# Integrals of a real power times a logarithm

This file supplies the improper integral at zero obtained by differentiating
the elementary real-power integral with respect to its exponent.
-/

open Filter MeasureTheory Set Topology

namespace intervalIntegral

private theorem hasDerivAt_rpowLogPrimitive {r x : ℝ} (hr : -1 < r)
    (hx : 0 < x) :
    HasDerivAt
      (fun y : ℝ =>
        y ^ (r + 1) / (r + 1) ^ 2 -
          y ^ (r + 1) * Real.log y / (r + 1))
      (-(x ^ r * Real.log x)) x := by
  have hr1 : r + 1 ≠ 0 := by linarith
  have hpow := Real.hasDerivAt_rpow_const (p := r + 1) (Or.inl hx.ne')
  have hlog := Real.hasDerivAt_log hx.ne'
  have h := (hpow.div_const ((r + 1) ^ 2)).sub
    ((hpow.mul hlog).div_const (r + 1))
  have hscalar :
      (r + 1) * x ^ (r + 1 - 1) / (r + 1) ^ 2 -
          ((r + 1) * x ^ (r + 1 - 1) * Real.log x +
            x ^ (r + 1) * x⁻¹) / (r + 1) =
        -(x ^ r * Real.log x) := by
    rw [show r + 1 - 1 = r by ring, Real.rpow_add_one hx.ne' r]
    field_simp
    ring
  exact h.congr_deriv hscalar

private theorem tendsto_rpowLogPrimitive_zero {r : ℝ} (hr : -1 < r) :
    Tendsto
      (fun x : ℝ =>
        x ^ (r + 1) / (r + 1) ^ 2 -
          x ^ (r + 1) * Real.log x / (r + 1))
      (𝓝[>] 0) (𝓝 0) := by
  have hr1 : 0 < r + 1 := by linarith
  have hpow : Tendsto (fun x : ℝ => x ^ (r + 1)) (𝓝[>] 0) (𝓝 0) := by
    have hc : ContinuousWithinAt (fun x : ℝ => x ^ (r + 1))
        (Ioi 0) 0 :=
      (Real.continuous_rpow_const hr1.le).continuousAt.continuousWithinAt
    simpa [Real.zero_rpow hr1.ne'] using
      hc.tendsto
  have hlogpow :
      Tendsto (fun x : ℝ => Real.log x * x ^ (r + 1)) (𝓝[>] 0) (𝓝 0) :=
    tendsto_log_mul_rpow_nhdsGT_zero hr1
  have h := (hpow.div_const ((r + 1) ^ 2)).sub
    (hlogpow.mul_const ((r + 1)⁻¹))
  convert h using 1
  · ext x
    ring
  · simp

private theorem tendsto_rpowLogPrimitive_one {r : ℝ} (hr : -1 < r) :
    Tendsto
      (fun x : ℝ =>
        x ^ (r + 1) / (r + 1) ^ 2 -
          x ^ (r + 1) * Real.log x / (r + 1))
      (𝓝[<] 1)
      (𝓝 ((r + 1)⁻¹ ^ 2)) := by
  have hr1 : r + 1 ≠ 0 := by linarith
  have hcont : ContinuousAt
      (fun x : ℝ =>
        x ^ (r + 1) / (r + 1) ^ 2 -
          x ^ (r + 1) * Real.log x / (r + 1)) 1 := by
    exact (((continuousAt_id.rpow_const (Or.inl one_ne_zero)).mul_const
      (((r + 1) ^ 2)⁻¹)).sub
        (((continuousAt_id.rpow_const (Or.inl one_ne_zero)).mul
          (Real.continuousAt_log one_ne_zero)).mul_const ((r + 1)⁻¹)))
  have hvalue :
      (1 : ℝ) ^ (r + 1) / (r + 1) ^ 2 -
          1 ^ (r + 1) * Real.log 1 / (r + 1) =
        (r + 1)⁻¹ ^ 2 := by
    simp only [Real.one_rpow, Real.log_one, mul_zero, zero_div, sub_zero]
    field_simp
  rw [← hvalue]
  exact hcont.tendsto.mono_left inf_le_left

/-- For `r > -1`, `x ^ r * log x` is interval-integrable across zero. -/
theorem intervalIntegrable_rpow_mul_log {r : ℝ} (hr : -1 < r) :
    IntervalIntegrable (fun x : ℝ => x ^ r * Real.log x) volume 0 1 := by
  let raw := fun x : ℝ =>
    x ^ (r + 1) / (r + 1) ^ 2 -
      x ^ (r + 1) * Real.log x / (r + 1)
  let F := extendFrom (Ioo (0 : ℝ) 1) raw
  have hraw_cont : ContinuousOn raw (Ioo (0 : ℝ) 1) := by
    intro x hx
    unfold raw
    exact (((continuousAt_id.rpow_const (Or.inl hx.1.ne')).mul_const
      (((r + 1) ^ 2)⁻¹)).sub
        (((continuousAt_id.rpow_const (Or.inl hx.1.ne')).mul
          (Real.continuousAt_log hx.1.ne')).mul_const
            ((r + 1)⁻¹))).continuousWithinAt
  have hzero : Tendsto raw (𝓝[>] 0) (𝓝 0) :=
    tendsto_rpowLogPrimitive_zero hr
  have hone : Tendsto raw (𝓝[<] 1) (𝓝 ((r + 1)⁻¹ ^ 2)) :=
    tendsto_rpowLogPrimitive_one hr
  have hF_cont : ContinuousOn F (Icc (0 : ℝ) 1) :=
    continuousOn_Icc_extendFrom_Ioo hraw_cont hzero hone
  have hF_deriv : ∀ x ∈ Ioo (0 : ℝ) 1,
      HasDerivAt F (-(x ^ r * Real.log x)) x := by
    intro x hx
    apply (hasDerivAt_rpowLogPrimitive hr hx.1).congr_of_eventuallyEq
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
    exact extendFrom_extends hraw_cont y hy
  have hneg_int : IntervalIntegrable
      (fun x : ℝ => -(x ^ r * Real.log x)) volume 0 1 := by
    apply intervalIntegrable_deriv_of_nonneg
      (by simpa [uIcc_of_le] using hF_cont)
    · simpa using hF_deriv
    · intro x hx
      simp only [min_eq_left zero_le_one, max_eq_right zero_le_one] at hx
      have hlog : Real.log x ≤ 0 := Real.log_nonpos hx.1.le hx.2.le
      rw [show -(x ^ r * Real.log x) = x ^ r * (-Real.log x) by ring]
      exact mul_nonneg (Real.rpow_nonneg hx.1.le r) (neg_nonneg.mpr hlog)
  convert hneg_int.neg using 1
  ext x
  simp

/-- The integral of `x ^ r * log x` from zero to one. -/
theorem integral_rpow_mul_log_zero_one {r : ℝ} (hr : -1 < r) :
    (∫ x : ℝ in 0..1, x ^ r * Real.log x) = -1 / (r + 1) ^ 2 := by
  have hint : IntervalIntegrable
      (fun x : ℝ => -(x ^ r * Real.log x)) volume 0 1 := by
    convert (intervalIntegrable_rpow_mul_log hr).neg using 1
    ext x
    simp
  have hneg :
      (∫ x : ℝ in 0..1, -(x ^ r * Real.log x)) = (r + 1)⁻¹ ^ 2 := by
    rw [integral_eq_sub_of_hasDerivAt_of_tendsto
      (f := fun x : ℝ =>
        x ^ (r + 1) / (r + 1) ^ 2 -
          x ^ (r + 1) * Real.log x / (r + 1))
      (fa := 0) (fb := (r + 1)⁻¹ ^ 2)
      (hint := hint)]
    · ring
    · norm_num
    · intro x hx
      exact hasDerivAt_rpowLogPrimitive hr hx.1
    · exact tendsto_rpowLogPrimitive_zero hr
    · exact tendsto_rpowLogPrimitive_one hr
  have hneg' : -(∫ x : ℝ in 0..1, x ^ r * Real.log x) =
      (r + 1)⁻¹ ^ 2 := by
    rw [← integral_neg]
    exact hneg
  calc
    (∫ x : ℝ in 0..1, x ^ r * Real.log x) = -((r + 1)⁻¹ ^ 2) := by
      linarith
    _ = -1 / (r + 1) ^ 2 := by field_simp

end intervalIntegral
