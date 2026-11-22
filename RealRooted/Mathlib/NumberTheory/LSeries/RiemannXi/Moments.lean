/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import RealRooted.Mathlib.NumberTheory.LSeries.RiemannXi.Kernel
import Mathlib.MeasureTheory.Integral.Bochner.Set
import RealRooted.Mathlib.Analysis.MellinTransform.LogMoments
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Logarithmic moments of the theta kernel

The positive moments at exponent `1/4` obey `M(n+1) ≤ (n+1) M(n)`.
This deliberately coarse bound suffices for positivity of the even xi derivatives.
-/

@[expose] public section

open Real Set Filter MeasureTheory
open scoped Topology

/-- The logarithmic moments entering the central derivatives of completed zeta. -/
noncomputable def riemannXiMoment (n : ℕ) : ℝ :=
  ∫ t in Ioi (1 : ℝ), riemannThetaKernel t * log t ^ n * t ^ (-3 / 4 : ℝ)

private theorem kernel_continuous : ContinuousOn riemannThetaKernel (Ici 1) :=
  continuousOn_riemannThetaKernel.mono (fun _ ht => zero_lt_one.trans_le ht)

private theorem moment_integrable (n : ℕ) :
    IntegrableOn (fun t : ℝ => riemannThetaKernel t * log t ^ n * t ^ (-3 / 4 : ℝ))
      (Ioi 1) :=
  integrableOn_mul_log_pow_rpow kernel_continuous isBigO_riemannThetaKernel_rpow n _

/-- Every logarithmic theta moment is strictly positive. -/
theorem riemannXiMoment_pos (n : ℕ) : 0 < riemannXiMoment n := by
  have hp (t : ℝ) (ht : t ∈ Ioi 1) :
      0 < riemannThetaKernel t * log t ^ n * t ^ (-3 / 4 : ℝ) :=
    mul_pos (mul_pos (riemannThetaKernel_pos (zero_lt_one.trans ht))
      (pow_pos (log_pos ht) n)) (rpow_pos_of_pos (zero_lt_one.trans ht) _)
  rw [riemannXiMoment, setIntegral_pos_iff_support_of_nonneg_ae
    (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => (hp t ht).le) (moment_integrable n)]
  have he : Function.support (fun t : ℝ => riemannThetaKernel t * log t ^ n *
      t ^ (-3 / 4 : ℝ)) ∩ Ioi 1 = Ioi 1 := by
    apply inter_eq_right.mpr
    exact fun t ht => (hp t ht).ne'
  rw [he]
  simp

private theorem quarter_rpow {t : ℝ} (ht : 0 < t) :
    t ^ (1 / 4 : ℝ) = t * t ^ (-3 / 4 : ℝ) := by
  rw [show (1 / 4 : ℝ) = 1 + (-3 / 4) by norm_num, rpow_add ht, rpow_one]

private theorem weighted_kernel_deriv_le {t : ℝ} (ht : 1 < t) :
    riemannThetaKernelDeriv t * t ^ (1 / 4 : ℝ) +
      riemannThetaKernel t * (1 / 4 : ℝ) * t ^ (-3 / 4 : ℝ) ≤
        -(riemannThetaKernel t * t ^ (-3 / 4 : ℝ)) := by
  have ht0 := zero_lt_one.trans ht
  have hf := (riemannThetaKernel_pos ht0).le
  have hd := riemannThetaKernelDeriv_le ht0
  have hd0 : riemannThetaKernelDeriv t ≤ 0 :=
    hd.trans (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr pi_pos.le) hf)
  have htd := mul_le_mul_of_nonpos_right ht.le hd0
  have hp := mul_nonneg (sub_nonneg.mpr two_le_pi) hf
  have hmain : t * riemannThetaKernelDeriv t + riemannThetaKernel t / 4 ≤
      -riemannThetaKernel t := by nlinarith
  rw [quarter_rpow ht0]
  nlinarith [mul_le_mul_of_nonneg_right hmain (rpow_pos_of_pos ht0 (-3 / 4 : ℝ)).le]

/-- Consecutive moments satisfy a factorial bound, obtained by integration by parts. -/
theorem riemannXiMoment_succ_le (n : ℕ) :
    riemannXiMoment (n + 1) ≤ (n + 1 : ℝ) * riemannXiMoment n := by
  let u (t : ℝ) := riemannThetaKernel t * t ^ (1 / 4 : ℝ)
  let u' (t : ℝ) := riemannThetaKernelDeriv t * t ^ (1 / 4 : ℝ) +
    riemannThetaKernel t * (1 / 4 : ℝ) * t ^ (-3 / 4 : ℝ)
  let v (t : ℝ) := log t ^ (n + 1)
  let v' (t : ℝ) := (n + 1 : ℝ) * log t ^ n / t
  have hu (t : ℝ) (ht : t ∈ Ioi 1) : HasDerivAt u (u' t) t := by
    convert (hasDerivAt_riemannThetaKernel (zero_lt_one.trans ht)).fun_mul
      (hasDerivAt_rpow_const (p := (1 / 4 : ℝ)) (Or.inl (zero_lt_one.trans ht).ne')) using 1
    dsimp [u, u']
    norm_num
    ring
  have hv (t : ℝ) (ht : t ∈ Ioi 1) : HasDerivAt v (v' t) t := by
    convert ((hasDerivAt_log (zero_lt_one.trans ht).ne').pow (n + 1)) using 1
    dsimp [v, v']
    simp only [Nat.cast_add, Nat.cast_one]
    ring
  have huv (t : ℝ) (ht : t ∈ Ioi 1) :
      u t * v' t = (n + 1 : ℝ) *
        (riemannThetaKernel t * log t ^ n * t ^ (-3 / 4 : ℝ)) := by
    dsimp [u, v']
    rw [quarter_rpow (zero_lt_one.trans ht)]
    field_simp [(zero_lt_one.trans ht).ne']
  have hu'v (t : ℝ) : u' t * v t =
      riemannThetaKernelDeriv t * log t ^ (n + 1) * t ^ (1 / 4 : ℝ) +
        (1 / 4 : ℝ) * (riemannThetaKernel t * log t ^ (n + 1) * t ^ (-3 / 4 : ℝ)) := by
    dsimp [u', v]
    ring
  have hi₁ : IntegrableOn (u * v') (Ioi 1) := by
    apply IntegrableOn.congr_fun ((moment_integrable n).const_mul (n + 1 : ℝ))
      (fun t ht => (huv t ht).symm) measurableSet_Ioi
  have hi₂ : IntegrableOn (u' * v) (Ioi 1) := by
    apply ((integrableOn_mul_log_pow_rpow continuousOn_riemannThetaKernelDeriv
      isBigO_riemannThetaKernelDeriv_rpow (n + 1) (1 / 4)).add
      ((moment_integrable (n + 1)).const_mul (1 / 4 : ℝ))).congr_fun
        (fun t _ => (hu'v t).symm) measurableSet_Ioi
  have hc : ContinuousAt riemannThetaKernel 1 :=
    continuousOn_riemannThetaKernel.continuousAt (Ioi_mem_nhds zero_lt_one)
  have hzero : Tendsto (u * v) (𝓝[>] 1) (𝓝 0) := by
    have h : ContinuousAt (u * v) 1 := by
      dsimp [u, v]
      fun_prop (disch := norm_num)
    simpa [u, v] using h.tendsto.mono_left nhdsWithin_le_nhds
  have hinfty : Tendsto (u * v) atTop (𝓝 0) := by
    convert tendsto_mul_log_pow_rpow_zero isBigO_riemannThetaKernel_rpow (n + 1) (1 / 4) using 1
    funext t
    dsimp [u, v]
    ring
  have hibp := integral_Ioi_mul_deriv_eq_deriv_mul hu hv hi₁ hi₂ hzero hinfty
  have heval : (∫ t in Ioi (1 : ℝ), u t * v' t) = (n + 1 : ℝ) * riemannXiMoment n := by
    rw [setIntegral_congr_fun measurableSet_Ioi huv, integral_const_mul]
    rfl
  rw [heval, sub_zero, zero_sub] at hibp
  rw [riemannXiMoment, hibp, ← integral_neg]
  apply integral_mono_ae (moment_integrable (n + 1)) hi₂.neg
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have hlog : 0 ≤ log t ^ (n + 1) := pow_nonneg (log_pos ht).le _
  have h := mul_le_mul_of_nonneg_right (weighted_kernel_deriv_le ht) hlog
  dsimp [u', v]
  nlinarith [h]
