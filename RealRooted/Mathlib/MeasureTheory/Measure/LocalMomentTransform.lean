/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import RealRooted.Mathlib.MeasureTheory.Measure.AnalyticMomentSupport
import RealRooted.Mathlib.MeasureTheory.Measure.CompactMomentTransform
import Mathlib.Analysis.Analytic.OfScalars

/-!
# Recovering an analytic germ from its signed moments

An analytic germ whose signed Taylor coefficients are the genuine moments of a
positive measure agrees locally with its reciprocal-kernel integral. Analyticity
itself forces bounded support, so the conclusion does not require it as input.

For a logarithmic derivative this establishes the local transform identity in
Sokal's moment criterion. It does not yet continue that identity globally or
reconstruct the Type-I canonical product.
-/

public section

open Filter MeasureTheory Topology

/-- For a bounded moment measure, agreement of the actual complex Taylor
coefficients gives equality of germs with the reciprocal-kernel integral. -/
theorem AnalyticAt.eventuallyEq_integral_inv_of_bounded_moments
    {f : ℂ → ℂ} {mu : Measure ℝ} [IsFiniteMeasure mu]
    (hf : AnalyticAt ℂ f 0) {R : ℝ} (hR : 0 ≤ R)
    (hb : ∀ᵐ x ∂mu, |x| ≤ R)
    (hmom : ∀ n : ℕ, (-1 : ℂ) ^ n * iteratedDeriv n f 0 / n.factorial =
      ((∫ x : ℝ, x ^ n ∂mu : ℝ) : ℂ)) :
    f =ᶠ[𝓝 0] fun z ↦ ∫ x : ℝ, (1 + z * (x : ℂ))⁻¹ ∂mu := by
  have hsmall : ∀ᶠ z : ℂ in 𝓝 0, ‖z‖ * R < 1 := by
    exact (continuous_norm.mul_const R).continuousAt.eventually
      (gt_mem_nhds (by simp : ‖(0 : ℂ)‖ * R < 1))
  filter_upwards [hf.hasFPowerSeriesAt.eventually_hasSum, hsmall] with z hz hzb
  have hs : HasSum (fun n : ℕ ↦ (iteratedDeriv n f 0 / n.factorial) * z ^ n)
      (f z) := by
    simpa only [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, zero_add] using hz
  have hterm (n : ℕ) : (iteratedDeriv n f 0 / n.factorial) * z ^ n =
      (-z) ^ n * ((∫ x : ℝ, x ^ n ∂mu : ℝ) : ℂ) := by
    rw [← hmom n, mul_div_assoc]
    calc
      _ = ((-z) ^ n * (-1 : ℂ) ^ n) * (iteratedDeriv n f 0 / n.factorial) := by
        rw [← mul_pow]
        simp only [neg_mul_neg, mul_one, mul_comm]
      _ = _ := mul_assoc _ _ _
  exact (hs.congr_fun fun n ↦ (hterm n).symm).unique
    (Measure.hasSum_moments_integral_inv (mu := mu) hR hb hzb)

/-- Signed Taylor moments of an analytic germ determine its local reciprocal
transform. Every power must be integrable; equality of totalized integrals
without this hypothesis would not imply finiteness or compact support. -/
theorem AnalyticAt.eventuallyEq_integral_inv_of_moments
    {f : ℂ → ℂ} {mu : Measure ℝ} (hf : AnalyticAt ℂ f 0)
    (hint : ∀ n : ℕ, Integrable (fun x : ℝ ↦ x ^ n) mu)
    (hmom : ∀ n : ℕ, (-1 : ℂ) ^ n * iteratedDeriv n f 0 / n.factorial =
      ((∫ x : ℝ, x ^ n ∂mu : ℝ) : ℂ)) :
    f =ᶠ[𝓝 0] fun z ↦ ∫ x : ℝ, (1 + z * (x : ℂ))⁻¹ ∂mu := by
  have : IsFiniteMeasure mu :=
    (integrable_const_iff_isFiniteMeasure (one_ne_zero : (1 : ℝ) ≠ 0)).mp
      (by simpa only [pow_zero] using hint 0)
  obtain ⟨R, hR, hb⟩ :=
    Measure.exists_pos_ae_abs_le_of_analytic_moments (mu := mu) hf hint hmom
  exact hf.eventuallyEq_integral_inv_of_bounded_moments hR.le hb hmom

/-- The local analytic identity obtained from the signed logarithmic-derivative
moments in Sokal's criterion. The original function only needs to be analytic
and nonzero at the base point. No realness or growth hypothesis is added. -/
theorem AnalyticAt.eventuallyEq_logDeriv_integral_inv_of_moments
    {f : ℂ → ℂ} {mu : Measure ℝ} (hf : AnalyticAt ℂ f 0) (h0 : f 0 ≠ 0)
    (hint : ∀ n : ℕ, Integrable (fun x : ℝ ↦ x ^ n) mu)
    (hmom : ∀ n : ℕ, (-1 : ℂ) ^ n * iteratedDeriv n (logDeriv f) 0 / n.factorial =
      ((∫ x : ℝ, x ^ n ∂mu : ℝ) : ℂ)) :
    logDeriv f =ᶠ[𝓝 0] fun z ↦ ∫ x : ℝ, (1 + z * (x : ℂ))⁻¹ ∂mu := by
  exact (hf.deriv.div hf h0).eventuallyEq_integral_inv_of_moments hint hmom

end
