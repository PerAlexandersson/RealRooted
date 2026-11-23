/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import TauCeti.Analysis.CompletelyMonotone.Stieltjes.Basic
import RealRooted.Mathlib.Analysis.Calculus.LogDeriv.SlitPlaneContinuation
import RealRooted.Mathlib.MeasureTheory.Measure.LocalMomentTransform
import RealRooted.Mathlib.MeasureTheory.Measure.NonnegativeMomentTransform
import Mathlib.Analysis.Complex.CauchyIntegral
import TauCeti.Analysis.Complex.SlitPlane

/-!
# Global continuation from logarithmic-derivative moments

For an entire function nonzero at zero, genuine nonnegative moment data for
the actual complex logarithmic-derivative coefficients give a global Stieltjes
transform on the slit plane. Its zeros are consequently nonpositive real.

The unrestricted normalized Type-I conclusion still requires canonical-product
reconstruction. It is not asserted here merely from this zero-location result.
-/

public section

open Complex Filter MeasureTheory Set Topology

/-- Local signed logarithmic-derivative moments give the actual transform
identity throughout the slit plane and exclude zeros there. Compact support,
positive-axis nonvanishing and conjugation symmetry are not input hypotheses. -/
theorem Differentiable.eqOn_logDeriv_integral_inv_of_moments
    {f : ℂ → ℂ} {mu : Measure ℝ} (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0)
    (hpos : ∀ᵐ x ∂mu, 0 ≤ x)
    (hint : ∀ n : ℕ, Integrable (fun x : ℝ ↦ x ^ n) mu)
    (hmom : ∀ n : ℕ, (-1 : ℂ) ^ n * iteratedDeriv n (logDeriv f) 0 / n.factorial =
      ((∫ x : ℝ, x ^ n ∂mu : ℝ) : ℂ)) :
    EqOn (logDeriv f) (fun z ↦ ∫ x : ℝ, (1 + z * (x : ℂ))⁻¹ ∂mu) slitPlane ∧
      ∀ z ∈ slitPlane, f z ≠ 0 := by
  have : IsFiniteMeasure mu :=
    (integrable_const_iff_isFiniteMeasure (one_ne_zero : (1 : ℝ) ≠ 0)).mp
      (by simpa only [pow_zero] using hint 0)
  exact hf.eqOn_logDeriv_of_eventuallyEq h0
    (Measure.analyticOnNhd_integral_inv_one_add_mul_of_ae_nonneg hpos)
    ((hf.analyticAt 0).eventuallyEq_logDeriv_integral_inv_of_moments h0 hint hmom)

/-- Genuine nonnegative moments of the actual complex logarithmic-derivative
coefficients force all zeros of the entire function to be nonpositive real. -/
theorem Differentiable.zeros_nonpos_of_logDeriv_moments
    {f : ℂ → ℂ} {mu : Measure ℝ} (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0)
    (hpos : ∀ᵐ x ∂mu, 0 ≤ x)
    (hint : ∀ n : ℕ, Integrable (fun x : ℝ ↦ x ^ n) mu)
    (hmom : ∀ n : ℕ, (-1 : ℂ) ^ n * iteratedDeriv n (logDeriv f) 0 / n.factorial =
      ((∫ x : ℝ, x ^ n ∂mu : ℝ) : ℂ)) :
    ∀ z : ℂ, f z = 0 → z.im = 0 ∧ z.re ≤ 0 := by
  have hne := (hf.eqOn_logDeriv_integral_inv_of_moments h0 hpos hint hmom).2
  intro z hz
  have hnot : z ∉ slitPlane := fun hmem ↦ hne z hmem hz
  exact ⟨im_eq_zero_of_notMem_slitPlane hnot,
    le_of_not_gt fun hre ↦ hnot (mem_slitPlane_iff.mpr (Or.inl hre))⟩

/-- The logarithmic derivative on the positive axis is a Stieltjes function
under the local moment hypotheses. This derives the global condition from
local complex coefficients, rather than assuming it. -/
theorem Differentiable.isStieltjesFunction_logDeriv_of_moments
    {f : ℂ → ℂ} {mu : Measure ℝ} (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0)
    (hpos : ∀ᵐ x ∂mu, 0 ≤ x)
    (hint : ∀ n : ℕ, Integrable (fun x : ℝ ↦ x ^ n) mu)
    (hmom : ∀ n : ℕ, (-1 : ℂ) ^ n * iteratedDeriv n (logDeriv f) 0 / n.factorial =
      ((∫ x : ℝ, x ^ n ∂mu : ℝ) : ℂ)) :
    TauCeti.IsStieltjesFunction (fun t : ℝ ↦ (logDeriv f t).re) := by
  have : IsFiniteMeasure mu :=
    (integrable_const_iff_isFiniteMeasure (one_ne_zero : (1 : ℝ) ≠ 0)).mp
      (by simpa only [pow_zero] using hint 0)
  have heq := (hf.eqOn_logDeriv_integral_inv_of_moments h0 hpos hint hmom).1
  apply (Measure.isStieltjesFunction_integral_inv_one_add_mul_of_ae_nonneg hpos).congr
  intro t ht
  exact congrArg Complex.re (heq (ofReal_mem_slitPlane.mpr ht))

end
