/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import RealRooted.Mathlib.MeasureTheory.Measure.MomentDeterminacy
import Mathlib.Analysis.Analytic.OfScalars

/-!
# Compact support from analytic moment coefficients

Taylor coefficients of an analytic germ satisfy a geometric bound. If its even
coefficients are the even moments of a positive measure, the existing moment
tail estimate forces bounded support. No nonnegative-support assumption or
nonzero-measure assumption is needed for this step.
-/

public section

open Filter MeasureTheory Topology

/-- Normalized derivatives of an analytic complex germ have a geometric bound. -/
theorem AnalyticAt.exists_norm_iteratedDeriv_div_factorial_le
    {f : ℂ → ℂ} {a : ℂ} (hf : AnalyticAt ℂ f a) :
    ∃ C > 0, ∃ R > 0, ∀ n : ℕ,
      ‖iteratedDeriv n f a / n.factorial‖ ≤ C * R ^ n := by
  let p := FormalMultilinearSeries.ofScalars ℂ
    (fun n ↦ iteratedDeriv n f a / n.factorial)
  have hp : 0 < p.radius := hf.hasFPowerSeriesAt.radius_pos
  obtain ⟨r, hr0, hrp⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hp
  have hr : (0 : NNReal) < r := ENNReal.coe_pos.mp hr0
  obtain ⟨C, hC, hbound⟩ := p.norm_le_div_pow_of_pos_of_lt_radius hr hrp
  refine ⟨C, hC, (r : ℝ)⁻¹, inv_pos.mpr hr, fun n ↦ ?_⟩
  simpa only [p, FormalMultilinearSeries.ofScalars_norm, div_eq_mul_inv, inv_pow]
    using hbound n

namespace MeasureTheory.Measure

/-- If the even moments are the even Taylor coefficients of an analytic germ,
the measure has bounded support. Integrability of the zeroth moment includes
finiteness; no finiteness typeclass is an additional hypothesis. -/
theorem exists_pos_ae_abs_le_of_analytic_even_moments
    {mu : Measure ℝ} {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0)
    (hint : ∀ n : ℕ, Integrable (fun x : ℝ ↦ x ^ (2 * n)) mu)
    (hmom : ∀ n : ℕ, iteratedDeriv (2 * n) f 0 / (2 * n).factorial =
      ((∫ x : ℝ, x ^ (2 * n) ∂mu : ℝ) : ℂ)) :
    ∃ R > 0, ∀ᵐ x ∂mu, |x| ≤ R := by
  obtain ⟨C, _, R, hR, hbound⟩ := hf.exists_norm_iteratedDeriv_div_factorial_le
  have hm (n : ℕ) : (∫ x : ℝ, x ^ (2 * n) ∂mu) ≤ C * R ^ (2 * n) := by
    calc
      _ ≤ |∫ x : ℝ, x ^ (2 * n) ∂mu| := le_abs_self _
      _ = ‖iteratedDeriv (2 * n) f 0 / (2 * n).factorial‖ := by
        rw [hmom n, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ _ := hbound (2 * n)
  have htail := measure_abs_ge_eq_zero_of_even_moment_bound hR.le
    (lt_add_one R) hint hm
  refine ⟨R + 1, add_pos hR zero_lt_one, ae_iff.mpr ?_⟩
  apply measure_mono_null _ htail
  intro x hx
  exact (lt_of_not_ge hx).le

/-- Signed complex Taylor coefficients which are genuine power moments force
bounded support. The equality is in `ℂ`, rather than merely after taking real
parts. The zero measure and a zero analytic germ are included. -/
theorem exists_pos_ae_abs_le_of_analytic_moments
    {mu : Measure ℝ} {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0)
    (hint : ∀ n : ℕ, Integrable (fun x : ℝ ↦ x ^ n) mu)
    (hmom : ∀ n : ℕ, (-1 : ℂ) ^ n * iteratedDeriv n f 0 / n.factorial =
      ((∫ x : ℝ, x ^ n ∂mu : ℝ) : ℂ)) :
    ∃ R > 0, ∀ᵐ x ∂mu, |x| ≤ R := by
  apply exists_pos_ae_abs_le_of_analytic_even_moments hf (fun n ↦ hint (2 * n))
  intro n
  simpa only [pow_mul, neg_one_sq, one_pow, one_mul] using hmom (2 * n)

/-- A nonnegative moment measure of an analytic germ is carried by a compact
interval in the closed positive half-line. An atom at zero is permitted. -/
theorem exists_pos_ae_mem_Icc_of_analytic_moments
    {mu : Measure ℝ} {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0)
    (hpos : ∀ᵐ x ∂mu, 0 ≤ x)
    (hint : ∀ n : ℕ, Integrable (fun x : ℝ ↦ x ^ n) mu)
    (hmom : ∀ n : ℕ, (-1 : ℂ) ^ n * iteratedDeriv n f 0 / n.factorial =
      ((∫ x : ℝ, x ^ n ∂mu : ℝ) : ℂ)) :
    ∃ R > 0, ∀ᵐ x ∂mu, x ∈ Set.Icc 0 R := by
  obtain ⟨R, hR, hb⟩ := exists_pos_ae_abs_le_of_analytic_moments hf hint hmom
  refine ⟨R, hR, ?_⟩
  filter_upwards [hpos, hb] with x hx hxb
  exact ⟨hx, (le_abs_self x).trans hxb⟩

end MeasureTheory.Measure

end
