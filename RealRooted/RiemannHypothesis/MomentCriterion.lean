/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import RealRooted.Mathlib.NumberTheory.LSeries.RiemannXi.Theta
import RealRooted.Mathlib.Analysis.Calculus.LogDeriv.MomentContinuation
import RealRooted.RiemannHypothesis.MomentMeasure

/-!
# A local moment-measure criterion for RH

RH is equivalent to the signed logarithmic-derivative Taylor coefficients of
the square-variable xi function being genuine moments of a positive measure
on `[0,∞)`. Compact support and finiteness are consequences, not hypotheses.
The forward measure construction was already proved; local analytic
continuation supplies the converse.

This criterion concerns actual complex coefficients and integrable moments.
It is not a claim of the unrestricted Type-I converse for every entire function.
-/

public section

open Complex MeasureTheory

namespace RealRooted

/-- Genuine nonnegative moment data for the actual signed complex coefficients
of the xi logarithmic derivative imply Mathlib's RH. -/
theorem riemannHypothesis_of_logDeriv_moments
    {mu : Measure ℝ} (hpos : ∀ᵐ x ∂mu, 0 ≤ x)
    (hint : ∀ n : ℕ, Integrable (fun x : ℝ ↦ x ^ n) mu)
    (hmom : ∀ n : ℕ,
      (-1 : ℂ) ^ n * iteratedDeriv n (logDeriv riemannXiTheta) 0 / n.factorial =
        ((∫ x : ℝ, x ^ n ∂mu : ℝ) : ℂ)) :
    RiemannHypothesis := by
  apply riemannHypothesis_iff_riemannXiTheta_zeros.mpr
  intro z hz
  exact (differentiable_riemannXiTheta.zeros_nonpos_of_logDeriv_moments
    riemannXiTheta_zero_ne_zero hpos hint hmom z hz).1

/-- RH is equivalent to a genuine positive moment measure for the actual
complex signed logarithmic-derivative coefficients at zero. The zeroth moment
ensures finiteness, and analyticity forces compact support. -/
theorem riemannHypothesis_iff_exists_logDeriv_moment_measure :
    RiemannHypothesis ↔ ∃ mu : Measure ℝ, (∀ᵐ x ∂mu, 0 ≤ x) ∧
      ∀ n : ℕ, Integrable (fun x : ℝ ↦ x ^ n) mu ∧
        (-1 : ℂ) ^ n * iteratedDeriv n (logDeriv riemannXiTheta) 0 / n.factorial =
          ((∫ x : ℝ, x ^ n ∂mu : ℝ) : ℂ) := by
  constructor
  · intro hRH
    obtain ⟨_, a, mu, _, _, _, _, _, hsupport, hmom⟩ :=
      exists_logDeriv_riemannXiTheta_moment_measure hRH 0
    refine ⟨mu, ?_, ?_⟩
    · have hs : ∀ᵐ x ∂mu, x ∈ Set.Icc 0 (∑' i, a i) := ae_iff.mpr hsupport
      exact hs.mono fun _ hx ↦ hx.1
    · simpa only [iteratedDeriv_zero] using hmom
  · rintro ⟨mu, hpos, hmom⟩
    exact riemannHypothesis_of_logDeriv_moments hpos (fun n ↦ (hmom n).1)
      (fun n ↦ (hmom n).2)

end RealRooted
