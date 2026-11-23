/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import RealRooted.Mathlib.NumberTheory.LSeries.RiemannXi.Theta
import RealRooted.RiemannHypothesis.TotalPositivity
import RealRooted.RiemannHypothesis.JensenSimple
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.LogDerivativeMeasure
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.LogMomentMassNearZero
import RealRooted.Mathlib.NumberTheory.LSeries.RiemannXi.Derivative


/-!
# RH logarithmic moment measures have no positive lower support gap

The gap obstruction is unconditional for nonpolynomial entire functions.
RH supplies the nonnegative logarithmic moment measure for each derivative
of the square-variable xi function. No simplicity of xi zeros is asserted.
-/

public section

open Complex MeasureTheory Set

namespace RealRooted

/-- Under RH, every derivative of the square-variable xi function has a
nonnegative logarithmic moment measure with positive mass below every positive
threshold. Thus its support cannot be separated from zero by a positive gap. -/
theorem exists_logDeriv_riemannXiTheta_moments_mass_near_zero
    (hRH : RiemannHypothesis) (n : ℕ) :
    ∃ mu : Measure ℝ, (∀ᵐ x ∂mu, 0 ≤ x) ∧
      (∀ k : ℕ, Integrable (fun x : ℝ => x ^ k) mu ∧
        (-1 : ℂ) ^ k * iteratedDeriv k
          (logDeriv (iteratedDeriv n riemannXiTheta)) 0 / k.factorial =
            ((∫ x : ℝ, x ^ k ∂mu : ℝ) : ℂ)) ∧
      ∀ c : ℝ, 0 < c → 0 < mu (Iio c) := by
  have hf := isLaguerrePolyaTypeI_iteratedDeriv_riemannXiTheta hRH n
  have h0 := iteratedDeriv_riemannXiTheta_zero_ne_zero n
  obtain ⟨_, a, mu, -, -, -, -, -, hsupport, hmom⟩ :=
    hf.exists_logDeriv_moment_measure h0
  refine ⟨mu, ?_, hmom, fun c hc => ?_⟩
  · have hs : ∀ᵐ x ∂mu, x ∈ Icc 0 (∑' i, a i) := ae_iff.mpr hsupport
    exact hs.mono fun _ hx => hx.1
  · exact measure_Iio_pos_of_logDeriv_moments_nonpolynomial
      (differentiable_iteratedDeriv_riemannXiTheta n) h0
      (iteratedDeriv_riemannXiTheta_ne_polynomial n) hmom hc

end RealRooted
