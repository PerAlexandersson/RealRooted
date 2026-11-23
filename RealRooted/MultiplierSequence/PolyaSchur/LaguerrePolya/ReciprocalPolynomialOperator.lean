/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Operator
public import Mathlib.Probability.Moments.ComplexMGF
import RealRooted.Hermite.FormalDifferential.Composition
import RealRooted.Hermite.FormalDifferential.Taylor
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.MGFPolynomialOperator
import RealRooted.Mathlib.Analysis.Analytic.TaylorInverse
import RealRooted.Mathlib.Probability.Moments.MGFTaylor
import RealRooted.Mathlib.Analysis.Analytic.TaylorSeries
import Mathlib.Tactic.TypeStar

/-!
# Reciprocal moment-generating germs invert polynomial convolution

A local reciprocal identity suffices. No global analyticity of the moment-
generating function, additional reality hypothesis on the reciprocal, or
real-rootedness assumption is used.
-/

public section

open Complex Filter MeasureTheory Polynomial ProbabilityTheory Set Topology
open RealRooted.HermitePoulain

namespace RealRooted

/-- A real mapped Taylor series identifies the formal and analytic polynomial
operators. This is a coefficient consequence of analyticity at zero only. -/
private theorem formal_eq_taylor_of_map {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0)
    (A : PowerSeries ℝ) (hA : TauCeti.taylorSeries f 0 = PowerSeries.map ofRealHom A)
    (p : ℝ[X]) : formalDifferentialOperator A p = taylorDifferentialOperator f p := by
  apply formalDifferentialOperator_eq_taylor
  intro k
  have h := congrArg Complex.re (congrArg (PowerSeries.coeff k) hA)
  rw [hf.coeff_taylorSeries_eq_iteratedDeriv, PowerSeries.coeff_map] at h
  simpa only [ofRealHom_eq_coe, ofReal_re] using h.symm

/-- A germ reciprocal to an actual complex MGF acts as the inverse polynomial
translation-average operator. Its real Taylor coefficients are derived from
the reciprocal identity and the real moment coefficients, not assumed. -/
theorem integral_eval_taylorDifferentialOperator_reciprocal
    {Ω : Type*} [MeasurableSpace Ω] {mu : Measure Ω} {Y : Ω → ℝ} {f : ℂ → ℂ}
    (h0 : 0 ∈ interior (integrableExpSet Y mu)) (hf : AnalyticAt ℂ f 0)
    (hrecip : (fun z => complexMGF Y mu z * f z) =ᶠ[𝓝 0] fun _ => 1)
    (p : ℝ[X]) (x : ℝ) :
    (∫ w, (taylorDifferentialOperator f p).eval (x + Y w) ∂mu) = p.eval x := by
  let A : PowerSeries ℝ := PowerSeries.mk fun k => (∫ w, Y w ^ k ∂mu) / k.factorial
  have hg : AnalyticAt ℂ (complexMGF Y mu) 0 :=
    analyticAt_complexMGF (by simpa only [zero_re] using h0)
  have hA : TauCeti.taylorSeries (complexMGF Y mu) 0 = PowerSeries.map ofRealHom A :=
    taylorSeries_complexMGF_zero h0
  obtain ⟨hA0, hF⟩ := hf.taylorSeries_eq_map_inv_of_mul_eq_one hg ofRealHom A hA
    (by simpa only [mul_comm] using hrecip)
  rw [← taylorDifferentialOperator_complexMGF_eval h0,
    ← formal_eq_taylor_of_map hf A⁻¹ hF,
    ← formal_eq_taylor_of_map hg A hA,
    ← formalDifferentialOperator_mul, PowerSeries.mul_inv_cancel A hA0,
    formalDifferentialOperator_one]

/-- The reciprocal of a one-sided Laplace germ inverts polynomial convolution.
Support and PF assumptions belong to the subsequent root-location theorem,
not to this analytic and algebraic identity. -/
theorem integral_eval_taylorDifferentialOperator_laplace
    {Ω : Type*} [MeasurableSpace Ω] {mu : Measure Ω} {T : Ω → ℝ} {f : ℂ → ℂ}
    (h0 : 0 ∈ interior (integrableExpSet (fun w => -T w) mu))
    (hf : AnalyticAt ℂ f 0)
    (hrecip : (fun z => (∫ w, exp (-z * (T w : ℂ)) ∂mu) * f z)
      =ᶠ[𝓝 0] fun _ => 1) (p : ℝ[X]) (x : ℝ) :
    (∫ w, (taylorDifferentialOperator f p).eval (x - T w) ∂mu) = p.eval x := by
  have hrecip' : (fun z => complexMGF (fun w => -T w) mu z * f z)
      =ᶠ[𝓝 0] fun _ => 1 := by
    simpa only [complexMGF, ofReal_neg, mul_neg, neg_mul] using hrecip
  simpa only [sub_eq_add_neg] using
    integral_eval_taylorDifferentialOperator_reciprocal h0 hf hrecip' p x

end RealRooted
