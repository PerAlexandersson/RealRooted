/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import TauCeti.Analysis.Analytic.TaylorSeries
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.RingTheory.PowerSeries.Log
import RealRooted.Mathlib.RingTheory.PowerSeries.LogarithmMul

/-!
# Taylor series and logarithmic derivatives

The one-variable Taylor series from Tau Ceti has coefficients given by normalized
iterated derivatives. It commutes with differentiation and sends an analytic
logarithmic derivative to the derivative of the normalized formal logarithm.
The function needs to be analytic only at the chosen point, where it is nonzero.
-/

public section

open Filter Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [CharZero 𝕜]
  {f : 𝕜 → 𝕜} {a : 𝕜}

/-- Taylor coefficients of an analytic function are normalized derivatives. -/
theorem AnalyticAt.coeff_taylorSeries_eq_iteratedDeriv (hf : AnalyticAt 𝕜 f a) (n : ℕ) :
    PowerSeries.coeff n (TauCeti.taylorSeries f a) = iteratedDeriv n f a / n.factorial := by
  rw [hf.hasFPowerSeriesAt.coeff_taylorSeries]
  exact FormalMultilinearSeries.coeff_ofScalars

/-- Taylor series commute with differentiation at analytic points. -/
theorem AnalyticAt.taylorSeries_deriv (hf : AnalyticAt 𝕜 f a) :
    TauCeti.taylorSeries (deriv f) a = PowerSeries.derivative (TauCeti.taylorSeries f a) := by
  ext n
  rw [hf.deriv.coeff_taylorSeries_eq_iteratedDeriv,
    PowerSeries.coeff_derivative, hf.coeff_taylorSeries_eq_iteratedDeriv,
    ← iteratedDeriv_succ', Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have hfac : (n.factorial : 𝕜) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  have hn : (n + 1 : 𝕜) ≠ 0 := Nat.cast_add_one_ne_zero n
  field_simp

/-- The analytic logarithmic derivative satisfies the formal product identity. -/
theorem AnalyticAt.taylorSeries_mul_logDeriv (hf : AnalyticAt 𝕜 f a) (h0 : f a ≠ 0) :
    TauCeti.taylorSeries f a * TauCeti.taylorSeries (logDeriv f) a =
      PowerSeries.derivative (TauCeti.taylorSeries f a) := by
  have hg : AnalyticAt 𝕜 (logDeriv f) a := hf.deriv.div hf h0
  have heq : f * logDeriv f =ᶠ[𝓝 a] deriv f := by
    filter_upwards [hf.continuousAt.eventually_ne h0] with z hz
    simp only [Pi.mul_apply, logDeriv_apply]
    exact mul_div_cancel₀ _ hz
  have h := TauCeti.taylorSeries_congr heq
  rwa [TauCeti.taylorSeries_mul hf hg, hf.taylorSeries_deriv] at h

/-- At a normalized analytic point, the derivative of the formal logarithm
is the Taylor series of the analytic logarithmic derivative. -/
theorem AnalyticAt.derivative_logOf_taylorSeries [Algebra ℚ 𝕜]
    (hf : AnalyticAt 𝕜 f a) (h0 : f a = 1) :
    PowerSeries.derivative (PowerSeries.logOf (TauCeti.taylorSeries f a)) =
      TauCeti.taylorSeries (logDeriv f) a := by
  have hc : PowerSeries.constantCoeff (TauCeti.taylorSeries f a) = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      hf.coeff_taylorSeries_eq_iteratedDeriv]
    simp [h0]
  apply (PowerSeries.isUnit_iff_constantCoeff.mpr (show
    IsUnit (PowerSeries.constantCoeff (TauCeti.taylorSeries f a)) by
      rw [hc]
      exact isUnit_one)).mul_left_cancel
  rw [PowerSeries.mul_derivative_logOf _ hc]
  exact (hf.taylorSeries_mul_logDeriv (by simp [h0])).symm

/-- Normalizing an analytic function by its nonzero constant value does not
change its logarithmic derivative series. -/
theorem AnalyticAt.derivative_logOf_normalized_taylorSeries [Algebra ℚ 𝕜]
    (hf : AnalyticAt 𝕜 f a) (h0 : f a ≠ 0) :
    PowerSeries.derivative (PowerSeries.logOf
      (PowerSeries.C (f a)⁻¹ * TauCeti.taylorSeries f a)) =
      TauCeti.taylorSeries (logDeriv f) a := by
  have hg : AnalyticAt 𝕜 (fun z => (f a)⁻¹ * f z) a := analyticAt_const.mul hf
  have h := hg.derivative_logOf_taylorSeries (by simp [h0])
  have heq : (fun z => (f a)⁻¹ * f z) = (fun _ => (f a)⁻¹) * f := rfl
  rw [heq, TauCeti.taylorSeries_mul analyticAt_const hf, TauCeti.taylorSeries_const] at h
  have hlog : logDeriv ((fun _ => (f a)⁻¹) * f) = logDeriv f := by
    funext z
    exact logDeriv_const_mul (f := f) z _ (inv_ne_zero h0)
  rwa [hlog] at h

/-- Taylor coefficients of an analytic logarithmic derivative equal the
coefficients obtained by differentiating the normalized formal logarithm. -/
theorem AnalyticAt.iteratedDeriv_logDeriv_eq_coeff_logOf [Algebra ℚ 𝕜]
    (hf : AnalyticAt 𝕜 f a) (h0 : f a ≠ 0) (n : ℕ) :
    iteratedDeriv n (logDeriv f) a / n.factorial =
      PowerSeries.coeff (n + 1) (PowerSeries.logOf
        (PowerSeries.C (f a)⁻¹ * TauCeti.taylorSeries f a)) * (n + 1) := by
  have hg : AnalyticAt 𝕜 (logDeriv f) a := hf.deriv.div hf h0
  have h := congrArg (PowerSeries.coeff n) (hf.derivative_logOf_normalized_taylorSeries h0)
  rw [PowerSeries.coeff_derivative, hg.coeff_taylorSeries_eq_iteratedDeriv] at h
  exact h.symm

/-- For real Taylor data, the real analytic logarithmic derivative coefficients
are the coefficients of the normalized real formal logarithm's derivative. -/
theorem AnalyticAt.re_iteratedDeriv_logDeriv_eq_coeff_logOf
    {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (h0 : f 0 ≠ 0)
    (hreal : ∀ k, Complex.ofReal (iteratedDeriv k f 0).re = iteratedDeriv k f 0) (n : ℕ) :
    (iteratedDeriv n (logDeriv f) 0).re / n.factorial =
      PowerSeries.coeff (n + 1) (PowerSeries.logOf (PowerSeries.mk
        (fun k => (iteratedDeriv k f 0).re / (k.factorial * (f 0).re)))) * (n + 1) := by
  have hreal0 : Complex.ofReal (f 0).re = f 0 := by simpa using hreal 0
  have h0re : (f 0).re ≠ 0 := by
    intro hz
    exact h0 (by rw [← hreal0, hz, Complex.ofReal_zero])
  let d : ℕ → ℝ := fun k => (iteratedDeriv k f 0).re / (k.factorial * (f 0).re)
  have hd : PowerSeries.constantCoeff (PowerSeries.mk d) = 1 := by simp [d, h0re]
  have hmap : PowerSeries.map Complex.ofRealHom (PowerSeries.mk d) =
      PowerSeries.C (f 0)⁻¹ * TauCeti.taylorSeries f 0 := by
    ext k
    rw [PowerSeries.coeff_map, PowerSeries.coeff_mk, PowerSeries.coeff_C_mul,
      hf.coeff_taylorSeries_eq_iteratedDeriv]
    simp only [Complex.ofRealHom_eq_coe, d, Complex.ofReal_div, Complex.ofReal_mul,
      Complex.ofReal_natCast, hreal, hreal0]
    ring
  have h := hf.iteratedDeriv_logDeriv_eq_coeff_logOf h0 n
  rw [← hmap, ← PowerSeries.map_logOf Complex.ofRealHom _ hd, PowerSeries.coeff_map] at h
  have hre := congrArg Complex.re h
  simpa only [Complex.div_natCast_re, Complex.ofRealHom_eq_coe, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.add_re, Complex.natCast_re,
    Complex.one_re, Complex.add_im, Complex.natCast_im, Complex.one_im, add_zero,
    mul_zero, sub_zero] using hre
