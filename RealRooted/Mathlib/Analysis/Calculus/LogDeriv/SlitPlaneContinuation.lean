/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.Analysis.Complex.Basic
import RealRooted.Mathlib.Analysis.Calculus.LogDeriv.ZeroFree
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Continuing a logarithmic derivative from the origin to the slit plane

An entire function nonzero at the origin has no zeros in the slit plane if
its local logarithmic derivative agrees with a function holomorphic there.
Continue the equation `f' = g f`, which stays analytic at possible zeros,
then use analytic orders to exclude them. No positive-axis nonvanishing or
conjugation hypothesis is assumed.
-/

public section

open Complex Filter Set Topology

/-- A local logarithmic derivative with a holomorphic slit-plane continuation
agrees with it globally on that plane, and the original entire function is
nowhere zero there. The origin belongs to the local germ, not to the slit plane. -/
theorem Differentiable.eqOn_logDeriv_of_eventuallyEq
    {f g : ℂ → ℂ} (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0)
    (hg : AnalyticOnNhd ℂ g slitPlane) (hlocal : logDeriv f =ᶠ[𝓝 0] g) :
    EqOn (logDeriv f) g slitPlane ∧ ∀ z ∈ slitPlane, f z ≠ 0 := by
  have heq : ∀ᶠ z in 𝓝 0, _root_.deriv f z = g z * f z ∧ f z ≠ 0 := by
    filter_upwards [hlocal, (hf.analyticAt 0).continuousAt.eventually_ne h0]
      with z hz hzn
    refine ⟨?_, hzn⟩
    rw [← hz, logDeriv_apply, div_mul_cancel₀ _ hzn]
  obtain ⟨s, hs, hso, h0s⟩ := eventually_nhds_iff.mp heq
  obtain ⟨r, hr, hrs⟩ := Metric.mem_nhds_iff.mp (hso.mem_nhds h0s)
  have has : ((r / 2 : ℝ) : ℂ) ∈ s := by
    apply hrs
    simpa only [Metric.mem_ball, dist_zero_right, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (half_pos hr)] using half_lt_self hr
  have ha : ((r / 2 : ℝ) : ℂ) ∈ slitPlane :=
    ofReal_mem_slitPlane.mpr (half_pos hr)
  have hfa : AnalyticOnNhd ℂ f slitPlane := fun z _ ↦ hf.analyticAt z
  have hda : AnalyticOnNhd ℂ (_root_.deriv f) slitPlane := fun z _ ↦ hf.deriv.analyticAt z
  have hga : AnalyticOnNhd ℂ (fun z ↦ g z * f z) slitPlane :=
    fun z hz ↦ (hg z hz).mul (hfa z hz)
  have hconn :=
    (starConvex_one_slitPlane.isPathConnected one_mem_slitPlane).isConnected.isPreconnected
  have hode : EqOn (_root_.deriv f) (fun z ↦ g z * f z) slitPlane :=
    hda.eqOn_of_preconnected_of_eventuallyEq hga hconn ha
      (Filter.Eventually.mono (hso.mem_nhds has) fun z hz ↦ (hs z hz).1)
  have hne := hfa.ne_zero_of_deriv_eq_mul hg isOpen_slitPlane hconn ha
    (hs _ has).2 hode
  refine ⟨?_, hne⟩
  intro z hz
  rw [logDeriv_apply, hode hz, mul_div_cancel_right₀ _ (hne z hz)]

end
