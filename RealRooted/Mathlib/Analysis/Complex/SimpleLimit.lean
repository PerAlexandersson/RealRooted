/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
import RealRooted.Mathlib.Analysis.Complex.PolynomialLimitCoeff
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Stability of simple zeros on a compact set

A positive lower bound for `norm f + norm (deriv f)` prevents nearby functions
and their derivatives from vanishing together. Locally uniform convergence of
entire functions supplies both uniform approximations, including at boundary points.
-/

public section

open Filter Topology

namespace Complex

/-- Locally uniformly convergent entire functions eventually have no multiple
zeros on a compact set where the limit has no multiple zeros. No nonempty-set
or real-rootedness hypothesis is needed. -/
theorem eventually_deriv_ne_zero_on_isCompact {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    (hlim : TendstoLocallyUniformly F f atTop)
    (hF : ∀ n, Differentiable ℂ (F n)) (hf : Differentiable ℂ f)
    {K : Set ℂ} (hK : IsCompact K)
    (hsimple : ∀ z ∈ K, f z = 0 → deriv f z ≠ 0) :
    ∀ᶠ n in atTop, ∀ z ∈ K, F n z = 0 → deriv (F n) z ≠ 0 := by
  have hc : Continuous (fun z => ‖f z‖ + ‖deriv f z‖) :=
    hf.continuous.norm.add hf.deriv.continuous.norm
  have hpos (z : ℂ) (hz : z ∈ K) : 0 < ‖f z‖ + ‖deriv f z‖ := by
    by_cases hzero : f z = 0
    · simpa only [hzero, norm_zero, zero_add] using norm_pos_iff.mpr (hsimple z hz hzero)
    · exact add_pos_of_pos_of_nonneg (norm_pos_iff.mpr hzero) (norm_nonneg _)
  obtain ⟨ε, hε, hbound⟩ := hK.exists_forall_le' hc.continuousOn hpos
  have hdlim : TendstoLocallyUniformly (fun n => deriv (F n)) (deriv f) atTop := by
    simpa only [iteratedDeriv_one] using hlim.iteratedDeriv hF 1
  have hv := tendstoLocallyUniformly_iff_forall_isCompact.mp hlim K hK
  have hd := tendstoLocallyUniformly_iff_forall_isCompact.mp hdlim K hK
  have hv' := (Metric.tendstoUniformlyOn_iff.mp hv) (ε / 3) (by positivity)
  have hd' := (Metric.tendstoUniformlyOn_iff.mp hd) (ε / 3) (by positivity)
  filter_upwards [hv', hd'] with n hn hdn z hz hzero
  intro hdzero
  have hvsmall : ‖f z‖ < ε / 3 := by
    simpa only [hzero, dist_zero_right] using hn z hz
  have hdsmall : ‖deriv f z‖ < ε / 3 := by
    simpa only [hdzero, dist_zero_right] using hdn z hz
  have hlow := hbound z hz
  linarith

end Complex
