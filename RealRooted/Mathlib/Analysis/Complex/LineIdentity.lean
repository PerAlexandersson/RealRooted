/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Complex.Basic

/-!
# The identity principle along a line

Vanishing on a real line segment through an interior point determines an
analytic function on a connected domain.
-/

public section

open Complex Filter Topology

/-- An analytic function on a connected domain which vanishes along a line
near one point vanishes throughout the domain. -/
theorem AnalyticOnNhd.eqOn_zero_of_line_eq_zero {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : ℂ → E} {U : Set ℂ} {z₀ v : ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hU : IsPreconnected U) (hz₀ : z₀ ∈ U)
    (hv : v ≠ 0) (hzero : ∀ᶠ t : ℝ in 𝓝 0, f (z₀ + (t : ℂ) * v) = 0) :
    Set.EqOn f 0 U := by
  have ht : Tendsto (fun t : ℝ => z₀ + (t : ℂ) * v)
      (𝓝[≠] 0) (𝓝[≠] z₀) := by
    have hcont : Continuous (fun t : ℝ => z₀ + (t : ℂ) * v) := by fun_prop
    simpa only [ofReal_zero, zero_mul, add_zero] using
      hcont.continuousWithinAt.tendsto_nhdsWithin (x := 0) (fun t ht => by
        simpa [hv] using ht)
  exact hf.eqOn_zero_of_preconnected_of_frequently_eq_zero hU hz₀
    (ht.frequently (hzero.filter_mono nhdsWithin_le_nhds).frequently)
