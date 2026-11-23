/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Analysis.Calculus.FDeriv.Basic
import TauCeti.Analysis.Complex.RealIdentity
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Nonzero real evaluations of an entire function
-/

public section

open Filter Topology

/-- A nonzero entire function has no real zeros in some punctured
neighborhood of each real point. The real point itself may be a zero. -/
theorem Differentiable.eventually_ofReal_ne_zero {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hne : f ≠ 0) (x : ℝ) :
    ∀ᶠ y : ℝ in 𝓝[≠] x, f y ≠ 0 := by
  have ha : AnalyticOnNhd ℝ (fun y : ℝ ↦ f y) Set.univ := by
    intro y _
    exact ((hf.analyticAt y).restrictScalars (𝕜 := ℝ)).comp
      (Complex.ofRealCLM.analyticAt y)
  rcases ha.eqOn_zero_or_eventually_ne_zero_of_preconnected isPreconnected_univ with h | h
  · exact (hne (hf.eq_of_ofReal_eq (differentiable_const 0)
      (fun y ↦ h (Set.mem_univ y)))).elim
  · simpa only [Set.mem_univ, forall_const] using
      (eventually_codiscreteWithin_iff_forall_eventually_nhdsNE.mp h) x (Set.mem_univ _)
