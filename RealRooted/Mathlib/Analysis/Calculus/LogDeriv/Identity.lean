/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Entire functions determined by a logarithmic derivative

Equality of logarithmic derivatives on one nonempty open connected region fixes
an entire function up to a constant. Normalization at zero fixes that constant.
-/

public section

open Filter Set Topology

/-- Two entire functions with equal logarithmic derivatives on a nonempty open
preconnected set, and nonzero values on that set, differ globally by a constant.
If the second function is one at zero, that constant is the first function's value at zero. -/
theorem Differentiable.eq_mul_of_logDeriv_eqOn {f g : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hg : Differentiable ℂ g) {s : Set ℂ}
    (hs : IsOpen s) (hconn : IsPreconnected s) (hne : s.Nonempty)
    (hfn : ∀ z ∈ s, f z ≠ 0) (hgn : ∀ z ∈ s, g z ≠ 0)
    (hlog : EqOn (_root_.logDeriv f) (_root_.logDeriv g) s) (hg0 : g 0 = 1) :
    ∀ z, f z = f 0 * g z := by
  obtain ⟨a, _, heq⟩ := (logDeriv_eqOn_iff hf.differentiableOn hg.differentiableOn
    hs hconn hgn hfn).mp hlog
  obtain ⟨w, hw⟩ := hne
  have hfa : AnalyticOnNhd ℂ f univ := fun z _ => hf.analyticAt z
  have hga : AnalyticOnNhd ℂ (fun z => a * g z) univ :=
    fun z _ => ((differentiable_const a).mul hg).analyticAt z
  have he : f = fun z => a * g z := by
    apply hfa.eq_of_eventuallyEq hga
    filter_upwards [hs.mem_nhds hw] with z hz
    simpa only [Pi.smul_apply, smul_eq_mul] using heq hz
  have ha : a = f 0 := by simpa only [hg0, mul_one] using (congrFun he 0).symm
  intro z
  simpa only [ha] using congrFun he z
