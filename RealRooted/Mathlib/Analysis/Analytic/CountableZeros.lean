/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Countability of analytic zero sets

The isolated-zero principle and the Lindelöf property show that the zeros of a
nonzero analytic function on a preconnected set are countable.
-/

public section

open Set

/-- The zeros of a function analytic on a preconnected set are countable unless
the function vanishes throughout that set. -/
theorem AnalyticOnNhd.countable_zeroSet {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [HereditarilyLindelofSpace 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {f : 𝕜 → E} {U : Set 𝕜} (hf : AnalyticOnNhd 𝕜 f U) (hU : IsPreconnected U)
    (hne : ¬ EqOn f 0 U) : {z ∈ U | f z = 0}.Countable := by
  have hz := (hf.eqOn_zero_or_eventually_ne_zero_of_preconnected hU).resolve_left hne
  have hd : IsDiscrete ({z | f z = 0} ∩ U) := isDiscrete_of_codiscreteWithin hz
  have hc := (HereditarilyLindelofSpace.isLindelof _).countable_of_isDiscrete hd
  simpa only [inter_def, mem_ofPred_eq, and_comm] using hc

/-- A nonzero entire complex function has a countable zero set. -/
theorem Differentiable.countable_zeroSet {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hne : f ≠ 0) : {z | f z = 0}.Countable := by
  have ha : AnalyticOnNhd ℂ f univ := fun z _ => hf.analyticAt z
  have hn : ¬ EqOn f 0 univ := fun h => hne (funext fun z => h (mem_univ z))
  simpa only [mem_univ, true_and] using ha.countable_zeroSet isPreconnected_univ hn

/-- The real zeros of a nonzero entire complex function form a countable set. -/
theorem Differentiable.countable_real_zeroSet {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hne : f ≠ 0) : {x : ℝ | f x = 0}.Countable :=
  (hf.countable_zeroSet hne).preimage Complex.ofReal_injective
