/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Real logarithms and complex logarithmic derivatives

On a nonvanishing real restriction of a complex differentiable function,
the derivative of the real logarithm is the real complex logarithmic
derivative. The iterated and weighted identities are local to the positive
axis and require no square-root differentiation at its boundary.
For negative real values, `Real.log` has its usual log-absolute-value meaning.
-/

public section

open Filter Topology

namespace Complex

/-- The real logarithm of a real nonzero complex restriction has the
expected logarithmic derivative. -/
theorem hasDerivAt_log_re {f : ℂ → ℂ} {x : ℝ}
    (hf : DifferentiableAt ℂ f (x : ℂ))
    (hreal : ((f (x : ℂ)).re : ℂ) = f (x : ℂ)) (hne : f (x : ℂ) ≠ 0) :
    HasDerivAt (fun y : ℝ ↦ Real.log (f (y : ℂ)).re) (logDeriv f (x : ℂ)).re x := by
  have hre : (f (x : ℂ)).re ≠ 0 := by
    intro h
    apply hne
    rw [← hreal, h, ofReal_zero]
  convert hf.hasDerivAt.real_of_complex.log hre using 1
  change (deriv f (x : ℂ) / f (x : ℂ)).re =
    (deriv f (x : ℂ)).re / (f (x : ℂ)).re
  exact (congrArg (fun w : ℂ ↦ (deriv f (x : ℂ) / w).re) hreal.symm).trans
    (div_ofReal_re _ _)

/-- Each positive-axis derivative of the literal real logarithm is the
corresponding derivative of the actual logarithmic derivative. -/
theorem iteratedDeriv_log_re_eq {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hreal : ∀ x : ℝ, 0 < x → ((f (x : ℂ)).re : ℂ) = f (x : ℂ))
    (hne : ∀ x : ℝ, 0 < x → f (x : ℂ) ≠ 0) (m : ℕ) {x : ℝ} (hx : 0 < x) :
    iteratedDeriv (m + 1) (fun y : ℝ ↦ Real.log (f (y : ℂ)).re) x =
      iteratedDeriv m (fun y : ℝ ↦ (logDeriv f (y : ℂ)).re) x := by
  have heq : deriv (fun y : ℝ ↦ Real.log (f (y : ℂ)).re) =ᶠ[𝓝 x]
      (fun y : ℝ ↦ (logDeriv f (y : ℂ)).re) := by
    filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
    exact (hasDerivAt_log_re (hf _) (hreal y hy) (hne y hy)).deriv
  rw [iteratedDeriv_succ', heq.iteratedDeriv_eq m]

/-- The literal real-logarithm and logarithmic-derivative versions of the
two-index weighted family agree at every positive argument. -/
theorem weighted_iteratedDeriv_log_re_eq {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hreal : ∀ x : ℝ, 0 < x → ((f (x : ℂ)).re : ℂ) = f (x : ℂ))
    (hne : ∀ x : ℝ, 0 < x → f (x : ℂ) ≠ 0) (k m : ℕ) {x : ℝ} (hx : 0 < x) :
    (-1 / x) ^ m * iteratedDeriv k (fun y : ℝ ↦ y ^ (k + m) *
      iteratedDeriv (m + 1) (fun z : ℝ ↦ Real.log (f (z : ℂ)).re) y) x =
      (-1 / x) ^ m * iteratedDeriv k (fun y : ℝ ↦ y ^ (k + m) *
        iteratedDeriv m (fun z : ℝ ↦ (logDeriv f (z : ℂ)).re) y) x := by
  have heq : (fun y : ℝ ↦ y ^ (k + m) *
      iteratedDeriv (m + 1) (fun z : ℝ ↦ Real.log (f (z : ℂ)).re) y) =ᶠ[𝓝 x]
      (fun y : ℝ ↦ y ^ (k + m) *
        iteratedDeriv m (fun z : ℝ ↦ (logDeriv f (z : ℂ)).re) y) := by
    filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
    rw [iteratedDeriv_log_re_eq hf hreal hne m hy]
  rw [heq.iteratedDeriv_eq k]

end Complex
