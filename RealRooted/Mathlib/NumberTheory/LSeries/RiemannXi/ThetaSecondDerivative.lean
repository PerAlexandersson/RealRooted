/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import RealRooted.Mathlib.NumberTheory.LSeries.RiemannXi.Kernel
import RealRooted.Mathlib.Analysis.SpecialFunctions.Gaussian.ParameterDerivative

/-!
# The actual second derivative of the theta kernel
-/

public section

open Real

/-- The second derivative series of the theta kernel on the positive half-line. -/
@[expose] noncomputable def riemannThetaKernelSecondDeriv (t : ℝ) : ℝ :=
  2 * π ^ 2 * ∑' n : ℕ, (n + 1 : ℝ) ^ 4 * exp (-π * (n + 1 : ℝ) ^ 2 * t)

/-- The actual derivative of the first theta-kernel derivative equals its series. -/
theorem hasDerivAt_riemannThetaKernelDeriv {t : ℝ} (ht : 0 < t) :
    HasDerivAt riemannThetaKernelDeriv (riemannThetaKernelSecondDeriv t) t := by
  have h := (hasDerivAt_tsum_pow_mul_exp_neg_sq_parameter 2 pi_pos ht).const_mul (-2 * π)
  convert h using 1
  · funext y
    rw [riemannThetaKernelDeriv, ← tsum_mul_left]
    exact tsum_congr fun n => by ring
  · simp only [riemannThetaKernelSecondDeriv]
    ring
