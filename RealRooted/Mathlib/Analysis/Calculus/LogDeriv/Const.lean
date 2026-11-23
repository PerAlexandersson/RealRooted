/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import Mathlib.Analysis.Calculus.LogDeriv

/-!
# Constant division in logarithmic derivatives
-/

public section

variable {𝕜 𝕜' : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜']
  [NormedAlgebra 𝕜 𝕜']

/-- Dividing a function by a nonzero constant preserves its logarithmic
derivative, including totalized values at zeros and nondifferentiable points. -/
theorem logDeriv_div_const {f : 𝕜 → 𝕜'} (x : 𝕜) (a : 𝕜') (ha : a ≠ 0) :
    logDeriv (fun z => f z / a) x = logDeriv f x := by
  simpa only [div_eq_mul_inv] using logDeriv_mul_const (f := f) x a⁻¹ (inv_ne_zero ha)
