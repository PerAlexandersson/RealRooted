/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.ChangeOrigin
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Real iterated derivatives of locally holomorphic functions

The real part of a holomorphic function restricted to the real axis has
iterated derivatives given by the real parts of the complex derivatives.
The local hypothesis applies at endpoints of subsequently restricted domains.
-/

public section

open Filter Topology

/-- Taking real parts and restricting to the real axis commutes with every
iterated derivative of a function holomorphic near the point. -/
theorem AnalyticAt.iteratedDeriv_real_of_complex {f : ℂ → ℂ} {x : ℝ}
    (hf : AnalyticAt ℂ f (x : ℂ)) (k : ℕ) :
    iteratedDeriv k (fun y : ℝ ↦ (f (y : ℂ)).re) x =
      (iteratedDeriv k f (x : ℂ)).re := by
  induction k generalizing f with
  | zero => rfl
  | succ k ih =>
      have heq : deriv (fun y : ℝ ↦ (f (y : ℂ)).re) =ᶠ[𝓝 x]
          (fun y : ℝ ↦ (deriv f (y : ℂ)).re) := by
        filter_upwards [Complex.continuous_ofReal.continuousAt.tendsto.eventually
          hf.eventually_analyticAt] with y hy
        exact hy.differentiableAt.hasDerivAt.real_of_complex.deriv
      rw [iteratedDeriv_succ', heq.iteratedDeriv_eq k, ih hf.deriv, iteratedDeriv_succ']
