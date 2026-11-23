/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import RealRooted.Mathlib.NumberTheory.LSeries.RiemannXi.Theta
public import TauCeti.Analysis.CompletelyMonotone.Basic
import Mathlib.Analysis.Calculus.LogDeriv
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.LogDerivativeHierarchy
import RealRooted.RiemannHypothesis.TotalPositivity
import RealRooted.Mathlib.NumberTheory.LSeries.RiemannXi.Derivative

/-!
# The weighted xi logarithmic-derivative hierarchy under RH

Mathlib's RH implies the full two-index complete-monotonicity hierarchy for
the square-variable xi function and every one of its derivative shifts.
The unshifted case is Zhang, arXiv:1506.07012v13, equation (3.28).
The derivative-shift extension uses the checked Type-I derivative closure.
-/

public section

open Complex

namespace RealRooted

/-- Under RH, every weighted logarithmic derivative of every xi derivative
shift is completely monotone on the positive real axis. Both hierarchy
indices may be zero, and no simplicity assumption on xi zeros is required. -/
theorem isCompletelyMonotoneOnIoi_xi_weighted_logDeriv
    (hRH : RiemannHypothesis) (s k m : ℕ) :
    TauCeti.IsCompletelyMonotoneOnIoi (fun x : ℝ ↦
      (-1 / x) ^ m * iteratedDeriv k (fun y : ℝ ↦
        y ^ (k + m) * iteratedDeriv m (fun z : ℝ ↦
          (logDeriv (iteratedDeriv s riemannXiTheta) (z : ℂ)).re) y) x) :=
  IsLaguerrePolyaTypeI.isCompletelyMonotoneOnIoi_weighted_logDeriv
    (isLaguerrePolyaTypeI_iteratedDeriv_riemannXiTheta hRH s)
    (iteratedDeriv_riemannXiTheta_zero_ne_zero s) k m

end RealRooted
