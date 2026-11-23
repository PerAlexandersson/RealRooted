/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import RealRooted.Mathlib.NumberTheory.LSeries.RiemannXi.Theta
public import TauCeti.Analysis.CompletelyMonotone.Basic
import Mathlib.Analysis.Calculus.LogDeriv
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.LogDerivativeCompletelyMonotone
import RealRooted.RiemannHypothesis.TotalPositivity
import RealRooted.Mathlib.NumberTheory.LSeries.RiemannXi.Derivative

/-!
# Completely monotone xi logarithmic derivatives under RH

Under Mathlib's RH, the logarithmic derivative of every derivative of the
square-variable xi function is completely monotone on the positive real axis.
Every alternating real derivative of that logarithmic derivative is also
completely monotone. The unshifted case is the `k = 0` part of Zhang,
arXiv:1506.07012v13, equation (3.28); all derivative shifts follow from the
checked Type-I closure theorem.
-/

public section

open Complex

namespace RealRooted

/-- RH makes every shifted xi logarithmic derivative completely monotone
on the positive real axis. -/
theorem isCompletelyMonotoneOnIoi_xi_logDeriv
    (hRH : RiemannHypothesis) (s : ℕ) :
    TauCeti.IsCompletelyMonotoneOnIoi (fun x : ℝ ↦
      (logDeriv (iteratedDeriv s riemannXiTheta) (x : ℂ)).re) :=
  IsLaguerrePolyaTypeI.isCompletelyMonotoneOnIoi_logDeriv
    (isLaguerrePolyaTypeI_iteratedDeriv_riemannXiTheta hRH s)
    (iteratedDeriv_riemannXiTheta_zero_ne_zero s)

/-- RH makes every alternating real derivative of each shifted xi
logarithmic derivative completely monotone on the positive real axis. -/
theorem isCompletelyMonotoneOnIoi_xi_signed_logDeriv
    (hRH : RiemannHypothesis) (s m : ℕ) :
    TauCeti.IsCompletelyMonotoneOnIoi (fun x : ℝ ↦
      (-1 : ℝ) ^ m * iteratedDeriv m
        (fun y : ℝ ↦ (logDeriv (iteratedDeriv s riemannXiTheta) (y : ℂ)).re) x) :=
  IsLaguerrePolyaTypeI.isCompletelyMonotoneOnIoi_signed_logDeriv
    (isLaguerrePolyaTypeI_iteratedDeriv_riemannXiTheta hRH s)
    (iteratedDeriv_riemannXiTheta_zero_ne_zero s) m

end RealRooted
