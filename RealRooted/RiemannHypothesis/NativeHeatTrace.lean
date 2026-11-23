/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import RealRooted.Mathlib.NumberTheory.LSeries.RiemannXi.Theta
public import RealRooted.Mathlib.Analysis.Complex.ZeroHeatTrace
import Mathlib.Analysis.Calculus.LogDeriv
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.NativeHeatTrace
import RealRooted.RiemannHypothesis.TotalPositivity
import RealRooted.Mathlib.NumberTheory.LSeries.RiemannXi.Derivative
import RealRooted.Mathlib.Analysis.Complex.GrowthOrder.Derivative

/-!
# Native xi zero heat traces under RH

All statements use the actual native divisor, including multiplicities,
and explicit classical RH. The unconditional order-one-half estimate supplies the pure product used
in the Laplace identity. Analytic multiplicities are retained without
choosing an enumeration of zeros.
-/

public section

open Complex Filter MeasureTheory Topology

namespace RealRooted

/-- Under RH, native xi zero heat traces are completely monotone and their
Laplace moments equal all signed logarithmic derivatives at `x ≥ 0`. -/
theorem native_heatTrace_xi_logDeriv (hRH : RiemannHypothesis) (s : ℕ) :
    TauCeti.IsCompletelyMonotoneOnIoi (Complex.zeroHeatTrace (iteratedDeriv s riemannXiTheta)) ∧
      ∀ (k : ℕ) (x : ℝ), 0 ≤ x →
        IntegrableOn (fun t : ℝ ↦ Real.exp (-x * t) * t ^ k *
          Complex.zeroHeatTrace (iteratedDeriv s riemannXiTheta) t) (Set.Ioi 0) ∧
        (-1 : ℝ) ^ k * iteratedDeriv k (fun y : ℝ ↦
          (logDeriv (iteratedDeriv s riemannXiTheta) (y : ℂ)).re) x =
          ∫ t : ℝ in Set.Ioi 0, Real.exp (-x * t) * t ^ k *
            Complex.zeroHeatTrace (iteratedDeriv s riemannXiTheta) t :=
  (isLaguerrePolyaTypeI_iteratedDeriv_riemannXiTheta hRH s).native_heatTrace_logDeriv
    (iteratedDeriv_riemannXiTheta_zero_ne_zero s)
      (orderLE_half_riemannXiTheta.iteratedDeriv differentiable_riemannXiTheta s)
      (by norm_num)

end RealRooted
