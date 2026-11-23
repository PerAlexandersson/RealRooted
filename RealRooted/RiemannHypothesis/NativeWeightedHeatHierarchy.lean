/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import RealRooted.Mathlib.NumberTheory.LSeries.RiemannXi.Theta
public import RealRooted.Mathlib.Analysis.Complex.ZeroHeatTrace
public import RealRooted.Mathlib.RingTheory.Polynomial.Laguerre.Basic
import Mathlib.Analysis.Calculus.LogDeriv
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.NativeWeightedHeatHierarchy
import RealRooted.RiemannHypothesis.TotalPositivity
import RealRooted.Mathlib.NumberTheory.LSeries.RiemannXi.Derivative

/-!
# Native weighted heat and Laguerre identities for xi under RH

Classical RH supplies Type-I membership for every fixed derivative of the
square-variable xi function. Its unconditional order-one-half bound removes
the exponential factor. Both integral representations use the actual native
zero multiplicities and the same logarithmic-derivative expression.
-/

public section

open Complex MeasureTheory Set

namespace RealRooted

/-- Under classical RH, every shifted xi hierarchy has its positive
weighted-heat and Laguerre integral representations, with actual integrability. -/
theorem native_weighted_heatTrace_xi_logDeriv (hRH : RiemannHypothesis)
    (s k m : ℕ) {x : ℝ} (hx : 0 < x) :
    (IntegrableOn (fun t : ℝ ↦ Real.exp (-x * t) * t ^ m * (-t) ^ k *
        iteratedDeriv k (Complex.zeroHeatTrace (iteratedDeriv s riemannXiTheta)) t) (Ioi 0) ∧
      (-1 / x) ^ m * iteratedDeriv k (fun y : ℝ ↦ y ^ (k + m) *
        iteratedDeriv m (fun z : ℝ ↦
          (logDeriv (iteratedDeriv s riemannXiTheta) (z : ℂ)).re) y) x =
            ∫ t : ℝ in Ioi 0, Real.exp (-x * t) * t ^ m * (-t) ^ k *
              iteratedDeriv k (Complex.zeroHeatTrace (iteratedDeriv s riemannXiTheta)) t) ∧
    (IntegrableOn (fun t : ℝ ↦ Real.exp (-x * t) * t ^ m *
        Complex.zeroHeatTrace (iteratedDeriv s riemannXiTheta) t *
          (Polynomial.generalizedLaguerre k (m : ℝ)).eval (-x * t)) (Ioi 0) ∧
      (-1 / x) ^ m * iteratedDeriv k (fun y : ℝ ↦ y ^ (k + m) *
        iteratedDeriv m (fun z : ℝ ↦
          (logDeriv (iteratedDeriv s riemannXiTheta) (z : ℂ)).re) y) x =
            ∫ t : ℝ in Ioi 0, Real.exp (-x * t) * t ^ m *
              Complex.zeroHeatTrace (iteratedDeriv s riemannXiTheta) t *
                (Polynomial.generalizedLaguerre k (m : ℝ)).eval (-x * t)) :=
  (isLaguerrePolyaTypeI_iteratedDeriv_riemannXiTheta hRH s).native_weighted_heatTrace_logDeriv
    (iteratedDeriv_riemannXiTheta_zero_ne_zero s)
    (orderLE_half_iteratedDeriv_riemannXiTheta s) (by norm_num) k m hx

end RealRooted
