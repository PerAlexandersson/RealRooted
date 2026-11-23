/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import RealRooted.Mathlib.NumberTheory.LSeries.RiemannXi.Theta
public import RealRooted.Mathlib.Analysis.SpecialFunctions.Exp.PositiveSlopeHeatTrace
import Mathlib.Analysis.Calculus.LogDeriv
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.LogDerivativePureHeatTrace
import RealRooted.RiemannHypothesis.TotalPositivity
import RealRooted.Mathlib.NumberTheory.LSeries.RiemannXi.Derivative
import RealRooted.Mathlib.Analysis.Complex.GrowthOrder.Derivative

/-!
# Pure xi zero heat traces under RH

The checked order-one-half bound removes the exponential factor in every
xi derivative's Type-I factorization. Thus its signed logarithmic derivatives
are pure heat-trace Laplace moments at all nonnegative arguments.
-/

public section

open Complex MeasureTheory

namespace RealRooted

/-- RH and the unconditional order-one-half estimate give a pure positive
zero heat trace for every xi derivative shift, with no constant correction. -/
theorem exists_pure_heatTrace_xi_logDeriv (hRH : RiemannHypothesis) (s : ℕ) :
    ∃ a : ℕ → ℝ, (∀ i, 0 ≤ a i) ∧ Summable a ∧
      iteratedDeriv s riemannXiTheta =
        (fun z : ℂ ↦ iteratedDeriv s riemannXiTheta 0 *
          ∏' i, (1 + (a i : ℂ) * z)) ∧
      TauCeti.IsCompletelyMonotoneOnIoi (Real.positiveSlopeHeatTrace a) ∧
      ∀ (k : ℕ) (x : ℝ), 0 ≤ x →
        IntegrableOn (fun t : ℝ ↦ Real.exp (-x * t) * t ^ k *
          Real.positiveSlopeHeatTrace a t) (Set.Ioi 0) ∧
        (-1 : ℝ) ^ k * iteratedDeriv k (fun y : ℝ ↦
          (logDeriv (iteratedDeriv s riemannXiTheta) (y : ℂ)).re) x =
          ∫ t : ℝ in Set.Ioi 0,
            Real.exp (-x * t) * t ^ k * Real.positiveSlopeHeatTrace a t :=
  (isLaguerrePolyaTypeI_iteratedDeriv_riemannXiTheta hRH s).exists_pure_heatTrace_logDeriv
    (iteratedDeriv_riemannXiTheta_zero_ne_zero s)
      (orderLE_half_riemannXiTheta.iteratedDeriv differentiable_riemannXiTheta s)
      (by norm_num)

end RealRooted
