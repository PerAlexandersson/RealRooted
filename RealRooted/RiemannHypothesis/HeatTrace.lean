/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import RealRooted.Mathlib.NumberTheory.LSeries.RiemannXi.Theta
import RealRooted.RiemannHypothesis.TotalPositivity
public import RealRooted.Mathlib.Analysis.SpecialFunctions.Exp.PositiveSlopeHeatTrace
import Mathlib.Analysis.Calculus.LogDeriv
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.LogDerivativeHeatTrace
import RealRooted.Mathlib.NumberTheory.LSeries.RiemannXi.Derivative

/-!
# Heat traces for the square-variable xi function under RH

Every derivative shift has a positive-zero heat trace under RH. Its Laplace
moments give all signed real logarithmic derivatives, including at zero.
The statement keeps the possible Type-I exponential constant explicit;
eliminating it using the sharper growth order is a separate strengthening.
-/

public section

open Complex MeasureTheory

namespace RealRooted

/-- Under RH, every xi derivative shift admits a completely monotone heat
trace from its positive zero rates, with all logarithmic derivatives given
by its Laplace moments and the explicit Type-I exponential constant. -/
theorem exists_heatTrace_xi_logDeriv (hRH : RiemannHypothesis) (s : ℕ) :
    ∃ (gamma : ℝ) (a : ℕ → ℝ),
      0 ≤ gamma ∧ (∀ i, 0 ≤ a i) ∧ Summable a ∧
      iteratedDeriv s riemannXiTheta =
        (fun z : ℂ ↦ iteratedDeriv s riemannXiTheta 0 * exp ((gamma : ℂ) * z) *
          ∏' i, (1 + (a i : ℂ) * z)) ∧
      TauCeti.IsCompletelyMonotoneOnIoi (Real.positiveSlopeHeatTrace a) ∧
      ∀ (k : ℕ) (x : ℝ), 0 ≤ x →
        IntegrableOn (fun t : ℝ ↦ Real.exp (-x * t) * t ^ k *
          Real.positiveSlopeHeatTrace a t) (Set.Ioi 0) ∧
        (-1 : ℝ) ^ k * iteratedDeriv k (fun y : ℝ ↦
          (logDeriv (iteratedDeriv s riemannXiTheta) (y : ℂ)).re) x =
          gamma * 0 ^ k + ∫ t : ℝ in Set.Ioi 0,
            Real.exp (-x * t) * t ^ k * Real.positiveSlopeHeatTrace a t :=
  (isLaguerrePolyaTypeI_iteratedDeriv_riemannXiTheta hRH s).exists_heatTrace_logDeriv
    (iteratedDeriv_riemannXiTheta_zero_ne_zero s)

end RealRooted
