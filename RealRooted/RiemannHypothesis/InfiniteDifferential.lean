module

public import RealRooted.Mathlib.NumberTheory.LSeries.RiemannXi.Theta

import RealRooted.RiemannHypothesis
public import RealRooted.Mathlib.Analysis.Complex.InfiniteDifferential.Basic
public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.InfiniteDifferential
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.IteratedDerivative
import RealRooted.Mathlib.Analysis.Complex.GrowthOrder.Derivative

/-!
# RH-conditional infinite xi differential operators

Under Mathlib's RH, every derivative of the square-variable xi function acts
as a normally convergent differential symbol on LP targets of order below two.
Conversely it may serve as the target for any LP symbol of order below two.
Taking both inputs to be xi derivatives gives the shifted xi self-operator family.
-/

public section

open Complex

namespace RealRooted

/-- Under RH, a xi derivative is an infinite differential symbol preserving
LP membership of every target of order below two. -/
theorem isLaguerrePolya_riemannXiTheta_differential (hRH : RiemannHypothesis) (n : ℕ)
    {f : ℂ → ℂ} (hf : IsLaguerrePolya f) {ρ : ℝ}
    (horder : TauCeti.OrderLE f ρ) (hρ : ρ < 2) :
    IsLaguerrePolya (infiniteDifferentialApply (iteratedDeriv n riemannXiTheta) f) := by
  have hφ := (riemannHypothesis_iff_isLaguerrePolya_riemannXiTheta.mp hRH).iteratedDeriv n
  exact hφ.infiniteDifferentialApply hf
    (orderLE_half_riemannXiTheta.iteratedDeriv differentiable_riemannXiTheta n)
    (by norm_num) horder hρ

/-- Under RH, an LP differential symbol of order below two sends every xi
derivative to an LP entire function. -/
theorem isLaguerrePolya_differential_riemannXiTheta (hRH : RiemannHypothesis) (n : ℕ)
    {φ : ℂ → ℂ} (hφ : IsLaguerrePolya φ) {ρ : ℝ}
    (horder : TauCeti.OrderLE φ ρ) (hρ : ρ < 2) :
    IsLaguerrePolya (infiniteDifferentialApply φ (iteratedDeriv n riemannXiTheta)) := by
  exact hφ.infiniteDifferentialApply
    ((riemannHypothesis_iff_isLaguerrePolya_riemannXiTheta.mp hRH).iteratedDeriv n)
    horder hρ (orderLE_half_riemannXiTheta.iteratedDeriv differentiable_riemannXiTheta n)
    (by norm_num)

end RealRooted
