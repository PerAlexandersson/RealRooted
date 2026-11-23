module

public import RealRooted.Mathlib.NumberTheory.LSeries.RiemannXi.Theta
public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya
public import RealRooted.Mathlib.Analysis.Complex.InfiniteDifferential.Basic
import RealRooted.RiemannHypothesis.TotalPositivity
import RealRooted.RiemannHypothesis.JensenSimple
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.TypeIDifferentialSimple
import RealRooted.Mathlib.Analysis.Complex.GrowthOrder.Derivative

/-!
# Simple infinite differential images under RH

Under Mathlib's RH, every derivative of the square-variable xi function is
a nonpolynomial Type-I symbol of order at most one half, nonzero at zero.
Acting on any LP entire target therefore gives zero or a function with only
simple real zeros. This concerns differential images, not xi's own zeros.
-/

public section

open Complex

namespace RealRooted

/-- Under RH, every derivative of the normalized xi symbol has simple
nonzero differential images on arbitrary LP entire targets. -/
theorem deriv_xi_differential_ne_zero (hRH : RiemannHypothesis) (n : ℕ)
    {f : ℂ → ℂ} (hf : IsLaguerrePolya f)
    (hne : infiniteDifferentialApply (iteratedDeriv n riemannXiTheta) f ≠ 0)
    {z : ℂ} (hz : infiniteDifferentialApply (iteratedDeriv n riemannXiTheta) f z = 0) :
    _root_.deriv (infiniteDifferentialApply (iteratedDeriv n riemannXiTheta) f) z ≠ 0 := by
  exact IsLaguerrePolyaTypeI.deriv_differential_ne_zero_of_order_lt_one
      (isLaguerrePolyaTypeI_iteratedDeriv_riemannXiTheta hRH n) hf
      (orderLE_half_riemannXiTheta.iteratedDeriv differentiable_riemannXiTheta n)
      (by norm_num) (iteratedDeriv_riemannXiTheta_ne_polynomial n) hne hz

/-- Under RH, all shifted xi differential operators send any LP entire target
to zero or to an LP entire function with only simple real zeros. -/
theorem xi_differential_simple_or_zero (hRH : RiemannHypothesis) (n : ℕ)
    {f : ℂ → ℂ} (hf : IsLaguerrePolya f) :
    infiniteDifferentialApply (iteratedDeriv n riemannXiTheta) f = 0 ∨
      IsLaguerrePolya (infiniteDifferentialApply (iteratedDeriv n riemannXiTheta) f) ∧
      ∀ z, infiniteDifferentialApply (iteratedDeriv n riemannXiTheta) f z = 0 →
        z.im = 0 ∧
          _root_.deriv (infiniteDifferentialApply (iteratedDeriv n riemannXiTheta) f) z ≠ 0 := by
  exact IsLaguerrePolyaTypeI.differential_simple_or_zero_of_order_lt_one
      (isLaguerrePolyaTypeI_iteratedDeriv_riemannXiTheta hRH n) hf
      (orderLE_half_riemannXiTheta.iteratedDeriv differentiable_riemannXiTheta n)
      (by norm_num) (iteratedDeriv_riemannXiTheta_ne_polynomial n)

end RealRooted
