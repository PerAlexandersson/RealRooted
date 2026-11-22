module

public import RealRooted.RiemannHypothesis
public import RealRooted.Mathlib.Analysis.Complex.HeatOperator.Basic
public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.HeatOperatorSimple
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Jensen
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Derivative
import RealRooted.Mathlib.Analysis.Complex.GrowthOrder.Derivative
import RealRooted.Mathlib.NumberTheory.LSeries.RiemannXi.Derivative

/-!
# RH-conditional simple zeros of entire xi heat images

Under Mathlib's RH, every derivative of the normalized square-variable xi
function has a nonzero LP backward heat image with only simple real zeros at
every positive time. This does not assert simplicity of the time-zero xi zeros.
-/

public section

open Complex

namespace RealRooted

/-- RH gives simple real zeros for every positive-time entire heat image of
every derivative of the normalized square-variable xi function. -/
theorem heatOperator_riemannXiTheta_simple_zeros (hRH : RiemannHypothesis) (n : ℕ)
    {t : ℝ} (ht : 0 < t) :
    IsLaguerrePolya (heatOperator (t : ℂ) (iteratedDeriv n riemannXiTheta)) ∧
      heatOperator (t : ℂ) (iteratedDeriv n riemannXiTheta) ≠ 0 ∧
      ∀ z, heatOperator (t : ℂ) (iteratedDeriv n riemannXiTheta) z = 0 →
        z.im = 0 ∧ _root_.deriv (heatOperator (t : ℂ) (iteratedDeriv n riemannXiTheta)) z ≠ 0 := by
  have hf := (riemannHypothesis_iff_isLaguerrePolya_riemannXiTheta.mp hRH).iterate_deriv n
  apply hf.heatOperator_simple_zeros
    (orderLE_half_riemannXiTheta.iteratedDeriv differentiable_riemannXiTheta n) (by norm_num)
    _ ht
  intro hz
  exact iteratedDeriv_riemannXiTheta_zero_ne_zero n (congrFun hz 0)

end RealRooted
