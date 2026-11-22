module

public import RealRooted.RiemannHypothesis
public import RealRooted.Mathlib.Analysis.Complex.InfiniteDifferential.Basic
public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.InfiniteDifferentialEntire
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.IteratedDerivative
import RealRooted.Mathlib.Analysis.Complex.GrowthOrder.Derivative

/-!
# RH-conditional xi operators on the full LP class

Under Mathlib's RH, every xi derivative is a convergent infinite differential
symbol preserving the entire LP class. Every LP symbol likewise acts on every
xi derivative with an LP entire result. Neither application needs a supplied
growth bound on the other LP input.
-/

public section

open Complex

namespace RealRooted

/-- Under RH, every xi derivative acts as a convergent differential symbol
on every LP entire target, without an additional target growth hypothesis. -/
theorem IsLaguerrePolya.riemannXiTheta_differential {f : ℂ → ℂ}
    (hf : IsLaguerrePolya f) (hRH : RiemannHypothesis) (n : ℕ) :
    IsLaguerrePolya (infiniteDifferentialApply (iteratedDeriv n riemannXiTheta) f) := by
  have hφ := (riemannHypothesis_iff_isLaguerrePolya_riemannXiTheta.mp hRH).iteratedDeriv n
  exact hφ.infiniteDifferentialApply_of_left_order hf
    (orderLE_half_riemannXiTheta.iteratedDeriv differentiable_riemannXiTheta n) (by norm_num)

/-- Under RH, every LP symbol acts on every xi derivative by a convergent
infinite differential series whose entire sum is LP. -/
theorem IsLaguerrePolya.differential_riemannXiTheta {φ : ℂ → ℂ}
    (hφ : IsLaguerrePolya φ) (hRH : RiemannHypothesis) (n : ℕ) :
    IsLaguerrePolya (infiniteDifferentialApply φ (iteratedDeriv n riemannXiTheta)) := by
  have hf := (riemannHypothesis_iff_isLaguerrePolya_riemannXiTheta.mp hRH).iteratedDeriv n
  exact hφ.infiniteDifferentialApply_of_right_order hf
    (orderLE_half_riemannXiTheta.iteratedDeriv differentiable_riemannXiTheta n) (by norm_num)

end RealRooted
