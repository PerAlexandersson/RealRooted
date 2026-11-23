module

public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya
public import RealRooted.Mathlib.Analysis.Complex.InfiniteDifferential.Basic
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.InfiniteDifferentialSummable
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Derivative
import RealRooted.Mathlib.Analysis.Complex.InfiniteDifferential.GaussianConvergence

/-!
# Laguerre--Pólya preservation under sharp Gaussian norm bounds

The actual differential series converges and remains LP when the product
of two positive Gaussian norm-bound coefficients is below one quarter.
This is the quantitative convergence input to the general Gaussian-type
theorem; extracting arbitrarily sharp bounds from a canonical factorization
is a separate obligation.
-/

public section

namespace RealRooted

/-- Explicit Gaussian norm bounds with product below one quarter give LP
preservation by the actual infinite differential series, including zero output. -/
theorem IsLaguerrePolya.infiniteDifferentialApply_of_gaussian {φ f : ℂ → ℂ}
    (hφ : IsLaguerrePolya φ) (hf : IsLaguerrePolya f)
    {Mφ Mf a b : ℝ} (hMφ : 0 ≤ Mφ) (hMf : 0 ≤ Mf) (ha : 0 < a) (hb : 0 < b)
    (hab : 4 * a * b < 1)
    (hφbound : ∀ w, ‖φ w‖ ≤ Mφ * Real.exp (a * ‖w‖ ^ 2))
    (hfbound : ∀ w, ‖f w‖ ≤ Mf * Real.exp (b * ‖w‖ ^ 2)) :
    IsLaguerrePolya (Complex.infiniteDifferentialApply φ f) :=
  hφ.infiniteDifferentialApply_of_summable hf (fun z =>
    (Complex.summable_norm_infiniteDifferentialApply_of_gaussian
      hφ.differentiable hf.differentiable hMφ hMf ha hb hab hφbound hfbound z).of_norm)

end RealRooted
