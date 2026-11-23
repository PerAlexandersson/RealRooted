module

public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya
public import RealRooted.Mathlib.Analysis.Complex.InfiniteDifferential.Basic
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.InfiniteDifferentialGaussian
import RealRooted.Mathlib.Analysis.Complex.InfiniteDifferential.GaussianMargin

/-!
# Infinite differential preservation from Gaussian type

The coefficients may vanish. Strictly larger positive norm-bound coefficients
are selected within the open region `4*a*b<1`, then the sharp convergence
theorem applies to the actual differential sum.
-/

public section

namespace RealRooted

/-- The Gaussian-type product condition gives LP preservation of the actual
infinite differential series. Type is expressed by arbitrarily sharp global
norm bounds, rather than an order-only bound that would lose the constants. -/
theorem IsLaguerrePolya.infiniteDifferentialApply_of_gaussian_type {φ f : ℂ → ℂ}
    (hφ : IsLaguerrePolya φ) (hf : IsLaguerrePolya f) {α β : ℝ}
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hab : 4 * α * β < 1)
    (hφbound : ∀ ε > 0, ∃ C > 0, ∀ z,
      ‖φ z‖ ≤ C * Real.exp ((α + ε) * ‖z‖ ^ 2))
    (hfbound : ∀ ε > 0, ∃ C > 0, ∀ z,
      ‖f z‖ ≤ C * Real.exp ((β + ε) * ‖z‖ ^ 2)) :
    IsLaguerrePolya (Complex.infiniteDifferentialApply φ f) := by
  obtain ⟨a, b, hαa, hβb, ha, hb, hab'⟩ := Real.exists_pos_gaussian_coefficients hα hβ hab
  obtain ⟨A, hA, hAbound⟩ := hφbound (a - α) (sub_pos.mpr hαa)
  obtain ⟨B, hB, hBbound⟩ := hfbound (b - β) (sub_pos.mpr hβb)
  apply hφ.infiniteDifferentialApply_of_gaussian hf hA.le hB.le ha hb hab'
  · have heq : α + (a - α) = a := by linarith
    simpa only [heq] using hAbound
  · have heq : β + (b - β) = b := by linarith
    simpa only [heq] using hBbound

end RealRooted
