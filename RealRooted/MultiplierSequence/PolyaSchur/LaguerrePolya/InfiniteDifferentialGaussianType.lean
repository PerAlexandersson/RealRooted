module

public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya
public import RealRooted.Mathlib.Analysis.Complex.InfiniteDifferential.Basic
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.InfiniteDifferentialGaussian

/-!
# Infinite differential preservation from Gaussian type

The coefficients may vanish. Strictly larger positive norm-bound coefficients
are selected within the open region `4*a*b<1`, then the sharp convergence
theorem applies to the actual differential sum.
-/

public section

namespace RealRooted

/-- The strict product condition survives a small simultaneous increase,
including when one or both original coefficients vanish. -/
private theorem exists_pos_gaussian_coefficients {α β : ℝ}
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hab : 4 * α * β < 1) :
    ∃ a b : ℝ, α < a ∧ β < b ∧ 0 < a ∧ 0 < b ∧ 4 * a * b < 1 := by
  have hopen : IsOpen {t : ℝ | 4 * (α + t) * (β + t) < 1} :=
    isOpen_lt (by fun_prop) continuous_const
  have hzero : (0 : ℝ) ∈ {t : ℝ | 4 * (α + t) * (β + t) < 1} := by
    simpa only [Set.mem_ofPred_eq, add_zero] using hab
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds hzero)
  have hh : r / 2 ∈ Metric.ball (0 : ℝ) r := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (half_pos hr)]
    linarith
  exact ⟨α + r / 2, β + r / 2, by linarith, by linarith,
    by linarith, by linarith, hball hh⟩

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
  obtain ⟨a, b, hαa, hβb, ha, hb, hab'⟩ := exists_pos_gaussian_coefficients hα hβ hab
  obtain ⟨A, hA, hAbound⟩ := hφbound (a - α) (sub_pos.mpr hαa)
  obtain ⟨B, hB, hBbound⟩ := hfbound (b - β) (sub_pos.mpr hβb)
  apply hφ.infiniteDifferentialApply_of_gaussian hf hA.le hB.le ha hb hab'
  · have heq : α + (a - α) = a := by linarith
    simpa only [heq] using hAbound
  · have heq : β + (b - β) = b := by linarith
    simpa only [heq] using hBbound

end RealRooted
