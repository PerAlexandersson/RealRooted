module

public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya
public import RealRooted.Mathlib.Analysis.Complex.InfiniteDifferential.Basic
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.CanonicalRepresentation
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.GeneralizedInequality
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.CanonicalMultiplicitySimple
import RealRooted.LaguerreInequalities.InverseSquare
import RealRooted.Mathlib.Analysis.Complex.CanonicalProduct.GaussianCoefficient
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Derivative

/-!
# Infinite-zero differential simplicity from the native LP predicates

The canonical representation and its Gaussian coefficient are derived from
the closure definition of LP. No canonical equality is supplied by the caller.
The output is the actual infinite differential series, including its zero case.
-/

public section

open Complex

namespace RealRooted

/-- Native LP symbols with infinitely many real zeros have zero or simple LP
output at the strict Gaussian product threshold. Both sharp Gaussian bounds
are analytic hypotheses; no product representation or simplicity is assumed. -/
theorem IsLaguerrePolya.differential_simple_or_zero_of_gaussian_bounds
    {φ f : ℂ → ℂ} (hφ : IsLaguerrePolya φ) (hf : IsLaguerrePolya f)
    {α β : ℝ} (hβ : 0 ≤ β) (hab : 4 * α * β < 1)
    (hφbound : ∀ ε > 0, ∃ C > 0, ∀ z,
      ‖φ z‖ ≤ C * Real.exp ((α + ε) * ‖z‖ ^ 2))
    (hfbound : ∀ ε > 0, ∃ C > 0, ∀ z,
      ‖f z‖ ≤ C * Real.exp ((β + ε) * ‖z‖ ^ 2))
    (hinf : Set.Infinite {x : ℝ | φ x = 0}) :
    infiniteDifferentialApply φ f = 0 ∨
      IsLaguerrePolya (infiniteDifferentialApply φ f) ∧
      ∀ z, infiniteDifferentialApply φ f z = 0 →
        z.im = 0 ∧ _root_.deriv (infiniteDifferentialApply φ f) z ≠ 0 := by
  by_cases hzero : φ = 0
  · left
    ext z
    simp only [hzero, infiniteDifferentialApply, iteratedDeriv_const_zero,
      zero_mul, zero_div, tsum_zero, Pi.zero_apply]
  · obtain ⟨g, hg, hg0, c, b, A, hc, hA, heq⟩ :=
      hφ.exists_eq_pow_mul_exp_mul_realZeroProduct hzero
    let a : {x : ℝ | g x = 0} → ℝ := fun r ↦ (r : ℝ)⁻¹
    let m : {x : ℝ | g x = 0} → ℕ := fun r ↦ analyticOrderNatAt g (r : ℂ)
    have hm : Summable (fun r ↦ (m r : ℝ) * a r ^ 2) := by
      simpa only [m, a, inv_pow, div_eq_mul_inv] using
        summable_analyticOrderNatAt_div_sq hg.differentiable hg.conj hg0
          hg.laguerreCoefficient_nonneg
    have hcanonical (z : ℂ) : φ z = (c : ℂ) * z ^ analyticOrderNatAt φ 0 *
        exp (-(A : ℂ) * z ^ 2 + (b : ℂ) * z) *
          ∏' r, weierstrassFactor 1 ((a r : ℂ) * z) ^ m r := by
      simpa only [realZeroProduct, a, m, ofReal_inv] using heq z
    have hAle := gaussian_le_of_canonical_norm_bound a m hm hc b A
      (analyticOrderNatAt φ 0) hcanonical hφbound
    have hprod : 4 * A * β < 1 :=
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hAle (by norm_num)) hβ).trans_lt hab
    exact hf.canonical_multiplicity_differential_simple_or_zero a m hm c b
      (analyticOrderNatAt φ 0) hA hβ hprod hcanonical hinf hfbound

end RealRooted
