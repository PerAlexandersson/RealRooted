module

public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya
public import RealRooted.Mathlib.Analysis.Complex.InfiniteDifferential.Basic
import RealRooted.Mathlib.Analysis.Complex.InfiniteDifferential.OrderDerivative
import RealRooted.Mathlib.Analysis.Complex.InfiniteDifferential.OrderConvergence
import RealRooted.Mathlib.Analysis.Complex.InfiniteDifferential.Star
import RealRooted.Mathlib.Analysis.Complex.GrowthOrder.Derivative
import RealRooted.Mathlib.Analysis.Calculus.IteratedDeriv.Star
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.InfiniteDifferentialCoefficients
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Derivative
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Jensen

/-!
# Infinite differential preservation under reciprocal order bounds

Positive exponents above the symbol and target growth orders suffice when
their reciprocals sum to more than one. The normally convergent differential
sum then remains LP. No separate coefficient convergence hypothesis is imposed,
and zero symbols, targets and outputs are included.
-/

public section

open Complex Filter Topology

namespace RealRooted

/-- The reciprocal growth-order condition gives LP preservation by the actual
infinite differential operator, including the identically zero result. -/
theorem IsLaguerrePolya.infiniteDifferentialApply_of_order {φ f : ℂ → ℂ}
    (hφ : IsLaguerrePolya φ) (hf : IsLaguerrePolya f) {ρ σ p q : ℝ}
    (hoφ : TauCeti.OrderLE φ ρ) (hp : 0 < p) (hρ : ρ < p)
    (hof : TauCeti.OrderLE f σ) (hq : 0 < q) (hσ : σ < q) (hsum : 1 < p⁻¹ + q⁻¹) :
    IsLaguerrePolya (Complex.infiniteDifferentialApply φ f) := by
  have hc : ∀ k, Tendsto (fun N => ∑ n ∈ Finset.range N,
      (iteratedDeriv n φ 0).re * (iteratedDeriv (k + n) f 0).re / n.factorial) atTop
      (𝓝 ((iteratedDeriv k (Complex.infiniteDifferentialApply φ f) 0).re)) := by
    intro k
    have hdf := (hf.differentiable.contDiff (n := ⊤)).differentiable_iteratedDeriv k
      (WithTop.coe_lt_top _)
    have hs := (summable_norm_infiniteDifferentialApply_of_order hφ.differentiable hoφ hp hρ
      hdf (hof.iteratedDeriv hf.differentiable k) hq hσ hsum 0).of_norm.hasSum
    have hre := Complex.hasSum_re hs
    have hreal (n : ℕ) : (iteratedDeriv n φ 0).im = 0 := by
      rw [← Complex.ofReal_re_iteratedDeriv_zero hφ.conj n]
      simp
    simp only [div_natCast_re, mul_re, hreal, zero_mul, sub_zero] at hre
    rw [iteratedDeriv_infiniteDifferentialApply_of_order hφ.differentiable hoφ hp hρ
      hf.differentiable hof hq hσ hsum]
    simpa only [Complex.infiniteDifferentialApply,
      iteratedDeriv_eq_iterate, ← Function.iterate_add_apply, Nat.add_comm k] using
      hre.tendsto_sum_nat
  have hconj (z : ℂ) : Complex.infiniteDifferentialApply φ f (starRingEnd ℂ z) =
      starRingEnd ℂ (Complex.infiniteDifferentialApply φ f z) :=
    Complex.infiniteDifferentialApply_conj hφ.conj hf.conj z
  rw [eq_complexExpGeneratingFunction_of_iteratedDeriv
    (differentiable_infiniteDifferentialApply_of_order hφ.differentiable hoφ hp hρ
      hf.differentiable hof hq hσ hsum)
    (fun k => (Complex.ofReal_re_iteratedDeriv_zero hconj k).symm)]
  exact hφ.infinite_differential_coefficients hf hc

end RealRooted
