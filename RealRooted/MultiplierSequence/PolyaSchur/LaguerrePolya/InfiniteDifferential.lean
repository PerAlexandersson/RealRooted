module

public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya
public import RealRooted.Mathlib.Analysis.Complex.InfiniteDifferential.Basic
import RealRooted.Mathlib.Analysis.Complex.InfiniteDifferential.Derivative
import RealRooted.Mathlib.Analysis.Complex.InfiniteDifferential.Star
import RealRooted.Mathlib.Analysis.Complex.GrowthOrder.Derivative
import RealRooted.Mathlib.Analysis.Calculus.IteratedDeriv.Star
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.InfiniteDifferentialCoefficients
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Derivative
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Jensen

/-!
# Infinite differential preservation below order two

An LP differential symbol of order below two acts on every LP entire target
of order below two by a normally convergent series whose sum remains LP.
Convergence follows from the growth bounds; it is not an additional premise.
Zero symbols, targets and outputs are included.
-/

public section

open Complex Filter Topology

namespace RealRooted

/-- The actual infinite differential image of two LP entire inputs of order
below two is again LP, including the identically zero result. -/
theorem IsLaguerrePolya.infiniteDifferentialApply {φ f : ℂ → ℂ}
    (hφ : IsLaguerrePolya φ) (hf : IsLaguerrePolya f) {ρ σ : ℝ}
    (hoφ : TauCeti.OrderLE φ ρ) (hρ : ρ < 2) (hof : TauCeti.OrderLE f σ) (hσ : σ < 2) :
    IsLaguerrePolya (Complex.infiniteDifferentialApply φ f) := by
  have hc : ∀ k, Tendsto (fun N => ∑ n ∈ Finset.range N,
      (iteratedDeriv n φ 0).re * (iteratedDeriv (k + n) f 0).re / n.factorial) atTop
      (𝓝 ((iteratedDeriv k (Complex.infiniteDifferentialApply φ f) 0).re)) := by
    intro k
    have hdf := (hf.differentiable.contDiff (n := ⊤)).differentiable_iteratedDeriv k
      (WithTop.coe_lt_top _)
    have hs := (summable_norm_infiniteDifferentialApply hφ.differentiable hoφ hρ
      hdf (hof.iteratedDeriv hf.differentiable k) hσ 0).of_norm.hasSum
    have hre := Complex.hasSum_re hs
    have hreal (n : ℕ) : (iteratedDeriv n φ 0).im = 0 := by
      rw [← Complex.ofReal_re_iteratedDeriv_zero hφ.conj n]
      simp
    simp only [div_natCast_re, mul_re, hreal, zero_mul, sub_zero] at hre
    rw [iteratedDeriv_infiniteDifferentialApply hφ.differentiable hoφ hρ
      hf.differentiable hof hσ]
    simpa only [Complex.infiniteDifferentialApply,
      iteratedDeriv_eq_iterate, ← Function.iterate_add_apply, Nat.add_comm k] using
      hre.tendsto_sum_nat
  have hconj (z : ℂ) : Complex.infiniteDifferentialApply φ f (starRingEnd ℂ z) =
      starRingEnd ℂ (Complex.infiniteDifferentialApply φ f z) :=
    Complex.infiniteDifferentialApply_conj hφ.conj hf.conj z
  rw [eq_complexExpGeneratingFunction_of_iteratedDeriv
    (differentiable_infiniteDifferentialApply hφ.differentiable hoφ hρ hf.differentiable hof hσ)
    (fun k => (Complex.ofReal_re_iteratedDeriv_zero hconj k).symm)]
  exact hφ.infinite_differential_coefficients hf hc

end RealRooted
