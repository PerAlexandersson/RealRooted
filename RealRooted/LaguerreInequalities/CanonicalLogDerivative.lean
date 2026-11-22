module

public import RealRooted.LaguerreInequalities.CanonicalProduct
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import RealRooted.LaguerreInequalities.AtomMultiplicity
import RealRooted.LaguerreInequalities.AtomicRepresentation
import RealRooted.LaguerreInequalities.MeasureSupport
import RealRooted.LaguerreInequalities.InverseSquare
import TauCeti.Analysis.Complex.CanonicalProduct.LogDeriv

/-!
# Reconstructing the logarithmic derivative from real zeros

The atomic Nevanlinna integral is the logarithmic derivative of the genus-one
product, up to its convergent real linear correction. The remaining term is
affine, with a nonpositive real slope.
-/

public section

open Complex MeasureTheory
open scoped ComplexConjugate

namespace RealRooted

private theorem weighted_nevanlinnaKernel_eq {r : ℝ} (hr : r ≠ 0) {z : ℂ}
    (hz : z ≠ (r : ℂ)) (m : ℕ) :
    (((m : ℝ) / (1 + r ^ 2) : ℝ) : ℂ) * TauCeti.nevanlinnaKernel z r =
      -(m : ℂ) * logDerivWeierstrassFactorOneMul (r : ℂ)⁻¹ z +
        (((m : ℝ) / (r * (1 + r ^ 2)) : ℝ) : ℂ) := by
  have hrC : (r : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr
  have hden : (1 + (r : ℂ) ^ 2) ≠ 0 := by
    exact_mod_cast (show 1 + r ^ 2 ≠ 0 by positivity)
  rw [TauCeti.nevanlinnaKernel_def, logDerivWeierstrassFactorOneMul_inv hrC hz]
  push_cast
  field_simp [hrC, hden, sub_ne_zero.mpr hz, sub_ne_zero.mpr hz.symm]
  ring

/-- All generalized Laguerre inequalities determine the logarithmic derivative
from its real-zero canonical product and an affine term with nonpositive slope. -/
theorem exists_logDeriv_eq_realZeroProduct {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hc : ∀ z, f (conj z) = conj (f z)) (hf0 : f 0 ≠ 0)
    (h : ∀ x n, 0 ≤ laguerreCoefficient f x n) :
    ∃ a b : ℝ, 0 ≤ b ∧ ∀ z ∈ UpperHalfPlane.upperHalfPlaneSet,
      logDeriv f z = (a : ℂ) - (b : ℂ) * z + logDeriv (realZeroProduct f) z := by
  have hne : f ≠ 0 := fun hzero => hf0 (congrFun hzero 0)
  obtain ⟨ρ, b, hρ, hb, hrep, hs, _⟩ := exists_nevanlinna_supported_on_zeros hf hc h
  let _ := hρ
  let t : ℝ := ∑' r : {x : ℝ | f x = 0},
    (analyticOrderNatAt f (r : ℂ) : ℝ) / ((r : ℝ) * (1 + (r : ℝ) ^ 2))
  have ht : HasSum (fun r : {x : ℝ | f x = 0} =>
      (((analyticOrderNatAt f (r : ℂ) : ℝ) /
        ((r : ℝ) * (1 + (r : ℝ) ^ 2)) : ℝ) : ℂ)) (t : ℂ) :=
    Complex.hasSum_ofReal.mpr
      (summable_analyticOrderNatAt_div_mul_one_add_sq hf hc hf0 h).hasSum
  refine ⟨-t - (-logDeriv f I).re, b, hb, fun z hz => ?_⟩
  have hzpos : 0 < z.im := hz
  have hp := (summable_norm_natCast_mul_logDerivWeierstrassFactorOneMul _ _
    (summable_analyticOrderNatAt_mul_norm_inv_sq hf hc hf0 h) z).of_norm.hasSum
  rw [← logDeriv_realZeroProduct hf hc hf0 h hzpos] at hp
  have hsum := hp.neg.add ht
  have hkernel := hasSum_nevanlinnaKernel_real_zeros hf hne hs hz
  have hatom := measureReal_singleton_eq_analyticOrderNatAt_div hf hne hrep
  have heq : (∫ x, TauCeti.nevanlinnaKernel z x ∂ρ) =
      -logDeriv (realZeroProduct f) z + (t : ℂ) := by
    apply HasSum.unique hkernel
    convert hsum using 1
    ext r
    rw [hatom]
    have hr : (r : ℝ) ≠ 0 := fun hzero => hf0 (by simpa [hzero] using r.property)
    have hzr : z ≠ (r : ℂ) := fun heq => by simp [heq] at hzpos
    simpa only [neg_mul] using weighted_nevanlinnaKernel_eq hr hzr (analyticOrderNatAt f r)
  have hre := hrep z hz
  rw [heq] at hre
  push_cast
  linear_combination -hre

end RealRooted
