module

public import RealRooted.LaguerreInequalities.Analytic
public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya
public import TauCeti.Analysis.Complex.CanonicalProduct.ElementaryFactor
import RealRooted.LaguerreInequalities.InverseSquare
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.IndexedProduct
import TauCeti.Analysis.Complex.CanonicalProduct.LogDeriv

/-!
# The genus-one product over actual real zeros

The generalized Laguerre inequalities supply the convergence hypothesis for the
canonical product, with the actual analytic multiplicity at each real zero.
When the origin is not a zero, the product has exactly those real zeros.
-/

public section

open Complex
open scoped ComplexConjugate

namespace RealRooted

/-- The genus-one product over the real zeros away from the origin, counted with
analytic multiplicity. A zero at the origin contributes the constant factor one. -/
@[expose] noncomputable def realZeroProduct (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  ∏' r : {x : ℝ | f x = 0}, weierstrassFactor 1 ((r : ℂ)⁻¹ * z) ^
    analyticOrderNatAt f (r : ℂ)

/-- The canonical product has value one at the origin. -/
@[simp] theorem realZeroProduct_zero (f : ℂ → ℂ) : realZeroProduct f 0 = 1 := by
  simp [realZeroProduct]

/-- All generalized Laguerre inequalities make the real-zero product an entire function. -/
theorem differentiable_realZeroProduct {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hc : ∀ z, f (conj z) = conj (f z)) (hf0 : f 0 ≠ 0)
    (h : ∀ x n, 0 ≤ laguerreCoefficient f x n) :
    Differentiable ℂ (realZeroProduct f) :=
  differentiable_tprod_weierstrassFactor_one_pow _ _
    (summable_analyticOrderNatAt_mul_norm_inv_sq hf hc hf0 h)

/-- The real-zero product has no zeros in the upper half-plane. -/
theorem realZeroProduct_ne_zero_of_im_pos {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hc : ∀ z, f (conj z) = conj (f z)) (hf0 : f 0 ≠ 0)
    (h : ∀ x n, 0 ≤ laguerreCoefficient f x n) {z : ℂ} (hz : 0 < z.im) :
    realZeroProduct f z ≠ 0 := by
  rw [realZeroProduct, ne_eq, tprod_weierstrassFactor_one_pow_eq_zero_iff _ _
    (summable_analyticOrderNatAt_mul_norm_inv_sq hf hc hf0 h)]
  rintro ⟨r, _, hr⟩
  have hr0 : (r : ℂ) ≠ 0 := fun hzero =>
    hf0 (by simpa only [hzero] using (show f (r : ℂ) = 0 from r.property))
  have heq : z = (r : ℂ) := ((inv_mul_eq_one₀ hr0).mp hr).symm
  simp only [heq, ofReal_im, lt_self_iff_false] at hz

/-- The logarithmic derivative of the real-zero product is its paired rational series. -/
theorem logDeriv_realZeroProduct {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hc : ∀ z, f (conj z) = conj (f z)) (hf0 : f 0 ≠ 0)
    (h : ∀ x n, 0 ≤ laguerreCoefficient f x n) {z : ℂ} (hz : 0 < z.im) :
    logDeriv (realZeroProduct f) z = ∑' r : {x : ℝ | f x = 0},
      (analyticOrderNatAt f (r : ℂ) : ℂ) *
        logDerivWeierstrassFactorOneMul (r : ℂ)⁻¹ z := by
  apply logDeriv_tprod_weierstrassFactor_one_pow _ _
    (summable_analyticOrderNatAt_mul_norm_inv_sq hf hc hf0 h)
  intro r _ heq
  have hr0 : (r : ℂ) ≠ 0 := fun hzero =>
    hf0 (by simpa only [hzero] using (show f (r : ℂ) = 0 from r.property))
  have hzr : z = (r : ℂ) := ((inv_mul_eq_one₀ hr0).mp heq).symm
  simp only [hzr, ofReal_im, lt_self_iff_false] at hz

/-- The real-zero canonical product is in the Laguerre--Pólya class, without an
order hypothesis on the original function. -/
theorem isLaguerrePolya_realZeroProduct {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hc : ∀ z, f (conj z) = conj (f z)) (hf0 : f 0 ≠ 0)
    (h : ∀ x n, 0 ≤ laguerreCoefficient f x n) :
    IsLaguerrePolya (realZeroProduct f) := by
  have hs : Summable (fun r : {x : ℝ | f x = 0} =>
      (analyticOrderNatAt f (r : ℂ) : ℝ) * ((r : ℝ)⁻¹) ^ 2) := by
    simpa only [inv_pow, div_eq_mul_inv] using
      summable_analyticOrderNatAt_div_sq hf hc hf0 h
  unfold realZeroProduct
  simpa only [ofReal_inv] using
    isLaguerrePolya_tprod_weierstrassFactor_one_pow _ _ hs

end RealRooted
