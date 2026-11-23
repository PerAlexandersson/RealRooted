module

public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya
public import RealRooted.LaguerreInequalities.AuxiliaryProduct
import RealRooted.LaguerreInequalities.AuxiliaryGenerating
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Derivative
import RealRooted.Mathlib.Analysis.Complex.PolynomialLimitCoeff

/-!
# Nonnegative auxiliary Taylor coefficients of Laguerre--Pólya functions

This is the forward implication of Cardon's fixed-auxiliary criterion.
The auxiliary may have zero roots. No division by the entire function occurs.
-/

public section

open Complex Filter Polynomial Topology

namespace RealRooted

/-- Every monic even auxiliary with nonnegative coefficients gives locally
uniform approximants with nonnegative coefficients. -/
theorem IsLaguerrePolya.exists_nonneg_auxiliaryProduct_approx {f : ℂ → ℂ}
    (hf : IsLaguerrePolya f) {g : ℝ[X]} (hg : g.Monic)
    (he : ∀ k, Odd k → g.coeff k = 0) (hc : HasNonnegCoeffs g) (x : ℝ) :
    ∃ p : ℕ → ℝ[X], (∀ i, HasNonnegCoeffs (p i)) ∧
      TendstoLocallyUniformly
        (fun i z ↦ ((p i).map ofRealHom).eval z) (auxiliaryProduct g f x) atTop := by
  have hcont := hf.differentiable.continuous
  obtain ⟨p, hp, hlim⟩ := hf
  have hs (i : ℕ) : (p i).Splits := (hp i).elim (fun h ↦ h ▸ Splits.zero) id
  have hprod := tendstoLocallyUniformly_auxiliaryProduct hlim hcont g x
  refine ⟨fun i ↦ auxiliaryGeneratingPolynomial g (p i) x,
    fun i ↦ hasNonnegCoeffs_auxiliaryGeneratingPolynomial hg he hc (p i) x, ?_⟩
  convert hprod using 1
  ext i z
  exact eval_auxiliaryGeneratingPolynomial hg (hs i) x z

/-- Cardon's auxiliary inequalities hold for every Laguerre--Pólya function
and every monic even auxiliary with nonnegative coefficients. -/
theorem IsLaguerrePolya.auxiliaryCoefficient_nonneg {f : ℂ → ℂ}
    (hf : IsLaguerrePolya f) {g : ℝ[X]} (hg : g.Monic)
    (he : ∀ k, Odd k → g.coeff k = 0) (hc : HasNonnegCoeffs g) (x : ℝ) (k : ℕ) :
    0 ≤ auxiliaryCoefficient g f x k := by
  obtain ⟨p, hp, hlim⟩ := hf.exists_nonneg_auxiliaryProduct_approx hg he hc x
  have hl := Polynomial.tendsto_coeff_of_tendstoLocallyUniformly hlim k
  simpa only [Complex.div_natCast_re, auxiliaryCoefficient] using
    ge_of_tendsto hl (Eventually.of_forall fun i ↦ hp i k)

end RealRooted
