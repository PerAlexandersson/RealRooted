module

public import RealRooted.LaguerreInequalities.CanonicalProduct
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.OriginFactor
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.GeneralizedInequality
import RealRooted.LaguerreInequalities.CanonicalRepresentation
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Derivative

/-!
# The native real canonical representation of every nonzero LP function
-/

public section

open Complex
open scoped ComplexConjugate

namespace RealRooted

/-- The closure definition of LP gives a literal real canonical expression,
including the actual origin multiplicity. The product uses the actual zeros
and multiplicities of the origin cofactor. -/
theorem IsLaguerrePolya.exists_eq_pow_mul_exp_mul_realZeroProduct {f : ℂ → ℂ}
    (hf : IsLaguerrePolya f) (hne : f ≠ 0) :
    ∃ g : ℂ → ℂ, IsLaguerrePolya g ∧ g 0 ≠ 0 ∧ ∃ c b A : ℝ,
      c ≠ 0 ∧ 0 ≤ A ∧ ∀ z : ℂ,
        f z = (c : ℂ) * z ^ analyticOrderNatAt f 0 *
          exp (-(A : ℂ) * z ^ 2 + (b : ℂ) * z) * realZeroProduct g z := by
  obtain ⟨g, hg, hg0, hfactor⟩ := hf.exists_origin_factor hne
  obtain ⟨b, B, hB, heq⟩ := exists_eq_exp_mul_realZeroProduct
    hg.differentiable hg.conj hg0 hg.laguerreCoefficient_nonneg
  have hreal : ((g 0).re : ℂ) = g 0 := by
    apply conj_eq_iff_re.mp
    simpa using (hg.conj 0).symm
  have hc : (g 0).re ≠ 0 := by
    intro hzero
    exact hg0 (hreal.symm.trans (by simp [hzero]))
  refine ⟨g, hg, hg0, (g 0).re, b, B / 2, hc,
    div_nonneg hB (by norm_num), fun z ↦ ?_⟩
  rw [congrFun hfactor z, heq z, hreal]
  have hexp : (b : ℂ) * z - (B : ℂ) * z ^ 2 / 2 =
      -((B / 2 : ℝ) : ℂ) * z ^ 2 + (b : ℂ) * z := by
    rw [ofReal_div, ofReal_ofNat]
    ring
  rw [hexp]
  ring

end RealRooted
