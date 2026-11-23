module

public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya
public import TauCeti.Analysis.Complex.GrowthOrder
public import Mathlib.Analysis.Analytic.Order
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Derivative
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.RootDivision
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.GrowthOrder
import TauCeti.Analysis.Complex.GrowthOrder.Zero.Factorization

/-!
# Removing the full origin zero of a Laguerre--Pólya function
-/

public section

namespace RealRooted

/-- Removing the full origin zero preserves LP and every supplied growth bound. -/
theorem IsLaguerrePolya.exists_origin_factor_of_order {f : ℂ → ℂ} {ρ : ℝ}
    (hf : IsLaguerrePolya f) (hne : f ≠ 0) (ho : TauCeti.OrderLE f ρ) :
    ∃ g : ℂ → ℂ, IsLaguerrePolya g ∧ g 0 ≠ 0 ∧ TauCeti.OrderLE g ρ ∧
      f = fun z : ℂ ↦ z ^ analyticOrderNatAt f 0 * g z := by
  obtain ⟨g, hgd, hg0, hgo, heq⟩ :=
    ho.exists_eq_sub_pow_mul hf.differentiable (Function.ne_iff.mp hne) 0
  have hfactor : f = fun z : ℂ ↦ z ^ analyticOrderNatAt f 0 * g z := by
    funext z
    simpa only [sub_zero] using heq z
  have hprod : IsLaguerrePolya (fun z : ℂ ↦ (z - (0 : ℝ)) ^
      analyticOrderNatAt f 0 * g z) := by
    simpa only [Complex.ofReal_zero, sub_zero, ← hfactor] using hf
  exact ⟨g, hprod.of_sub_pow_mul 0 _ hgd, hg0, hgo, hfactor⟩

/-- Every nonzero LP function is its full origin monomial times an LP
function nonzero at the origin. No growth premise is required. -/
theorem IsLaguerrePolya.exists_origin_factor {f : ℂ → ℂ}
    (hf : IsLaguerrePolya f) (hne : f ≠ 0) :
    ∃ g : ℂ → ℂ, IsLaguerrePolya g ∧ g 0 ≠ 0 ∧
      f = fun z : ℂ ↦ z ^ analyticOrderNatAt f 0 * g z := by
  obtain ⟨g, hg, hg0, _, heq⟩ := hf.exists_origin_factor_of_order hne hf.orderLE_two
  exact ⟨g, hg, hg0, heq⟩

end RealRooted
