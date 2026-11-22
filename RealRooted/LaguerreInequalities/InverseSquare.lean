module

public import RealRooted.LaguerreInequalities.Analytic
public import Mathlib.Analysis.Analytic.Order
import RealRooted.LaguerreInequalities.AtomMultiplicity
import RealRooted.Mathlib.Analysis.Normed.Field.WeightedInverse

/-!
# Inverse-square summability from generalized Laguerre inequalities

A nonzero value at the origin separates every real zero from zero. The finite
Nevanlinna measure then supplies the inverse-square summability needed for the
genus-one canonical product, as well as its convergent real linear correction.
-/

public section

open Complex Filter Metric Set Topology
open scoped ComplexConjugate

namespace RealRooted

private theorem exists_pos_le_abs_real_zero {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hf0 : f 0 ≠ 0) : ∃ δ : ℝ, 0 < δ ∧ ∀ r : ℝ, f r = 0 → δ ≤ |r| := by
  obtain ⟨δ, hδ, hs⟩ := Metric.mem_nhds_iff.mp
    (hf.continuous.continuousAt.eventually_ne hf0)
  refine ⟨δ, hδ, fun r hr => le_of_not_gt fun hlt => ?_⟩
  have hmem : (r : ℂ) ∈ ball 0 δ := by
    simpa only [mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs] using hlt
  exact hs hmem hr

/-- Every real zero has inverse-square summable multiplicity when all generalized
Laguerre inequalities hold and the origin is not a zero. -/
theorem summable_analyticOrderNatAt_div_sq {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hc : ∀ z, f (conj z) = conj (f z)) (hf0 : f 0 ≠ 0)
    (h : ∀ x n, 0 ≤ laguerreCoefficient f x n) :
    Summable (fun r : {x : ℝ | f x = 0} =>
      (analyticOrderNatAt f (r : ℂ) : ℝ) / (r : ℝ) ^ 2) := by
  have hne : f ≠ 0 := fun hzero => hf0 (congrFun hzero 0)
  obtain ⟨δ, hδ, hr⟩ := exists_pos_le_abs_real_zero hf hf0
  exact (summable_analyticOrderNatAt_div_one_add_sq hf hc hne h).div_sq_of_abs_ge
    (fun _ => Nat.cast_nonneg _) hδ (fun r => hr r r.property)

/-- The natural-multiplicity canonical product satisfies the exact complex norm
summability hypothesis of the genus-one convergence theorems. -/
theorem summable_analyticOrderNatAt_mul_norm_inv_sq {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hc : ∀ z, f (conj z) = conj (f z)) (hf0 : f 0 ≠ 0)
    (h : ∀ x n, 0 ≤ laguerreCoefficient f x n) :
    Summable (fun r : {x : ℝ | f x = 0} =>
      (analyticOrderNatAt f (r : ℂ) : ℝ) * ‖(r : ℂ)⁻¹‖ ^ 2) := by
  simpa only [norm_inv, Complex.norm_real, Real.norm_eq_abs, ← abs_inv, sq_abs, ← inv_pow,
    div_eq_mul_inv] using summable_analyticOrderNatAt_div_sq hf hc hf0 h

/-- The real linear correction in the genus-one Nevanlinna normalization is an
absolutely convergent series. -/
theorem summable_analyticOrderNatAt_div_mul_one_add_sq {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hc : ∀ z, f (conj z) = conj (f z)) (hf0 : f 0 ≠ 0)
    (h : ∀ x n, 0 ≤ laguerreCoefficient f x n) :
    Summable (fun r : {x : ℝ | f x = 0} =>
      (analyticOrderNatAt f (r : ℂ) : ℝ) / ((r : ℝ) * (1 + (r : ℝ) ^ 2))) := by
  have hne : f ≠ 0 := fun hzero => hf0 (congrFun hzero 0)
  obtain ⟨δ, hδ, hr⟩ := exists_pos_le_abs_real_zero hf hf0
  exact (summable_analyticOrderNatAt_div_one_add_sq hf hc hne h).div_mul_one_add_sq_of_abs_ge
    (fun _ => Nat.cast_nonneg _) hδ (fun r => hr r r.property)

end RealRooted
