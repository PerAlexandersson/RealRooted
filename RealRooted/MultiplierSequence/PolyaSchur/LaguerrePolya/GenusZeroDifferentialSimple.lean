module

public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya
public import RealRooted.Mathlib.Analysis.Complex.InfiniteDifferential.Basic
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Derivative
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Zeros
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.DifferentialTailSimple
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.InfiniteDifferentialEntire
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.GrowthOrder
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.LinearProduct
import RealRooted.Mathlib.Algebra.Polynomial.LinearProductDegree
import RealRooted.Mathlib.Analysis.Complex.LinearProductPrefix
import RealRooted.Mathlib.Analysis.Complex.InfiniteDifferential.PolynomialComposition
import RealRooted.Mathlib.Analysis.Complex.InfiniteDifferential.GenusZeroTail

/-!
# Simple zeros for nonpolynomial genus-zero differential symbols

This is the pure genus-zero case of Cardon--de Gaston (2005), Theorem 1.
The target may be any LP function, including one of order exactly two.
The actual differential series either vanishes identically or has only simple
real zeros. No claim of injectivity is made: exponential targets can be killed
when their exponent is a zero of the symbol.

The proof uses finite-factor multiplicity descent and canonical-tail
convergence. It does not require composition of two infinite operators.
-/

public section

open Complex Polynomial Filter Topology

namespace RealRooted

/-- The actual infinite image factors as a finite prefix operator acting on
the canonical-tail image. Convergence permits targets of order exactly two. -/
private theorem infiniteDifferentialApply_eq_prefix_apply_tail
    {a : ℕ → ℝ} (ha : Summable a) {f : ℂ → ℂ} (hf : IsLaguerrePolya f) (n : ℕ) :
    infiniteDifferentialApply (fun z : ℂ => ∏' j, (1 + (a j : ℂ) * z)) f =
      ((∏ j ∈ Finset.range n, (1 + C (a j) * X : ℝ[X])).map ofRealHom).differentialApply
        (infiniteDifferentialApply
          (fun z : ℂ => ∏' j : ℕ, (1 + (a (j + n) : ℂ) * z)) f) := by
  rw [tprod_one_add_eq_prefix_mul_tail ha n]
  have ht := (summable_nat_add_iff n).mpr ha
  exact infiniteDifferentialApply_polynomial_mul _
    (isLaguerrePolya_tprod_one_add_mul ht).differentiable
    (orderLE_tprod_one_add_ofReal_mul ht) (p := (3 / 2 : ℝ)) (by norm_num) (by norm_num)
    hf.differentiable hf.orderLE_two (q := (5 / 2 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num)

/-- Every zero of a nonzero image under a nonpolynomial pure genus-zero
LP symbol is simple. Signed slopes, repeated slopes, and zero slopes are allowed. -/
theorem IsLaguerrePolya.deriv_genusZero_differential_ne_zero
    {f : ℂ → ℂ} (hf : IsLaguerrePolya f) {a : ℕ → ℝ} (ha : Summable a)
    (hnp : ∀ p : ℂ[X],
      (fun z : ℂ => ∏' j, (1 + (a j : ℂ) * z)) ≠ fun z => p.eval z)
    (hne : infiniteDifferentialApply (fun z : ℂ => ∏' j, (1 + (a j : ℂ) * z)) f ≠ 0)
    {z : ℂ} (hz : infiniteDifferentialApply
      (fun z : ℂ => ∏' j, (1 + (a j : ℂ) * z)) f z = 0) :
    _root_.deriv (infiniteDifferentialApply
      (fun z : ℂ => ∏' j, (1 + (a j : ℂ) * z)) f) z ≠ 0 := by
  have hLP := (isLaguerrePolya_tprod_one_add_mul ha).infiniteDifferentialApply_of_left_order
    hf (orderLE_tprod_one_add_ofReal_mul ha) (by norm_num)
  have him := hLP.im_eq_zero_of_eq_zero hne hz
  have heq : (z.re : ℂ) = z := by apply Complex.ext <;> simp [him]
  rw [← heq] at hz ⊢
  have hf0 : f ≠ 0 := by
    intro hzero
    apply hne
    rw [hzero]
    ext w
    simp only [infiniteDifferentialApply, iteratedDeriv_const_zero, mul_zero,
      zero_div, tsum_zero, Pi.zero_apply]
  apply deriv_ne_zero_of_differential_tails
    (g := fun n => infiniteDifferentialApply
      (fun z : ℂ => ∏' j : ℕ, (1 + (a (j + n) : ℂ) * z)) f)
    (p := fun n => ∏ j ∈ Finset.range n, (1 + C (a j) * X : ℝ[X]))
    _ (tendstoLocallyUniformly_infiniteDifferentialApply_linear_tail
      ha hf.differentiable hf.orderLE_two) hf.differentiable hf0 _
    (tendsto_natDegree_prod_one_add (infinite_support_of_tprod_ne_polynomial hnp))
    (infiniteDifferentialApply_eq_prefix_apply_tail ha hf) hne hz
  · intro n
    have ht := (summable_nat_add_iff n).mpr ha
    exact (isLaguerrePolya_tprod_one_add_mul ht).infiniteDifferentialApply_of_left_order
      hf (orderLE_tprod_one_add_ofReal_mul ht) (by norm_num)
  · intro n
    exact Splits.prod (fun j _ => splits_one_add_C_mul_X (a j))

/-- Zero-aware form: the actual image of any LP target under a nonpolynomial
pure genus-zero symbol is identically zero or LP with only simple real zeros. -/
theorem IsLaguerrePolya.genusZero_differential_simple_or_zero
    {f : ℂ → ℂ} (hf : IsLaguerrePolya f) {a : ℕ → ℝ} (ha : Summable a)
    (hnp : ∀ p : ℂ[X],
      (fun z : ℂ => ∏' j, (1 + (a j : ℂ) * z)) ≠ fun z => p.eval z) :
    infiniteDifferentialApply (fun z : ℂ => ∏' j, (1 + (a j : ℂ) * z)) f = 0 ∨
      IsLaguerrePolya (infiniteDifferentialApply
        (fun z : ℂ => ∏' j, (1 + (a j : ℂ) * z)) f) ∧
      ∀ z, infiniteDifferentialApply (fun z : ℂ => ∏' j, (1 + (a j : ℂ) * z)) f z = 0 →
        z.im = 0 ∧ _root_.deriv (infiniteDifferentialApply
          (fun z : ℂ => ∏' j, (1 + (a j : ℂ) * z)) f) z ≠ 0 := by
  by_cases hne : infiniteDifferentialApply (fun z : ℂ => ∏' j, (1 + (a j : ℂ) * z)) f = 0
  · exact Or.inl hne
  · have hLP := (isLaguerrePolya_tprod_one_add_mul ha).infiniteDifferentialApply_of_left_order
      hf (orderLE_tprod_one_add_ofReal_mul ha) (by norm_num)
    exact Or.inr ⟨hLP, fun z hz => ⟨hLP.im_eq_zero_of_eq_zero hne hz,
      hf.deriv_genusZero_differential_ne_zero ha hnp hne hz⟩⟩

end RealRooted
