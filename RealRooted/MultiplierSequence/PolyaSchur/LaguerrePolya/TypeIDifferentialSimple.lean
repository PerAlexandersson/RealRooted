module

public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.TypeI
public import RealRooted.Mathlib.Analysis.Complex.InfiniteDifferential.Basic
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Derivative
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Zeros
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.TypeIPureProduct
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.TypeIOriginFactor
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.IteratedDerivative
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.GrowthOrder
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.GenusZeroDifferentialSimple
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.InfiniteDifferentialEntire
import RealRooted.Mathlib.Analysis.Complex.InfiniteDifferential.SymbolAlgebra
import RealRooted.Mathlib.Analysis.Complex.InfiniteDifferential.PolynomialComposition
import RealRooted.Mathlib.Analysis.Complex.InfiniteDifferential.OrderDerivative
import RealRooted.Mathlib.Analysis.Calculus.IteratedDeriv.PolynomialAlgebra

/-!
# Simple infinite differential images for Type-I symbols of order below one

Nonpolynomiality and a growth bound strictly below one eliminate the finite
product and exponential exceptions. An origin factor is absorbed into a
derivative of the target. The actual image may vanish identically.
-/

public section

open Complex Polynomial

namespace RealRooted

/-- A nonpolynomial Type-I symbol of order below one and nonzero at zero
gives only simple zeros whenever its actual differential image is nonzero. -/
private theorem deriv_differential_ne_zero_of_ne_zero
    {φ f : ℂ → ℂ} (hφ : IsLaguerrePolyaTypeI φ) (hf : IsLaguerrePolya f)
    (h0 : φ 0 ≠ 0) {ρ : ℝ} (horder : TauCeti.OrderLE φ ρ) (hρ : ρ < 1)
    (hnp : ∀ p : ℂ[X], φ ≠ fun z => p.eval z)
    (hne : infiniteDifferentialApply φ f ≠ 0)
    {z : ℂ} (hz : infiniteDifferentialApply φ f z = 0) :
    _root_.deriv (infiniteDifferentialApply φ f) z ≠ 0 := by
  obtain ⟨a, _, hs, hprod⟩ := hφ.exists_eq_prod_of_order_lt_one h0 horder hρ
  let ψ : ℂ → ℂ := fun z => ∏' j, (1 + (a j : ℂ) * z)
  have hψnp (p : ℂ[X]) : ψ ≠ fun z => p.eval z := by
    intro hp
    apply hnp (C (φ 0) * p)
    ext w
    rw [congrFun hprod w]
    change φ 0 * ψ w = _
    rw [congrFun hp w]
    simp only [eval_mul, eval_C]
  have heq : infiniteDifferentialApply φ f =
      fun w => φ 0 * infiniteDifferentialApply ψ f w := by
    calc
      _ = infiniteDifferentialApply (fun w => φ 0 * ψ w) f :=
        congrArg (fun u => infiniteDifferentialApply u f) hprod
      _ = _ := infiniteDifferentialApply_const_mul_symbol (φ 0) ψ f
  have hψne : infiniteDifferentialApply ψ f ≠ 0 := by
    intro hzero
    apply hne
    rw [heq, hzero]
    ext w
    simp only [Pi.zero_apply, mul_zero]
  have hψz : infiniteDifferentialApply ψ f z = 0 := by
    rw [heq] at hz
    exact (mul_eq_zero.mp hz).resolve_left h0
  have hd := hf.deriv_genusZero_differential_ne_zero hs hψnp hψne hψz
  rw [heq, deriv_const_mul_field]
  exact mul_ne_zero h0 hd

/-- A nonpolynomial Type-I symbol of order below one gives only simple zeros
in every nonzero differential image. Arbitrary origin multiplicity is allowed. -/
theorem IsLaguerrePolyaTypeI.deriv_differential_ne_zero_of_order_lt_one
    {φ f : ℂ → ℂ} (hφ : IsLaguerrePolyaTypeI φ) (hf : IsLaguerrePolya f)
    {ρ : ℝ} (horder : TauCeti.OrderLE φ ρ) (hρ : ρ < 1)
    (hnp : ∀ p : ℂ[X], φ ≠ fun z => p.eval z)
    (hne : infiniteDifferentialApply φ f ≠ 0)
    {z : ℂ} (hz : infiniteDifferentialApply φ f z = 0) :
    _root_.deriv (infiniteDifferentialApply φ f) z ≠ 0 := by
  have hφne : φ ≠ 0 := by
    intro hzero
    apply hnp 0
    ext w
    simp only [hzero, Pi.zero_apply, eval_zero]
  obtain ⟨ψ, hψ, hψ0, hoψ, heq⟩ :=
    hφ.exists_origin_factor_of_order hφne horder hρ.le
  let m := analyticOrderNatAt φ 0
  have hψnp (p : ℂ[X]) : ψ ≠ fun w => p.eval w := by
    intro hp
    apply hnp (X ^ m * p)
    rw [heq, hp]
    ext w
    simp only [eval_mul, eval_pow, eval_X, m]
  have hop : infiniteDifferentialApply φ f =
      infiniteDifferentialApply ψ (iteratedDeriv m f) := by
    rw [heq]
    have hc := infiniteDifferentialApply_polynomial_mul (monomial m 1)
      hψ.toLaguerrePolya.differentiable hoψ (p := (1 : ℝ)) (by norm_num) hρ
      hf.differentiable hf.orderLE_two (q := (3 : ℝ)) (by norm_num) (by norm_num)
      (by norm_num)
    have hd := iteratedDeriv_infiniteDifferentialApply_of_order
      hψ.toLaguerrePolya.differentiable hoψ (p := (1 : ℝ)) (by norm_num) hρ
      hf.differentiable hf.orderLE_two (q := (3 : ℝ)) (by norm_num) (by norm_num)
      (by norm_num) m
    simp only [eval_monomial, differentialApply_monomial, one_mul] at hc
    exact hc.trans hd
  rw [hop] at hne hz ⊢
  exact deriv_differential_ne_zero_of_ne_zero hψ (hf.iteratedDeriv m)
    hψ0 hoψ hρ hψnp hne hz

/-- The zero-aware genus-zero strictness criterion for a natural Type-I symbol:
the output is identically zero or LP with only simple real zeros. -/
theorem IsLaguerrePolyaTypeI.differential_simple_or_zero_of_order_lt_one
    {φ f : ℂ → ℂ} (hφ : IsLaguerrePolyaTypeI φ) (hf : IsLaguerrePolya f)
    {ρ : ℝ} (horder : TauCeti.OrderLE φ ρ) (hρ : ρ < 1)
    (hnp : ∀ p : ℂ[X], φ ≠ fun z => p.eval z) :
    infiniteDifferentialApply φ f = 0 ∨
      IsLaguerrePolya (infiniteDifferentialApply φ f) ∧
      ∀ z, infiniteDifferentialApply φ f z = 0 →
        z.im = 0 ∧ _root_.deriv (infiniteDifferentialApply φ f) z ≠ 0 := by
  by_cases hne : infiniteDifferentialApply φ f = 0
  · exact Or.inl hne
  · have hLP := hφ.toLaguerrePolya.infiniteDifferentialApply_of_left_order hf horder
      (lt_trans hρ (by norm_num))
    exact Or.inr ⟨hLP, fun z hz => ⟨hLP.im_eq_zero_of_eq_zero hne hz,
      hφ.deriv_differential_ne_zero_of_order_lt_one hf horder hρ hnp hne hz⟩⟩

end RealRooted
