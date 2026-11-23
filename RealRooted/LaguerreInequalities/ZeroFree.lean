module

public import RealRooted.LaguerreInequalities.Analytic
public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya
public import Mathlib.Analysis.Complex.Exponential
import RealRooted.LaguerreInequalities.MeasureSupport
import RealRooted.Mathlib.Analysis.Calculus.LogDeriv.Identity
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Derivative
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.GeneralizedInequality
import Mathlib.Analysis.Complex.Convex

/-!
# Zero-free functions satisfying all generalized Laguerre inequalities

The supported Nevanlinna measure vanishes when the entire function has no zeros.
Its negative logarithmic derivative is then affine, and the function is a real
exponential times a Gaussian, including constant and ordinary exponential cases.
No order or genus hypothesis is needed.
-/

public section

open Complex MeasureTheory Set
open scoped ComplexConjugate

namespace RealRooted

/-- A zero-free real entire function satisfying all generalized Laguerre
inequalities is a constant times a real exponential and a nonnegative Gaussian. -/
theorem exists_exp_quadratic_of_laguerreCoefficient_nonneg {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hc : ∀ z, f (conj z) = conj (f z))
    (h : ∀ x n, 0 ≤ laguerreCoefficient f x n) (hn : ∀ z, f z ≠ 0) :
    ∃ a b : ℝ, 0 ≤ b ∧ ∀ z : ℂ,
      f z = f 0 * exp ((a : ℂ) * z - (b : ℂ) * z ^ 2 / 2) := by
  obtain ⟨ρ, b, hρ, hb, hrep, hs, _⟩ := exists_nevanlinna_supported_on_zeros hf hc h
  let _ := hρ
  have hempty : ρ.support = ∅ := by
    ext r
    exact ⟨fun hr => (hn r (hs hr)).elim, fun hr => hr.elim⟩
  have hρzero : ρ = 0 := Measure.support_eq_empty_iff.mp hempty
  let a : ℝ := -(-logDeriv f I).re
  let g : ℂ → ℂ := fun z => exp ((a : ℂ) * z - (b : ℂ) * z ^ 2 / 2)
  have hg : Differentiable ℂ g := by dsimp [g]; fun_prop
  have hglog (z : ℂ) : logDeriv g z = (a : ℂ) - (b : ℂ) * z := by
    have hp : HasDerivAt (fun w : ℂ => (a : ℂ) * w - (b : ℂ) * w ^ 2 / 2)
        ((a : ℂ) - (b : ℂ) * z) z := by
      convert ((hasDerivAt_id z).const_mul (a : ℂ)).sub
        ((((hasDerivAt_id z).pow 2).const_mul (b : ℂ)).div_const 2) using 1
      · ext w
        simp only [Pi.sub_apply, Pi.pow_apply, id_eq]
      · simp only [id_eq, mul_one]
        ring
    rw [logDeriv_apply, show deriv g z = _ from hp.cexp.deriv]
    exact mul_div_cancel_left₀ _ (exp_ne_zero _)
  refine ⟨a, b, hb, ?_⟩
  apply hf.eq_mul_of_logDeriv_eqOn hg UpperHalfPlane.isOpen_upperHalfPlaneSet
    (convex_halfSpace_im_gt 0).isPreconnected ⟨I, by simp⟩
    (fun z _ => hn z) (fun z _ => exp_ne_zero _)
  · intro z hz
    rw [hglog]
    have hzrep := hrep z hz
    rw [hρzero, integral_zero_measure, add_zero] at hzrep
    dsimp only [a]
    push_cast
    linear_combination -hzrep
  · simp only [g, mul_zero, zero_pow (by norm_num : 2 ≠ 0), zero_div, sub_zero, exp_zero]

/-- Every zero-free Laguerre--Pólya function is a constant times a real
exponential and a Gaussian with nonnegative coefficient. -/
theorem IsLaguerrePolya.exists_exp_quadratic_of_forall_ne_zero {f : ℂ → ℂ}
    (hf : IsLaguerrePolya f) (hn : ∀ z, f z ≠ 0) :
    ∃ a b : ℝ, 0 ≤ b ∧ ∀ z : ℂ,
      f z = f 0 * exp ((a : ℂ) * z - (b : ℂ) * z ^ 2 / 2) :=
  exists_exp_quadratic_of_laguerreCoefficient_nonneg hf.differentiable hf.conj
    hf.laguerreCoefficient_nonneg hn

end RealRooted
