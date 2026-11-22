module

public import RealRooted.LaguerreInequalities.AuxiliaryQuartic
public import RealRooted.LaguerreInequalities.Analytic
public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.GeneralizedInequality
import RealRooted.Mathlib.Analysis.Calculus.IteratedDeriv.CompPowCoefficient
import Mathlib.Analysis.Complex.TaylorSeries

/-!
# A counterexample to the fixed-auxiliary converse without a growth hypothesis

For `p = X^4 + 4` and `f(z) = exp (-z^4)`, every Taylor coefficient of
`∏ j, f(x + α_j t)` is nonnegative at every real `x`, although `f` is not
Laguerre--Pólya. The actual coefficients are calculated by complex differentiation.

This is a newly derived counterexample to the fixed-auxiliary formulation of
Csordas--Vishnyakova, *The generalized Laguerre inequalities and functions in the
Laguerre--Pólya class* (2013), Conjecture 3.6, p.1649,
https://doi.org/10.2478/s11533-013-0269-x.
It does not contradict their Theorem 3.5 or Cardon's original Theorem 2.1:
those statements impose an additional genus/growth restriction. Nor does it
address a condition requiring positivity for every admissible auxiliary.
-/

@[expose] public section

open Complex Polynomial
open scoped ComplexConjugate

noncomputable section

namespace RealRooted

/-- The explicit real Taylor coefficients of the translated quartic product. -/
def quarticTranslateCoefficient (x : ℝ) (n : ℕ) : ℝ :=
  if 4 ∣ n then Real.exp (-4 * x ^ 4) * 16 ^ (n / 4) / (n / 4).factorial else 0

private theorem iteratedDeriv_exp_quartic_zero (c : ℂ) (n : ℕ) :
    iteratedDeriv n (fun z : ℂ => exp (c * z ^ 4)) 0 =
      if 4 ∣ n then (n.factorial : ℂ) * (c ^ (n / 4) / (n / 4).factorial) else 0 := by
  have ha : AnalyticAt ℂ (fun z : ℂ => exp (c * z)) 0 := by fun_prop
  simpa only [iteratedDeriv_cexp_const_mul, mul_zero, exp_zero, mul_one] using
    iteratedDeriv_comp_pow_zero_eq ha (by norm_num : 0 < 4) n

/-- The explicit coefficients are the actual Taylor coefficients of the entire
translated product, including its zero coefficients. -/
theorem iteratedDeriv_quarticTranslateProduct_zero (x : ℝ) (n : ℕ) :
    iteratedDeriv n (quarticTranslateProduct x) 0 / (n.factorial : ℂ) =
      (quarticTranslateCoefficient x n : ℂ) := by
  have hp : quarticTranslateProduct x = fun t => exp (-4 * (x : ℂ) ^ 4) *
      exp (16 * t ^ 4) := funext (quarticTranslateProduct_eq x)
  have hx : exp (-4 * (x : ℂ) ^ 4) = (Real.exp (-4 * x ^ 4) : ℂ) := by
    simp only [Complex.ofReal_exp, ofReal_mul, ofReal_neg, ofReal_ofNat, ofReal_pow]
  rw [hp, iteratedDeriv_const_mul_field, iteratedDeriv_exp_quartic_zero, hx]
  have hn : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  by_cases h : 4 ∣ n
  · simp only [h, ite_eq_left, quarticTranslateCoefficient, ofReal_div, ofReal_mul,
      ofReal_pow, ofReal_ofNat, ofReal_natCast]
    field_simp
  · simp [h, quarticTranslateCoefficient]

/-- Every coefficient of the translated quartic product is nonnegative for every
real center, exactly as required by the fixed-auxiliary converse. -/
theorem quarticTranslateCoefficient_nonneg (x : ℝ) (n : ℕ) :
    0 ≤ quarticTranslateCoefficient x n := by
  unfold quarticTranslateCoefficient
  split_ifs <;> positivity

/-- The nonnegative coefficients give a convergent Taylor expansion at every
complex value of the translation parameter. -/
theorem hasSum_quarticTranslateCoefficient (x : ℝ) (t : ℂ) :
    HasSum (fun n => (quarticTranslateCoefficient x n : ℂ) * t ^ n)
      (quarticTranslateProduct x t) := by
  convert Complex.hasSum_taylorSeries_of_entire
    (differentiable_quarticTranslateProduct x) 0 t using 1
  ext n
  rw [← iteratedDeriv_quarticTranslateProduct_zero]
  simp only [sub_zero, smul_eq_mul, div_eq_mul_inv]
  ring

/-- The standard second generalized Laguerre coefficient of `exp (-z^4)`
is negative at the origin. -/
theorem laguerreCoefficient_quarticDecay_two : laguerreCoefficient quarticDecay 0 2 = -2 := by
  have hp : laguerreProduct quarticDecay 0 = fun z : ℂ => exp (-2 * z ^ 4) := by
    funext z
    simp only [laguerreProduct, quarticDecay, ofReal_zero, zero_add, zero_sub,
      ← Complex.exp_add]
    congr 1
    calc
      _ = -2 * z ^ 4 * I ^ 4 := by ring
      _ = _ := by rw [Complex.I_pow_four]; ring
  rw [laguerreCoefficient, hp, iteratedDeriv_exp_quartic_zero]
  norm_num

/-- The quartic exponential is outside the Laguerre--Pólya class, even though
it is real entire, zero-free, and passes every quartic-auxiliary inequality. -/
theorem not_isLaguerrePolya_quarticDecay : ¬ IsLaguerrePolya quarticDecay := by
  intro h
  have hn := h.laguerreCoefficient_nonneg 0 2
  rw [laguerreCoefficient_quarticDecay_two] at hn
  norm_num at hn

/-- A fully quantified counterexample to the fixed-auxiliary converse for an
arbitrary nonzero real entire function. The auxiliary is monic, even, has
nonnegative real coefficients and a nonreal zero; every actual Taylor coefficient
of its translated product is a nonnegative real number. -/
theorem exists_auxiliary_nonneg_not_isLaguerrePolya :
    ∃ (p : ℝ[X]) (α : Fin 4 → ℂ) (f : ℂ → ℂ),
      p.Monic ∧ HasNonnegCoeffs p ∧ p.comp (-X) = p ∧
      p.map ofRealHom = ∏ j : Fin 4, (X + C (α j)) ∧
      (∃ z : ℂ, (p.map ofRealHom).eval z = 0 ∧ z.im ≠ 0) ∧
      Differentiable ℂ f ∧ (∀ z, f (conj z) = conj (f z)) ∧ (∀ z, f z ≠ 0) ∧
      (∀ (x : ℝ) (k : ℕ), ∃ a : ℝ, 0 ≤ a ∧
        iteratedDeriv k (fun t : ℂ => ∏ j : Fin 4, f (x + α j * t)) 0 /
          (k.factorial : ℂ) = (a : ℂ)) ∧ ¬ IsLaguerrePolya f := by
  refine ⟨quarticAuxiliary, quarticSlope, quarticDecay, monic_quarticAuxiliary,
    hasNonnegCoeffs_quarticAuxiliary, quarticAuxiliary_comp_neg_X,
    map_quarticAuxiliary, ⟨1 + I, quarticAuxiliary_nonreal_zero⟩,
    differentiable_quarticDecay, quarticDecay_conj, quarticDecay_ne_zero, ?_,
    not_isLaguerrePolya_quarticDecay⟩
  intro x k
  exact ⟨quarticTranslateCoefficient x k, quarticTranslateCoefficient_nonneg x k,
    iteratedDeriv_quarticTranslateProduct_zero x k⟩

end RealRooted
