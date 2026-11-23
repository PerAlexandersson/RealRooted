module

public import RealRooted.LaguerreInequalities.AuxiliaryProduct
import RealRooted.LaguerreInequalities.AuxiliarySymmetry
import RealRooted.Mathlib.Analysis.Complex.TranslateProductNonzero
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Real zeros detected by an auxiliary with nonzero roots

This is the analytic core of Cardon's converse. Removing zero auxiliary
roots is a separate step: they are not excluded from the final criterion.
-/

public section

open Complex Polynomial
open scoped ComplexConjugate

namespace RealRooted

private theorem hasSum_auxiliaryProduct {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (g : ℝ[X]) (x y : ℝ) :
    HasSum (fun n ↦ auxiliaryCoefficient g f x n * y ^ n)
      (auxiliaryProduct g f x y).re := by
  have h := Complex.hasSum_re
    (Complex.hasSum_taylorSeries_of_entire (differentiable_auxiliaryProduct hf g x) 0
      (y : ℂ))
  convert h using 1
  ext n
  simp only [auxiliaryCoefficient, sub_zero, smul_eq_mul]
  rw [← Complex.div_natCast_re, ← Complex.re_mul_ofReal]
  congr 1
  push_cast
  ring

private theorem auxiliaryProduct_eq_zero_of_pos_zero {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hc : ∀ z, f (conj z) = conj (f z))
    (g : ℝ[X]) (x : ℝ) (h : ∀ k, 0 ≤ auxiliaryCoefficient g f x k)
    {r : ℝ} (hr : 0 < r) (hz : auxiliaryProduct g f x r = 0) :
    auxiliaryProduct g f x = 0 := by
  have hs := hasSum_auxiliaryProduct hf g x r
  rw [hz, zero_re] at hs
  have hderiv (k : ℕ) : iteratedDeriv k (auxiliaryProduct g f x) 0 = 0 := by
    have hle := le_hasSum hs k (fun j _ ↦ mul_nonneg (h j) (pow_nonneg hr.le j))
    have heq := le_antisymm hle (mul_nonneg (h k) (pow_nonneg hr.le k))
    have ha := (mul_eq_zero.mp heq).resolve_right (pow_ne_zero k hr.ne')
    have hd : iteratedDeriv k (auxiliaryProduct g f x) 0 / (k.factorial : ℂ) = 0 := by
      rw [← ofReal_auxiliaryCoefficient hc g x k, ha, ofReal_zero]
    exact (div_eq_zero_iff.mp hd).resolve_right (by exact_mod_cast k.factorial_ne_zero)
  funext z
  rw [← Complex.taylorSeries_eq_of_entire' 0 z (differentiable_auxiliaryProduct hf g x)]
  simp [hderiv]

/-- An even auxiliary with a nonreal root and nonzero constant coefficient
detects every nonreal zero of a nonzero real entire function. -/
theorem im_eq_zero_of_auxiliary_nonneg_of_coeff_zero_ne_zero
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hc : ∀ z, f (conj z) = conj (f z)) (hne : f ≠ 0) {g : ℝ[X]}
    (he : ∀ k, Odd k → g.coeff k = 0) (h0 : g.coeff 0 ≠ 0)
    (ha : ∃ a ∈ (g.map ofRealHom).roots, a.im ≠ 0)
    (h : ∀ x k, 0 ≤ auxiliaryCoefficient g f x k) {z : ℂ} (hz : f z = 0) :
    z.im = 0 := by
  by_contra him
  obtain ⟨a, ha, haim⟩ := ha
  let t : ℝ := -z.im / a.im
  let x : ℝ := z.re + a.re * t
  have ht : t ≠ 0 := div_ne_zero (neg_ne_zero.mpr him) haim
  have heq : (x : ℂ) - a * (t : ℂ) = z := by
    apply Complex.ext
    · simp only [sub_re, ofReal_re, mul_re, ofReal_im, mul_zero, sub_zero]
      dsimp only [x]
      ring
    · simp only [sub_im, ofReal_im, mul_im, ofReal_re, mul_zero, zero_add]
      dsimp only [t]
      field_simp [haim]
      ring
  have hzero : auxiliaryProduct g f x t = 0 := by
    apply Multiset.prod_eq_zero
    exact Multiset.mem_map.mpr ⟨a, ha, by rw [heq, hz]⟩
  have habs : auxiliaryProduct g f x (|t| : ℝ) = 0 := by
    rcases le_total 0 t with hpos | hneg
    · simpa only [abs_of_nonneg hpos] using hzero
    · simpa only [abs_of_nonpos hneg, ofReal_neg, auxiliaryProduct_neg he] using hzero
  have hs : ∀ r ∈ (g.map ofRealHom).roots, r ≠ 0 := by
    intro r hr hr0
    have hg0 : g.map ofRealHom ≠ 0 := ne_zero_of_mem_roots hr
    have hv := (mem_roots hg0).mp hr
    rw [hr0] at hv
    have hz0 : (g.coeff 0 : ℂ) = 0 := by
      simpa [IsRoot, coeff_map, ← coeff_zero_eq_eval_zero] using hv
    exact h0 (ofReal_eq_zero.mp hz0)
  exact (translateProduct_ne_zero hf hne (g.map ofRealHom).roots hs x)
    (auxiliaryProduct_eq_zero_of_pos_zero hf hc g x (h x) (abs_pos.mpr ht) habs)

end RealRooted
