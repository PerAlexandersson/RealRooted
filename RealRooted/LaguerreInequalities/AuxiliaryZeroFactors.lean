module

public import RealRooted.LaguerreInequalities.AuxiliaryProduct
import RealRooted.LaguerreInequalities.AuxiliarySymmetry
import RealRooted.Mathlib.Analysis.Complex.RealIdentity
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Topology.Order.OrderClosed

/-!
# Removing zero auxiliary roots

Zero roots contribute a constant factor `f(x)^m` to the auxiliary product.
For even `m`, positivity descends wherever `f(x)` is nonzero and then extends
by continuity through every zero of `f` on the real axis.
-/

public section

open Complex Filter Polynomial Topology
open scoped ComplexConjugate

namespace RealRooted

/-- An origin factor of the auxiliary contributes the corresponding power
of the central function value to its translated product. -/
theorem auxiliaryProduct_X_pow_mul {q : ℝ[X]} (hq : q.Monic)
    (m : ℕ) (f : ℂ → ℂ) (x : ℝ) (z : ℂ) :
    auxiliaryProduct (X ^ m * q) f x z = f x ^ m * auxiliaryProduct q f x z := by
  have hq0 : q.map ofRealHom ≠ 0 := (hq.map ofRealHom).ne_zero
  simp only [auxiliaryProduct, Polynomial.map_mul, Polynomial.map_pow, map_X,
    roots_mul (mul_ne_zero (pow_ne_zero m X_ne_zero) hq0), roots_X_pow,
    Multiset.map_add, Multiset.prod_add, Multiset.map_nsmul, Multiset.map_singleton,
    Multiset.prod_nsmul, Multiset.prod_singleton, zero_mul, sub_zero]

/-- At a real center the zero auxiliary factors scale each coefficient by
a power of the real central value. -/
theorem auxiliaryCoefficient_X_pow_mul {f : ℂ → ℂ}
    (hc : ∀ z, f (conj z) = conj (f z)) {q : ℝ[X]} (hq : q.Monic)
    (m : ℕ) (x : ℝ) (k : ℕ) :
    auxiliaryCoefficient (X ^ m * q) f x k = (f x).re ^ m * auxiliaryCoefficient q f x k := by
  have hr : ((f x).re : ℂ) = f x := by
    apply conj_eq_iff_re.mp
    simpa only [conj_ofReal] using (hc x).symm
  have heq : auxiliaryProduct (X ^ m * q) f x =
      (fun z ↦ f x ^ m * auxiliaryProduct q f x z) := by
    funext z
    exact auxiliaryProduct_X_pow_mul hq m f x z
  rw [auxiliaryCoefficient, heq, iteratedDeriv_const_mul_field, ← hr, ← ofReal_pow,
    re_ofReal_mul]
  simp only [auxiliaryCoefficient, mul_div_assoc, ofReal_re]

/-- Removing an even origin factor preserves the full auxiliary
inequalities, including at centers where the entire function vanishes. -/
theorem auxiliaryCoefficient_nonneg_of_X_pow_mul {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hc : ∀ z, f (conj z) = conj (f z)) (hne : f ≠ 0)
    {q : ℝ[X]} (hq : q.Monic) {m : ℕ} (hm : Even m)
    (h : ∀ x k, 0 ≤ auxiliaryCoefficient (X ^ m * q) f x k) (x : ℝ) (k : ℕ) :
    0 ≤ auxiliaryCoefficient q f x k := by
  have hgood (y : ℝ) (hy : f y ≠ 0) : 0 ≤ auxiliaryCoefficient q f y k := by
    have hr : (f y).re ≠ 0 := by
      intro hr0
      have hr : ((f y).re : ℂ) = f y :=
        conj_eq_iff_re.mp (by simpa only [conj_ofReal] using (hc y).symm)
      exact hy (by rw [← hr, hr0, ofReal_zero])
    have hh := h y k
    rw [auxiliaryCoefficient_X_pow_mul hc hq] at hh
    exact nonneg_of_mul_nonneg_right hh (hm.pow_pos hr)
  have he := (hf.eventually_ofReal_ne_zero hne x).mono fun y hy ↦ hgood y hy
  have ht : Tendsto (fun y : ℝ ↦ auxiliaryCoefficient q f y k) (𝓝[≠] x)
      (𝓝 (auxiliaryCoefficient q f x k)) :=
    (continuous_auxiliaryCoefficient hf q k).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  exact ge_of_tendsto ht he

end RealRooted
