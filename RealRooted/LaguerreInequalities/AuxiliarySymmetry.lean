module

public import RealRooted.LaguerreInequalities.AuxiliaryProduct
import RealRooted.Mathlib.Algebra.Polynomial.EvenCoefficients
import RealRooted.Mathlib.Analysis.Calculus.IteratedDeriv.Star
import RealRooted.Mathlib.Analysis.Complex.TranslateProductContinuity
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Analysis.Complex.Polynomial.Basic
import RealRooted.Mathlib.Analysis.Complex.Polynomial.JensenDisks

/-!
# Reality, symmetry and continuity of auxiliary coefficients
-/

public section

open Complex Polynomial
open scoped ComplexConjugate

namespace RealRooted

/-- A real auxiliary preserves conjugation compatibility of its translated product. -/
theorem auxiliaryProduct_conj {f : ℂ → ℂ}
    (hf : ∀ z, f (conj z) = conj (f z)) (g : ℝ[X]) (x : ℝ) (z : ℂ) :
    auxiliaryProduct g f x (conj z) = conj (auxiliaryProduct g f x z) := by
  have h := congrArg
    (fun s : Multiset ℂ ↦ (s.map fun r ↦ f ((x : ℂ) - r * conj z)).prod)
    (map_conj_roots_map_ofReal g)
  have hm : algebraMap ℝ ℂ = ofRealHom := by
    ext r
    simp
  rw [hm] at h
  have harg (r : ℂ) : (x : ℂ) - conj r * conj z = conj ((x : ℂ) - r * z) := by simp
  simp only [Multiset.map_map, Function.comp_apply] at h
  simp_rw [harg, hf] at h
  simpa only [auxiliaryProduct, map_multiset_prod, Multiset.map_map,
    Function.comp_apply] using h.symm

/-- An even auxiliary gives an even translated product. -/
theorem auxiliaryProduct_neg {g : ℝ[X]}
    (he : ∀ k, Odd k → g.coeff k = 0) (f : ℂ → ℂ) (x : ℝ) (z : ℂ) :
    auxiliaryProduct g f x (-z) = auxiliaryProduct g f x z := by
  have hm : (g.map ofRealHom).comp (-X) = g.map ofRealHom := by
    simpa only [Polynomial.map_comp, Polynomial.map_neg, map_X] using
      congrArg (fun p : ℝ[X] ↦ p.map ofRealHom)
        (comp_neg_X_eq_self_of_odd_coeff_eq_zero he)
  have hr : (g.map ofRealHom).roots.map (fun r ↦ -r) = (g.map ofRealHom).roots := by
    rw [← roots_comp_neg_X, hm]
  have h := congrArg
    (fun s : Multiset ℂ ↦ (s.map fun r ↦ f ((x : ℂ) - r * z)).prod) hr
  simpa only [auxiliaryProduct, Multiset.map_map, Function.comp_apply, neg_mul,
    mul_neg, sub_neg_eq_add] using h

/-- Every Taylor coefficient of a conjugation-compatible auxiliary product is real. -/
theorem ofReal_auxiliaryCoefficient {f : ℂ → ℂ}
    (hf : ∀ z, f (conj z) = conj (f z)) (g : ℝ[X]) (x : ℝ) (k : ℕ) :
    (auxiliaryCoefficient g f x k : ℂ) =
      iteratedDeriv k (auxiliaryProduct g f x) 0 / k.factorial := by
  rw [auxiliaryCoefficient, ofReal_div, ofReal_natCast,
    ofReal_re_iteratedDeriv_zero (auxiliaryProduct_conj hf g x)]

/-- Auxiliary Taylor coefficients of an entire function are continuous in
the real center, including at zeros of the function. -/
theorem continuous_auxiliaryCoefficient {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (g : ℝ[X]) (k : ℕ) :
    Continuous (fun x : ℝ ↦ auxiliaryCoefficient g f x k) := by
  exact (continuous_re.comp
    ((continuous_iteratedDeriv_translateProduct hf (g.map ofRealHom).roots k).comp
      continuous_ofReal)).div_const _

end RealRooted
