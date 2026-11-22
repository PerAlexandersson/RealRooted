module

public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya
public import RealRooted.Mathlib.Analysis.Complex.CanonicalProduct.GenusOne
public import RealRooted.MultiplierSequence.JensenProduct
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.GenusOne
import RealRooted.MultiplierSequence.JensenProductExpansion
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.JensenProduct
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Derivative
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Zeros
import RealRooted.Mathlib.Algebra.Polynomial.Reverse

/-!
# The full genus-one-star auxiliary Jensen criterion

O'Sullivan (2021), Theorem 3.5: a real function of genus `1*` has only real zeros
if and only if the Jensen polynomials of its product with a fixed nonzero
Laguerre--Pólya function split. Both factors may vanish at the origin. The
ordinary and reciprocal polynomial sums are given explicitly, including degree
loss in the auxiliary. Degree zero is harmless and included in the indexed form.
-/

public section

open Complex Polynomial
open scoped ComplexConjugate

namespace RealRooted

/-- A nonzero Laguerre--Pólya auxiliary detects real zeros of every real
genus-one-star function, with no restriction on either origin multiplicity. -/
theorem real_zeros_iff_isLaguerrePolya_mul {f g : ℂ → ℂ}
    (hf : HasGenusOneStar f) (hc : ∀ z, f (conj z) = conj (f z))
    (hg : IsLaguerrePolya g) (hg0 : g ≠ 0) :
    (∀ z, f z = 0 → z.im = 0) ↔ IsLaguerrePolya (f * g) := by
  constructor
  · exact fun hz => (isLaguerrePolya_of_hasGenusOneStar hf hc hz).mul hg
  · intro hfg
    have hfg0 : f * g ≠ 0 := by
      intro hzero
      have hfa : AnalyticOnNhd ℂ f Set.univ := fun z _ => hf.differentiable.analyticAt z
      rcases hfa.eq_zero_or_eq_zero_of_mul_eq_zero hg.analyticOnNhd
        (fun z _ => congrFun hzero z) isPreconnected_univ with h | h
      · exact hf.ne_zero (funext fun z => h z (Set.mem_univ _))
      · exact hg0 (funext fun z => h z (Set.mem_univ _))
    exact fun z hz => hfg.im_eq_zero_of_eq_zero hfg0 (by simp [Pi.mul_apply, hz])

/-- Multiplication by a fixed nonzero Laguerre--Pólya function detects class
membership for every real function of genus one star. -/
theorem isLaguerrePolya_mul_iff_of_hasGenusOneStar {f g : ℂ → ℂ}
    (hf : HasGenusOneStar f) (hc : ∀ z, f (conj z) = conj (f z))
    (hg : IsLaguerrePolya g) (hg0 : g ≠ 0) :
    IsLaguerrePolya (f * g) ↔ IsLaguerrePolya f := by
  refine ⟨fun h => isLaguerrePolya_of_hasGenusOneStar hf hc
    ((real_zeros_iff_isLaguerrePolya_mul hf hc hg hg0).mpr h), fun h => h.mul hg⟩

/-- The Jensen-product criterion for real zeros in the full genus-one-star class. -/
theorem real_zeros_iff_jensenProductPolynomial_splits {f g : ℂ → ℂ}
    {gamma delta : ℕ → ℝ} (hf : HasGenusOneStar f)
    (hc : ∀ z, f (conj z) = conj (f z)) (hg : IsLaguerrePolya g) (hg0 : g ≠ 0)
    (hgamma : ∀ k, iteratedDeriv k f 0 = (gamma k : ℂ))
    (hdelta : ∀ k, iteratedDeriv k g 0 = (delta k : ℂ)) :
    (∀ z, f z = 0 → z.im = 0) ↔
      ∀ d, (jensenProductPolynomial d gamma delta).Splits :=
  (real_zeros_iff_isLaguerrePolya_mul hf hc hg hg0).trans
    (isLaguerrePolya_mul_iff_jensenProductPolynomial_splits
      hf.differentiable hg.differentiable hgamma hdelta)

private theorem forall_jensenProduct_splits_iff (gamma delta : ℕ → ℝ) :
    (∀ d, (jensenProductPolynomial d gamma delta).Splits) ↔
      ∀ d, d ≠ 0 → (jensenProductPolynomial d gamma delta).Splits := by
  refine ⟨fun h d _ => h d, fun h d => ?_⟩
  by_cases hd : d = 0
  · subst d
    exact Splits.of_natDegree_le_one ((natDegree_jensenProductPolynomial_le 0 _ _).trans
      (by norm_num))
  · exact h d hd

/-- O'Sullivan's Theorem 3.5 in ordinary Jensen-sum form, valid for a fixed
nonzero auxiliary even when its constant coefficient vanishes. -/
theorem real_zeros_iff_jensen_sum_splits {f g : ℂ → ℂ}
    {gamma delta : ℕ → ℝ} (hf : HasGenusOneStar f)
    (hc : ∀ z, f (conj z) = conj (f z)) (hg : IsLaguerrePolya g) (hg0 : g ≠ 0)
    (hgamma : ∀ k, iteratedDeriv k f 0 = (gamma k : ℂ))
    (hdelta : ∀ k, iteratedDeriv k g 0 = (delta k : ℂ)) :
    (∀ z, f z = 0 → z.im = 0) ↔ ∀ d, d ≠ 0 →
      (∑ j ∈ Finset.range (d + 1), C ((d.choose j : ℝ) * gamma j) *
        (X ^ j * jensenPolynomial (d - j) delta)).Splits := by
  simpa only [← jensenProductPolynomial_eq_sum] using
    (real_zeros_iff_jensenProductPolynomial_splits hf hc hg hg0 hgamma hdelta).trans
      (forall_jensenProduct_splits_iff gamma delta)

/-- O'Sullivan's Theorem 3.5 in reciprocal Jensen-sum form, retaining all zero
coefficients and origin factors. -/
theorem real_zeros_iff_reciprocal_jensen_sum_splits {f g : ℂ → ℂ}
    {gamma delta : ℕ → ℝ} (hf : HasGenusOneStar f)
    (hc : ∀ z, f (conj z) = conj (f z)) (hg : IsLaguerrePolya g) (hg0 : g ≠ 0)
    (hgamma : ∀ k, iteratedDeriv k f 0 = (gamma k : ℂ))
    (hdelta : ∀ k, iteratedDeriv k g 0 = (delta k : ℂ)) :
    (∀ z, f z = 0 → z.im = 0) ↔ ∀ d, d ≠ 0 →
      (∑ j ∈ Finset.range (d + 1), C ((d.choose j : ℝ) * gamma j) *
        reflect (d - j) (jensenPolynomial (d - j) delta)).Splits := by
  simp only [← reflect_jensenProductPolynomial_eq_sum,
    splits_reflect_iff (natDegree_jensenProductPolynomial_le _ _ _)]
  exact (real_zeros_iff_jensenProductPolynomial_splits hf hc hg hg0 hgamma hdelta).trans
    (forall_jensenProduct_splits_iff gamma delta)

end RealRooted
