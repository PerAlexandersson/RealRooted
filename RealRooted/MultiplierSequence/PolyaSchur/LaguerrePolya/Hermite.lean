module

public import RealRooted.Hermite.Jensen
public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Jensen
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Derivative
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.HeatFlow
import RealRooted.Mathlib.Algebra.Polynomial.Reverse
import RealRooted.Mathlib.Analysis.Calculus.IteratedDeriv.Star

/-!
# A Hermite form of Jensen's criterion

All Hermite Jensen polynomials of a real entire function `f` split exactly when
`f(z) exp(-z²)` belongs to the Laguerre–Pólya class. In particular, membership
of `f` itself implies splitting. The converse concerns the Gaussian product.
-/

public section

open Polynomial Complex
open scoped ComplexConjugate

namespace RealRooted

/-- A Hermite form of Jensen's criterion, with the Gaussian factor explicit. -/
theorem isLaguerrePolya_mul_exp_neg_sq_iff
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hconj : ∀ z, f (conj z) = conj (f z)) :
    IsLaguerrePolya (fun z => f z * exp (-z ^ 2)) ↔
      ∀ d, (hermiteJensenPolynomial d (fun k => (iteratedDeriv k f 0).re)).Splits := by
  let F : ℂ → ℂ := fun z => f z * exp (-z ^ 2)
  have hF : Differentiable ℂ F := hf.mul (by fun_prop)
  have hFc (z : ℂ) : F (conj z) = conj (F z) := by
    simp only [F, hconj, map_mul, ← exp_conj, map_neg, map_pow]
  have hg (k : ℕ) := (ofReal_re_iteratedDeriv_zero hconj k).symm
  have hb (k : ℕ) := (ofReal_re_iteratedDeriv_zero hFc k).symm
  change IsLaguerrePolya F ↔ _
  rw [isLaguerrePolya_iff_jensenPolynomial_splits hF hb]
  apply forall_congr'
  intro d
  rw [hermiteJensenPolynomial_eq_reflect_jensenPolynomial hf hg hb]
  rw [← splits_iff_comp_splits_of_natDegree_eq_one
    (show (C (2 : ℝ) * X).natDegree = 1 by simp)]
  exact (splits_reflect_iff (natDegree_jensenPolynomial_le d _)).symm

/-- Hermite Jensen polynomials of a Laguerre–Pólya function split over the reals. -/
theorem IsLaguerrePolya.hermiteJensenPolynomial_splits {f : ℂ → ℂ}
    (hf : IsLaguerrePolya f) (d : ℕ) :
    (hermiteJensenPolynomial d (fun k => (iteratedDeriv k f 0).re)).Splits := by
  apply (isLaguerrePolya_mul_exp_neg_sq_iff hf.differentiable hf.conj).mp ?_ d
  have h := hf.mul (isLaguerrePolya_exp_neg_mul_sq (a := 1) (by norm_num))
  simpa only [Pi.mul_def, ofReal_one, neg_one_mul] using h

end RealRooted
