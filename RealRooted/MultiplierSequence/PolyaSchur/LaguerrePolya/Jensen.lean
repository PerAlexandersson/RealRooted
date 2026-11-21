module

public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Derivative
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Operator
import RealRooted.Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Analysis.Complex.TaylorSeries

/-!
# Jensen's criterion for the Laguerre–Pólya class

An entire function with real Taylor coefficients belongs to the Laguerre–Pólya class
exactly when all its Jensen polynomials split over the reals. Differentiation gives the
same conclusion for every shift of the Taylor coefficient sequence.
-/

public section

open Polynomial Complex Filter Topology

namespace RealRooted

private theorem taylorDifferentialOperator_X_pow (f : ℂ → ℂ) (n : ℕ) :
    taylorDifferentialOperator f (X ^ n) =
      reflect n (jensenPolynomial n (fun k => (iteratedDeriv k f 0).re)) := by
  classical
  ext k
  simp only [taylorDifferentialOperator, natDegree_X_pow, finsetSum_coeff, coeff_C_mul,
    coeff_iterate_derivative, nsmul_eq_mul, coeff_reflect]
  by_cases hk : k ≤ n
  · rw [revAt_le hk, coeff_jensenPolynomial, ite_eq_left (Nat.sub_le _ _)]
    rw [Finset.sum_eq_single (n - k)]
    · rw [Nat.add_sub_of_le hk, coeff_X_pow_self, mul_one,
        Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul]
      simp only [div_natCast_re]
      field_simp
    · intro j _ hj
      simp [coeff_X_pow, show k + j ≠ n by lia]
    · simp
  · rw [revAt_eq_self_of_lt (lt_of_not_ge hk), coeff_jensenPolynomial, ite_eq_right hk]
    apply Finset.sum_eq_zero
    intro j _
    simp [coeff_X_pow, show k + j ≠ n by lia]

/-- Every Jensen polynomial of the Taylor data of a Laguerre–Pólya function splits. -/
theorem IsLaguerrePolya.jensenPolynomial_splits {f : ℂ → ℂ}
    (hf : IsLaguerrePolya f) (n : ℕ) :
    (jensenPolynomial n (fun k => (iteratedDeriv k f 0).re)).Splits := by
  apply (splits_reflect_iff (natDegree_jensenPolynomial_le n _)).mp
  rw [← taylorDifferentialOperator_X_pow]
  exact hf.taylorDifferentialOperator_splits (Splits.X.pow n)

/-- Every derivative of a Laguerre–Pólya function belongs to the same class. -/
theorem IsLaguerrePolya.iterate_deriv {f : ℂ → ℂ}
    (hf : IsLaguerrePolya f) (n : ℕ) : IsLaguerrePolya (iteratedDeriv n f) := by
  induction n with
  | zero => simpa using hf
  | succ n ih => simpa [iteratedDeriv_succ] using ih.deriv

/-- Jensen's theorem also applies to every shift of the Taylor data. -/
theorem IsLaguerrePolya.jensenPolynomial_shift_splits {f : ℂ → ℂ}
    (hf : IsLaguerrePolya f) (d n : ℕ) :
    (jensenPolynomial d (fun k => (iteratedDeriv (n + k) f 0).re)).Splits := by
  simpa only [iteratedDeriv_eq_iterate, ← Function.iterate_add_apply, Nat.add_comm] using
    (hf.iterate_deriv n).jensenPolynomial_splits d

/-- The Taylor data of an entire function have an absolutely summable exponential
generating series at every radius. -/
theorem summable_norm_iteratedDeriv_div_factorial {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (R : ℝ) (hR : 0 ≤ R) :
    Summable (fun k => ‖iteratedDeriv k f 0‖ * R ^ k / k.factorial) := by
  have h := (hasSum_taylorSeries_of_entire hf 0 (R : ℂ)).summable.norm
  simpa only [sub_zero, smul_eq_mul, norm_mul, norm_inv, norm_natCast, norm_pow,
    norm_real, Real.norm_eq_abs, abs_of_nonneg hR, div_eq_mul_inv, mul_comm,
    mul_left_comm, mul_assoc] using h

/-- An entire function with real Taylor data is their exponential generating function. -/
theorem eq_complexExpGeneratingFunction_of_iteratedDeriv {f : ℂ → ℂ} {gamma : ℕ → ℝ}
    (hf : Differentiable ℂ f) (hgamma : ∀ k, iteratedDeriv k f 0 = (gamma k : ℂ)) :
    f = complexExpGeneratingFunction gamma := by
  rw [complexExpGeneratingFunction_eq_tsum]
  funext z
  rw [← taylorSeries_eq_of_entire' 0 z hf]
  apply tsum_congr
  intro k
  rw [hgamma k]
  simp [div_eq_mul_inv, mul_comm]

/-- Jensen's criterion for an entire function with real Taylor coefficients. -/
theorem isLaguerrePolya_iff_jensenPolynomial_splits {f : ℂ → ℂ} {gamma : ℕ → ℝ}
    (hf : Differentiable ℂ f) (hgamma : ∀ k, iteratedDeriv k f 0 = (gamma k : ℂ)) :
    IsLaguerrePolya f ↔ ∀ n, (jensenPolynomial n gamma).Splits := by
  constructor
  · intro h n
    simpa only [hgamma, ofReal_re] using h.jensenPolynomial_splits n
  · intro h
    have hsum (R : ℝ) (hR : 0 ≤ R) :
        Summable (fun k => ‖gamma k‖ * R ^ k / k.factorial) := by
      simpa only [hgamma, norm_real] using summable_norm_iteratedDeriv_div_factorial hf R hR
    rw [eq_complexExpGeneratingFunction_of_iteratedDeriv hf hgamma,
      complexExpGeneratingFunction_eq_tsum]
    refine ⟨fun n => rescaledJensenPolynomial n gamma, fun n => Or.inr ?_,
      tendstoLocallyUniformly_eval_complex_rescaledJensenPolynomial_of_summable gamma hsum⟩
    dsimp only
    rw [rescaledJensenPolynomial_eq_jensenPolynomial_comp]
    exact (h n).comp_of_natDegree_le_one ((natDegree_C_mul_le _ _).trans (by simp))

end RealRooted
