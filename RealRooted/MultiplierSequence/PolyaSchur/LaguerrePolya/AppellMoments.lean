module

public import RealRooted.BasisTransform.LimitingAppellMoments
public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.TypeI
public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Operator
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.HeatFlow
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Derivative
import RealRooted.Mathlib.Analysis.Calculus.IteratedDeriv.CompPowCoefficient

/-!
# Hankel positivity of logarithmic coefficients of Type-I entire functions

The normalized ordinary Taylor coefficients give real-rooted limiting Appell
rows through the substitution `f(-z²)`. Newton sums of these rows yield positive
semidefinite Hankel matrices of the signed logarithmic coefficients, including
both matrices in the Stieltjes moment criterion.

These are the Hankel positivity consequences of the forward direction of
A. D. Sokal, *When does a hypergeometric function pFq belong to the
Laguerre–Pólya class LP+?*, Proposition 6,
https://doi.org/10.1016/j.jmaa.2022.126432. A representing measure and the converse
criterion require additional arguments.
-/

public section

open Polynomial Finset Complex

namespace RealRooted

private theorem taylor_comp_neg_sq (f : ℂ → ℂ) (hf : Differentiable ℂ f) (k : ℕ) :
    (iteratedDeriv k (fun z => f (-z ^ 2)) 0 / k.factorial).re =
      if 2 ∣ k then (-1 : ℝ) ^ (k / 2) *
        ((iteratedDeriv (k / 2) f 0).re / (k / 2).factorial) else 0 := by
  have ha : AnalyticAt ℂ (fun z => f (-z)) 0 :=
    (hf.comp (by fun_prop : Differentiable ℂ (fun z : ℂ => -z))).analyticAt 0
  have h := iteratedDeriv_comp_pow_zero_eq ha (by norm_num : 0 < 2) k
  change iteratedDeriv k (fun z => f (-(z ^ 2))) 0 = _ at h
  rw [h, iteratedDeriv_comp_neg]
  have hk : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
  by_cases hd : 2 ∣ k
  · simp only [ite_eq_left hd, neg_zero, smul_eq_mul]
    rw [mul_div_cancel_left₀ _ hk]
    have hs : (-1 : ℂ) ^ (k / 2) = Complex.ofReal ((-1 : ℝ) ^ (k / 2)) := by simp
    rw [hs]
    simp only [mul_div_assoc, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero,
      div_natCast_re]
  · simp [hd]

private theorem sum_even_range {M : Type*} [AddCommMonoid M]
    (F : ℕ → M) (N : ℕ) :
    (∑ k ∈ range (N + 1), if 2 ∣ k then F k else 0) =
      ∑ j ∈ range (N / 2 + 1), F (2 * j) := by
  classical
  rw [← sum_filter]
  symm
  apply sum_bij (fun j _ => 2 * j)
  · intro j hj
    simp only [mem_filter, mem_range]
    have hj' := mem_range.mp hj
    constructor
    · lia
    · exact dvd_mul_right 2 j
  · intro a ha b hb hab
    lia
  · intro k hk
    obtain ⟨hkr, hkd⟩ := mem_filter.mp hk
    refine ⟨k / 2, mem_range.mpr ?_, ?_⟩
    · have hle := mem_range.mp hkr
      lia
    · exact Nat.mul_div_cancel' hkd
  · intro j hj
    rfl

/-- The even square-substitution operator produces the limiting Appell row. -/
theorem taylorDifferentialOperator_comp_neg_sq_X_pow
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) (N : ℕ) :
    taylorDifferentialOperator (fun z => f (-z ^ 2)) (X ^ N) =
      limitingAppellPolynomial (fun j => (iteratedDeriv j f 0).re / j.factorial) N := by
  rw [taylorDifferentialOperator, natDegree_X_pow]
  simp only [taylor_comp_neg_sq f hf, apply_ite C, map_zero, ite_mul, zero_mul]
  rw [sum_even_range]
  ext k
  rw [finsetSum_coeff, coeff_limitingAppellPolynomial]
  apply sum_congr rfl
  intro j hj
  rw [Nat.mul_div_cancel_left j (by norm_num : 0 < 2),
    iterate_derivative_X_pow_eq_C_mul]
  simp only [← mul_assoc, ← C_mul]
  rw [coeff_C_mul_X_pow]
  split_ifs <;> simp_all
  ring

/-- Scalar multiplication of the coefficient sequence scales each Appell row. -/
private theorem limitingAppellPolynomial_const_mul (c : ℝ) (d : ℕ → ℝ) (N : ℕ) :
    limitingAppellPolynomial (fun j => c * d j) N =
      C c * limitingAppellPolynomial d N := by
  ext k
  simp only [coeff_C_mul, coeff_limitingAppellPolynomial]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  split_ifs <;> ring

/-- Type-I entire functions give real-rooted limiting Appell rows. -/
theorem IsLaguerrePolyaTypeI.splits_limitingAppellPolynomial
    {f : ℂ → ℂ} (hf : IsLaguerrePolyaTypeI f) (N : ℕ) :
    (limitingAppellPolynomial
      (fun j => (iteratedDeriv j f 0).re / j.factorial) N).Splits := by
  have hg : IsLaguerrePolya (fun z => f (-z ^ 2)) := by
    simpa using hf.isLaguerrePolya_comp_neg_mul_sq (by norm_num : (0 : ℝ) ≤ 1)
  rw [← taylorDifferentialOperator_comp_neg_sq_X_pow hf.toLaguerrePolya.differentiable]
  exact hg.taylorDifferentialOperator_splits ((Splits.X).pow N)

/-- Normalizing the constant term preserves the splitting of the Appell rows. -/
private theorem splits_normalized_limitingAppellPolynomial
    {f : ℂ → ℂ} (hf : IsLaguerrePolyaTypeI f) (N : ℕ) :
    (limitingAppellPolynomial
      (fun j => (iteratedDeriv j f 0).re / (j.factorial * (f 0).re)) N).Splits := by
  have heq : (fun j => (iteratedDeriv j f 0).re / (j.factorial * (f 0).re)) =
      fun j => (f 0).re⁻¹ * ((iteratedDeriv j f 0).re / j.factorial) := by
    funext j
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [heq, limitingAppellPolynomial_const_mul]
  exact (Splits.C _).mul (hf.splits_limitingAppellPolynomial N)

/-- Every shifted Hankel matrix of the normalized Newton moments is positive
semidefinite for a Type-I entire function with nonzero constant term. -/
theorem IsLaguerrePolyaTypeI.posSemidef_limitingAppellMoment
    {f : ℂ → ℂ} (hf : IsLaguerrePolyaTypeI f) (h0 : (f 0).re ≠ 0) (n r : ℕ) :
    Matrix.PosSemidef (fun i j : Fin n =>
      limitingAppellMoment
        (fun k => (iteratedDeriv k f 0).re / (k.factorial * (f 0).re))
        (i.val + j.val + (r + 1))) :=
  RealRooted.posSemidef_limitingAppellMoment (by simp [h0])
    (splits_normalized_limitingAppellPolynomial hf) n r

/-- Every shifted Hankel matrix of the normalized signed logarithmic
coefficients is positive semidefinite. -/
theorem IsLaguerrePolyaTypeI.posSemidef_signed_coeff_logOf
    {f : ℂ → ℂ} (hf : IsLaguerrePolyaTypeI f) (h0 : (f 0).re ≠ 0) (n r : ℕ) :
    Matrix.PosSemidef (fun i j : Fin n =>
      let k := i.val + j.val + (r + 1)
      (-1 : ℝ) ^ (k + 1) * k * PowerSeries.coeff k (PowerSeries.logOf
        (PowerSeries.mk
          (fun j => (iteratedDeriv j f 0).re / (j.factorial * (f 0).re))))) :=
  posSemidef_signed_coeff_logOf_limitingAppell (by simp [h0])
    (splits_normalized_limitingAppellPolynomial hf) n r

end RealRooted
