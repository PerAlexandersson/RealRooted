import RealRooted.CombinatorialExamples.BigDescentsOddBinom

/-!
# Even binomial polynomials

The even companion of `BigDescents.oddBinomPolyReal`:

```text
evenBinomPolyReal n = sum_k C(n, 2k) X^k,
2 · evenBinomPolyReal n (y^2) = (1 + y)^n + (1 - y)^n,
evenBinomPolyReal n (-tan^2 θ) · cos^n θ = cos (n θ).
```

Ported from `real-rooted-oeis-proofs` (`EvenBinomial`).
-/

open Polynomial
open scoped BigOperators

noncomputable section

namespace BigDescents

/-- `sum_k C(n, 2k) X^(2k)`, the even part of `(1 + X)^n`. -/
def evenBinomAuxReal (n : ℕ) : ℝ[X] :=
  ∑ k ∈ Finset.range (n / 2 + 1),
    C ((Nat.choose n (2 * k) : ℝ)) * X ^ (2 * k)

/-- `sum_k C(n, 2k) X^k`. -/
def evenBinomPolyReal (n : ℕ) : ℝ[X] :=
  ∑ k ∈ Finset.range (n / 2 + 1),
    C ((Nat.choose n (2 * k) : ℝ)) * X ^ k

lemma coeff_evenBinomAuxReal_even (n k : ℕ) :
    (evenBinomAuxReal n).coeff (2 * k) =
      (n.choose (2 * k) : ℝ) := by
  simp only [evenBinomAuxReal, map_natCast, finsetSum_coeff, coeff_natCast_mul,
    coeff_X_pow, mul_eq_mul_left_iff, OfNat.ofNat_ne_zero, or_false, mul_ite,
    mul_one, mul_zero, Finset.sum_ite_eq, ite_eq_left_iff]
  intro h
  rw [Nat.choose_eq_zero_of_lt] <;> grind

lemma coeff_evenBinomAuxReal_odd (n k : ℕ) :
    (evenBinomAuxReal n).coeff (2 * k + 1) = 0 := by
  simp only [evenBinomAuxReal, finsetSum_coeff, coeff_C_mul, coeff_X_pow,
    mul_ite, mul_one, mul_zero]
  apply Finset.sum_eq_zero
  grind

theorem evenBinomAuxReal_identity (n : ℕ) :
    (2 : ℝ[X]) * evenBinomAuxReal n =
      ((1 : ℝ[X]) + X) ^ n + ((1 : ℝ[X]) - X) ^ n := by
  ext m
  change (C (2 : ℝ) * evenBinomAuxReal n).coeff m = _
  rw [coeff_add, coeff_C_mul, Polynomial.coeff_one_add_X_pow,
    coeff_one_sub_X_pow]
  rcases Nat.even_or_odd m with hm | hm
  · rcases hm with ⟨k, rfl⟩
    rw [show k + k = 2 * k by lia]
    rw [coeff_evenBinomAuxReal_even]
    have heven : Even (2 * k) := ⟨k, by lia⟩
    rw [heven.neg_one_pow]
    ring
  · rcases hm with ⟨k, rfl⟩
    rw [coeff_evenBinomAuxReal_odd]
    have hodd : Odd (2 * k + 1) := ⟨k, rfl⟩
    rw [hodd.neg_one_pow]
    ring

lemma evenBinomPolyReal_eval_sq_eq_aux (n : ℕ) (y : ℝ) :
    (evenBinomPolyReal n).eval (y ^ 2) = (evenBinomAuxReal n).eval y := by
  rw [evenBinomPolyReal, evenBinomAuxReal,
    Polynomial.eval_finsetSum, Polynomial.eval_finsetSum]
  simp [pow_mul]

lemma coeff_evenBinomPolyReal (n k : ℕ) :
    (evenBinomPolyReal n).coeff k = (n.choose (2 * k) : ℝ) := by
  simp only [evenBinomPolyReal, map_natCast, finsetSum_coeff, coeff_natCast_mul,
    coeff_X_pow, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
    Finset.mem_range, ite_eq_left_iff]
  intro h
  rw [Nat.choose_eq_zero_of_lt] <;> grind

lemma map_evenBinomAuxReal (n : ℕ) :
    (evenBinomAuxReal n).map (algebraMap ℝ ℂ) =
      ∑ k ∈ Finset.range (n / 2 + 1),
        C ((Nat.choose n (2 * k) : ℂ)) * X ^ (2 * k) := by
  simp [evenBinomAuxReal, Polynomial.map_sum]

lemma map_evenBinomPolyReal (n : ℕ) :
    (evenBinomPolyReal n).map (algebraMap ℝ ℂ) =
      ∑ k ∈ Finset.range (n / 2 + 1),
        C ((Nat.choose n (2 * k) : ℂ)) * X ^ k := by
  simp [evenBinomPolyReal, Polynomial.map_sum]

lemma evenBinom_eval_sq_eq_aux (n : ℕ) (y : ℂ) :
    ((evenBinomPolyReal n).map (algebraMap ℝ ℂ)).eval (y ^ 2) =
      ((evenBinomAuxReal n).map (algebraMap ℝ ℂ)).eval y := by
  rw [map_evenBinomPolyReal, map_evenBinomAuxReal,
    Polynomial.eval_finsetSum, Polynomial.eval_finsetSum]
  simp [pow_mul]

lemma evenBinom_eval_sq_identity (n : ℕ) (y : ℂ) :
    (2 : ℂ) *
        ((evenBinomPolyReal n).map (algebraMap ℝ ℂ)).eval (y ^ 2) =
      (1 + y) ^ n + (1 - y) ^ n := by
  have h := congrArg (Polynomial.map (algebraMap ℝ ℂ))
    (evenBinomAuxReal_identity n)
  have heval := congrArg (fun p : ℂ[X] ↦ p.eval y) h
  simp at heval
  have hsq := evenBinom_eval_sq_eq_aux n y
  simp_all

lemma one_add_I_mul_tan_eq (theta : ℝ) (hcos : Real.cos theta ≠ 0) :
    (1 : ℂ) + Complex.I * (Real.tan theta : ℂ) =
      ((Real.cos theta : ℂ) + (Real.sin theta : ℂ) * Complex.I) /
        (Real.cos theta : ℂ) := by
  rw [Real.tan_eq_sin_div_cos]
  rw [Complex.ofReal_div]
  have hcosC : (Real.cos theta : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hcos
  grind

lemma one_sub_I_mul_tan_eq (theta : ℝ) (hcos : Real.cos theta ≠ 0) :
    (1 : ℂ) - Complex.I * (Real.tan theta : ℂ) =
      ((Real.cos theta : ℂ) - (Real.sin theta : ℂ) * Complex.I) /
        (Real.cos theta : ℂ) := by
  rw [Real.tan_eq_sin_div_cos]
  rw [Complex.ofReal_div]
  have hcosC : (Real.cos theta : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hcos
  grind

lemma evenBinomPolyReal_eval_neg_tan_sq_mul_cos_pow
    (n : ℕ) (theta : ℝ) (hcos : Real.cos theta ≠ 0) :
    (evenBinomPolyReal n).eval (-(Real.tan theta) ^ 2) *
        (Real.cos theta) ^ n =
      Real.cos ((n : ℝ) * theta) := by
  have hidentity := evenBinom_eval_sq_identity n
    (Complex.I * (Real.tan theta : ℂ))
  have hsq :
      (Complex.I * (Real.tan theta : ℂ)) ^ 2 =
        ((-(Real.tan theta) ^ 2 : ℝ) : ℂ) := by
    push_cast
    rw [mul_pow]
    simp
  rw [hsq] at hidentity
  have hevalcast :
      ((evenBinomPolyReal n).map (algebraMap ℝ ℂ)).eval
          ((-(Real.tan theta) ^ 2 : ℝ) : ℂ) =
        (((evenBinomPolyReal n).eval (-(Real.tan theta) ^ 2) : ℝ) : ℂ) := by
    exact Polynomial.eval_map_apply (p := evenBinomPolyReal n)
      (algebraMap ℝ ℂ) (-(Real.tan theta) ^ 2)
  rw [hevalcast] at hidentity
  rw [one_add_I_mul_tan_eq theta hcos,
    one_sub_I_mul_tan_eq theta hcos] at hidentity
  rw [div_pow, div_pow] at hidentity
  have hplus := Complex.cos_add_sin_mul_I_pow n (theta : ℂ)
  have hminus := Complex.cos_add_sin_mul_I_pow n (-(theta : ℂ))
  have hplus' :
      ((Real.cos theta : ℂ) + (Real.sin theta : ℂ) * Complex.I) ^ n =
        (Real.cos ((n : ℝ) * theta) : ℂ) +
          (Real.sin ((n : ℝ) * theta) : ℂ) * Complex.I := by
    simpa using hplus
  have hminus' :
      ((Real.cos theta : ℂ) - (Real.sin theta : ℂ) * Complex.I) ^ n =
        (Real.cos ((n : ℝ) * theta) : ℂ) -
          (Real.sin ((n : ℝ) * theta) : ℂ) * Complex.I := by
    simpa [Complex.cos_neg, Complex.sin_neg, sub_eq_add_neg] using hminus
  rw [hplus', hminus'] at hidentity
  have hcosC : (Real.cos theta : ℂ) ^ n ≠ 0 :=
    pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hcos)
  have hcomplex :
      ((((evenBinomPolyReal n).eval (-(Real.tan theta) ^ 2) : ℝ) : ℂ) *
          ((Real.cos theta : ℂ) ^ n)) =
        (Real.cos ((n : ℝ) * theta) : ℂ) := by grind
  exact_mod_cast hcomplex

end BigDescents
