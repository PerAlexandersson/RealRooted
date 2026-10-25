module

public import RealRooted.CombinatorialExamples.BigDescentsOddBinom
public import RealRooted.ThreeTermRecurrence.HalfGrowth

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

@[expose] public section

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
    Polynomial.coeff_one_sub_X_pow]
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
  simpa only [Real.cos_neg, Real.sin_neg, Real.tan_neg, Complex.ofReal_neg, neg_mul, mul_neg,
    sub_eq_add_neg] using one_add_I_mul_tan_eq (-theta) (by
      simpa only [Real.cos_neg] using hcos)

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

lemma evenBinomPolyReal_recurrence (n : ℕ) :
    evenBinomPolyReal (n + 2) =
      C 2 * evenBinomPolyReal (n + 1) +
        (X - 1) * evenBinomPolyReal n := by
  ext k
  rw [coeff_evenBinomPolyReal, coeff_add, coeff_C_mul]
  rw [show (X - 1) * evenBinomPolyReal n =
      X * evenBinomPolyReal n - evenBinomPolyReal n by ring]
  rw [coeff_sub, coeff_evenBinomPolyReal]
  cases k with
  | zero => norm_num [coeff_evenBinomPolyReal]
  | succ k =>
      rw [coeff_X_mul, coeff_evenBinomPolyReal, coeff_evenBinomPolyReal]
      rw [show 2 * (k + 1) = (2 * k + 1) + 1 by lia,
        Nat.choose_succ_succ, Nat.choose_succ_succ, Nat.choose_succ_succ]
      grind

lemma evenBinomPolyReal_natDegree (n : ℕ) :
    (evenBinomPolyReal n).natDegree = n / 2 := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · rw [natDegree_le_iff_coeff_eq_zero]
    intro k hk
    rw [coeff_evenBinomPolyReal, Nat.choose_eq_zero_of_lt]
    · norm_num
    · lia
  · rw [coeff_evenBinomPolyReal]
    exact Nat.cast_choose_ne_zero (R := ℝ) (by lia)

lemma evenBinomPolyReal_leadingCoeff_pos (n : ℕ) :
    0 < (evenBinomPolyReal n).leadingCoeff := by
  rw [leadingCoeff, evenBinomPolyReal_natDegree, coeff_evenBinomPolyReal]
  exact_mod_cast Nat.choose_pos (by lia : 2 * (n / 2) ≤ n)

/-- The polynomial with coefficients `choose n (2 * k)` is nonzero and has
only real roots. -/
theorem evenBinomPolyReal_ne_zero_and_splits (n : ℕ) :
    evenBinomPolyReal n ≠ 0 ∧ (evenBinomPolyReal n).Splits := by
  have hzero : evenBinomPolyReal 0 = 1 := by
    simp [evenBinomPolyReal]
  have hone : evenBinomPolyReal 1 = 1 := by
    simp [evenBinomPolyReal]
  have htwo : evenBinomPolyReal 2 = 1 + X := by
    norm_num [evenBinomPolyReal, Finset.sum_range_succ, Nat.choose]
  have hthree : evenBinomPolyReal 3 = 1 + 3 * X := by
    norm_num [evenBinomPolyReal, Finset.sum_range_succ, Nat.choose]
  exact (RealRooted.threeTermHalf_ne_zero_and_splits
    (P := evenBinomPolyReal) (a := fun _ => C 2)
    (b := fun _ => X - 1) (D₀ := 0) (e := 0)
    evenBinomPolyReal_recurrence
    (fun _ => by simp) (fun _ => by simp) (fun _ r => by
      simp only [eval_sub, eval_X, eval_one]
      nlinarith [sq_nonneg (r - 1)])
    (fun m => by simp [evenBinomPolyReal_natDegree])
    evenBinomPolyReal_leadingCoeff_pos
    (by rw [hzero, htwo]; exact RealRooted.interlaces_one_linear (by
      compute_degree
      norm_num))
    (by rw [hone, hthree]; exact RealRooted.interlaces_one_linear (by
      compute_degree
      norm_num)) n)

theorem evenBinomPolyReal_splits (n : ℕ) :
    (evenBinomPolyReal n).Splits :=
  (evenBinomPolyReal_ne_zero_and_splits n).2

end BigDescents
