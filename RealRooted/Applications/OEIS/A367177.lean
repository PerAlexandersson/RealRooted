module

public import RealRooted.MultiplierSequence.JensenHypergeometric
public import RealRooted.Recurrence.RowModel
public import RealRooted.Recurrence.Uniqueness

/-!
# The A367177 reciprocal double-Narayana model

The coefficient of `X^k` in row `n` is `C(n,k)^2 C(2k,k)`. This is the
degree-`n` reciprocal shift of the A318397 double-Narayana row.
-/

@[expose] public section

open RealRooted Polynomial

noncomputable section

namespace RealRooted.Applications.OEIS.A367177

/-- The reciprocal double-Narayana model for A367177. -/
def polynomial (n : ℕ) : ℝ[X] :=
  reciprocalShift n (doubleNarayanaPolynomial n)

/-- Coefficients of the A367177 model. -/
theorem coeff_polynomial (n k : ℕ) :
    (polynomial n).coeff k =
      (((n.choose k) ^ 2 * (2 * k).choose k : ℕ) : ℝ) := by
  rw [polynomial, coeff_reciprocalShift]
  rw [coeff_doubleNarayanaPolynomial]
  by_cases hk : k ≤ n
  · rw [Polynomial.revAt_le hk]
    simp only [show n - (n - k) = k by lia]
    rw [Nat.choose_symm hk]
  · have hnk : n < k := Nat.lt_of_not_ge hk
    rw [Polynomial.revAt_eq_self_of_lt hnk,
      Nat.choose_eq_zero_of_lt hnk]
    simp

/-- The A367177 model has degree `n`. -/
theorem polynomial_natDegree (n : ℕ) : (polynomial n).natDegree = n := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · exact (Polynomial.natDegree_reflect_le (N := n)
      (p := doubleNarayanaPolynomial n)).trans
      (max_le le_rfl (natDegree_doubleNarayanaPolynomial_le n))
  · rw [coeff_polynomial]
    norm_num
    exact (Nat.choose_pos (by lia : n ≤ 2 * n)).ne'

@[simp] private theorem coeff_polynomial_zero (n : ℕ) :
    (polynomial n).coeff 0 = 1 := by
  rw [coeff_polynomial]
  simp

private theorem coeff_recurrence_interior
    (n k : ℕ) (hkpos : 1 ≤ k) (hkn : k ≤ n) :
    ((n : ℝ) + 2) ^ 2 * (polynomial (n + 2)).coeff k =
      ((8 * (n : ℝ) + 10) * (k : ℝ) +
          (1 - 2 * (n : ℝ) ^ 2 - 2 * (n : ℝ))) *
        (polynomial (n + 1)).coeff k +
      (-(8 * (n : ℝ) + 10) * ((k : ℝ) - 1) +
          (12 * (n : ℝ) ^ 2 + 32 * (n : ℝ) + 22)) *
        (polynomial (n + 1)).coeff (k - 1) +
      3 * ((n : ℝ) + 1) ^ 2 *
        ((polynomial n).coeff k - 4 * (polynomial n).coeff (k - 1)) := by
  rw [coeff_polynomial, coeff_polynomial, coeff_polynomial,
    coeff_polynomial, coeff_polynomial]
  push_cast
  have hk_n1 : k ≤ n + 1 := by lia
  have hk_n2 : k ≤ n + 2 := by lia
  have hkm1_n : k - 1 ≤ n := by lia
  have hkm1_n1 : k - 1 ≤ n + 1 := by lia
  rw [Nat.cast_choose ℝ hk_n2, Nat.cast_choose ℝ hk_n1,
    Nat.cast_choose ℝ hkm1_n1, Nat.cast_choose ℝ hkn,
    Nat.cast_choose ℝ hkm1_n]
  have hk_self : k ≤ 2 * k := by lia
  have hkm1_self : k - 1 ≤ 2 * (k - 1) := by lia
  rw [Nat.cast_choose ℝ hk_self, Nat.cast_choose ℝ hkm1_self]
  have hsub1 : n + 2 - k = (n - k) + 2 := by lia
  have hsub2 : n + 1 - k = (n - k) + 1 := by lia
  have hsub3 : n + 1 - (k - 1) = (n - k) + 2 := by lia
  have hsub4 : n - (k - 1) = (n - k) + 1 := by lia
  have hsub5 : 2 * k - k = k := by lia
  have hsub6 : 2 * (k - 1) - (k - 1) = k - 1 := by lia
  rw [hsub1, hsub2, hsub3, hsub4, hsub5, hsub6]
  simp only [Nat.factorial_succ]
  push_cast
  have hfack :
      ((Nat.factorial k : ℕ) : ℝ) =
        (k : ℝ) * ((Nat.factorial (k - 1) : ℕ) : ℝ) := by
    cases k with
    | zero => lia
    | succ j => simp [Nat.factorial_succ]
  have hfac2k :
      ((Nat.factorial (2 * k) : ℕ) : ℝ) =
        (2 * (k : ℝ)) * (2 * (k : ℝ) - 1) *
          ((Nat.factorial (2 * (k - 1)) : ℕ) : ℝ) := by
    have hidx : 2 * k = 2 * (k - 1) + 2 := by lia
    rw [hidx, Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    rw [Nat.cast_sub hkpos]
    ring
  rw [hfack, hfac2k, Nat.cast_sub hkn]
  have hfac : ∀ j : ℕ, ((Nat.factorial j : ℕ) : ℝ) ≠ 0 :=
    fun j ↦ by positivity
  have hkR : (k : ℝ) ≠ 0 := by positivity
  have h2k1 : 2 * (k : ℝ) - 1 ≠ 0 := by grind
  have hnk1 : (n : ℝ) - (k : ℝ) + 1 ≠ 0 := by
    have : (k : ℝ) ≤ n := by simp_all
    linarith
  have hnk2 : (n : ℝ) - (k : ℝ) + 2 ≠ 0 := by
    have : (k : ℝ) ≤ n := by simp_all
    linarith
  have hden :
      4 + (n : ℝ) * 4 - (n : ℝ) * (k : ℝ) * 2 + (n : ℝ) ^ 2 -
          (k : ℝ) * 4 + (k : ℝ) ^ 2 ≠ 0 := by
    grind
  field_simp [hfac, hkR, h2k1, hnk1, hnk2, hden]
  ring_nf
  grind

private theorem coeff_recurrence_top (n : ℕ) :
    ((n : ℝ) + 2) ^ 2 * (polynomial (n + 2)).coeff (n + 2) =
      (-(8 * (n : ℝ) + 10) * (((n + 2 : ℕ) : ℝ) - 1) +
          (12 * (n : ℝ) ^ 2 + 32 * (n : ℝ) + 22)) *
        (polynomial (n + 1)).coeff (n + 1) := by
  rw [coeff_polynomial, coeff_polynomial]
  simp only [Nat.choose_self, one_pow, one_mul]
  have hcb := congrArg (fun z : ℕ ↦ (z : ℝ))
    (Nat.succ_mul_centralBinom_succ (n + 1))
  simp only [Nat.centralBinom] at hcb
  grind

private theorem coeff_recurrence_nextToTop (n : ℕ) :
    ((n : ℝ) + 2) ^ 2 * (polynomial (n + 2)).coeff (n + 1) =
      ((8 * (n : ℝ) + 10) * ((n + 1 : ℕ) : ℝ) +
          (1 - 2 * (n : ℝ) ^ 2 - 2 * (n : ℝ))) *
        (polynomial (n + 1)).coeff (n + 1) +
      (-(8 * (n : ℝ) + 10) * (n : ℝ) +
          (12 * (n : ℝ) ^ 2 + 32 * (n : ℝ) + 22)) *
        (polynomial (n + 1)).coeff n -
      12 * ((n : ℝ) + 1) ^ 2 * (polynomial n).coeff n := by
  rw [coeff_polynomial, coeff_polynomial, coeff_polynomial, coeff_polynomial]
  simp only [Nat.choose_self, Nat.choose_succ_self_right, one_pow, one_mul]
  have hcb := congrArg (fun z : ℕ ↦ (z : ℝ))
    (Nat.succ_mul_centralBinom_succ n)
  simp only [Nat.centralBinom] at hcb
  grind

private theorem polynomial_recurrence_cleared (n : ℕ) :
    C (((n : ℝ) + 2) ^ 2) * polynomial (n + 2) =
      C (8 * (n : ℝ) + 10) * X * (1 - X) *
          (polynomial (n + 1)).derivative +
        (C (1 - 2 * (n : ℝ) ^ 2 - 2 * (n : ℝ)) +
            C (12 * (n : ℝ) ^ 2 + 32 * (n : ℝ) + 22) * X) *
          polynomial (n + 1) +
        C (3 * ((n : ℝ) + 1) ^ 2) * (1 - 4 * X) * polynomial n := by
  ext k
  rw [show
      C (8 * (n : ℝ) + 10) * X * (1 - X) *
              (polynomial (n + 1)).derivative +
            (C (1 - 2 * (n : ℝ) ^ 2 - 2 * (n : ℝ)) +
                C (12 * (n : ℝ) ^ 2 + 32 * (n : ℝ) + 22) * X) *
              polynomial (n + 1) +
            C (3 * ((n : ℝ) + 1) ^ 2) * (1 - 4 * X) * polynomial n =
      C (8 * (n : ℝ) + 10) *
          (X * (polynomial (n + 1)).derivative -
            X ^ 2 * (polynomial (n + 1)).derivative) +
        C (1 - 2 * (n : ℝ) ^ 2 - 2 * (n : ℝ)) * polynomial (n + 1) +
        C (12 * (n : ℝ) ^ 2 + 32 * (n : ℝ) + 22) *
          (X * polynomial (n + 1)) +
        C (3 * ((n : ℝ) + 1) ^ 2) * polynomial n -
        C (3 * ((n : ℝ) + 1) ^ 2) * (4 * (X * polynomial n)) by ring]
  cases k with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_C_mul, coeff_X_mul_zero,
        coeff_X_pow_mul', coeff_derivative, coeff_ofNat_mul,
        coeff_polynomial_zero]
      grind
  | succ k =>
    cases k with
    | zero =>
      simp only [coeff_add, coeff_sub, coeff_C_mul, coeff_X_mul,
        coeff_X_pow_mul', coeff_derivative, coeff_ofNat_mul]
      norm_num
      by_cases hn : n = 0
      · subst n
        norm_num [coeff_polynomial]
      · have h := coeff_recurrence_interior n 1 (by lia) (by lia)
        rw [coeff_polynomial_zero (n + 1), coeff_polynomial_zero n] at h
        grind
    | succ k =>
      simp only [coeff_add, coeff_sub, coeff_C_mul, coeff_X_mul,
        coeff_X_pow_mul', coeff_derivative, coeff_ofNat_mul]
      rw [ite_eq_left (by lia : 2 ≤ k + 2)]
      rw [show k + 1 + 1 - 2 + 1 = k + 1 by lia,
        show k + 1 + 1 - 2 = k by lia]
      push_cast
      by_cases hkn : k + 2 ≤ n
      · have h := coeff_recurrence_interior n (k + 2) (by lia) hkn
        grind
      · by_cases hnext : k + 2 = n + 1
        · rw [show k + 1 = n by lia]
          have hkR : (k : ℝ) + 1 + 1 = (n : ℝ) + 1 := by
            exact_mod_cast hnext
          have hkRprev : (k : ℝ) + 1 = (n : ℝ) := by simp_all
          rw [hkR, hkRprev]
          have hz : (polynomial n).coeff (n + 1) = 0 := by
            rw [coeff_polynomial,
              Nat.choose_eq_zero_of_lt (by lia : n < n + 1)]
            simp
          rw [hz]
          have h := coeff_recurrence_nextToTop n
          grind
        · by_cases htop : k + 2 = n + 2
          · rw [show k + 1 = n + 1 by lia]
            have hkR : (k : ℝ) + 1 + 1 = (n : ℝ) + 2 := by grind
            have hkRprev : (k : ℝ) + 1 = (n : ℝ) + 1 := by simp_all
            rw [hkR, hkRprev]
            have hz1 : (polynomial (n + 1)).coeff (n + 2) = 0 := by
              rw [coeff_polynomial,
                Nat.choose_eq_zero_of_lt (by lia : n + 1 < n + 2)]
              simp
            have hz2 : (polynomial n).coeff (n + 2) = 0 := by
              rw [coeff_polynomial,
                Nat.choose_eq_zero_of_lt (by lia : n < n + 2)]
              simp
            have hz3 : (polynomial n).coeff (n + 1) = 0 := by
              rw [coeff_polynomial,
                Nat.choose_eq_zero_of_lt (by lia : n < n + 1)]
              simp
            rw [hz1, hz2, hz3]
            have h := coeff_recurrence_top n
            grind
          · have hgt : n + 2 < k + 2 := by lia
            simp only [coeff_polynomial]
            rw [Nat.choose_eq_zero_of_lt hgt,
              Nat.choose_eq_zero_of_lt (by lia : n + 1 < k + 2),
              Nat.choose_eq_zero_of_lt (by lia : n + 1 < k + 1),
              Nat.choose_eq_zero_of_lt (by lia : n < k + 2),
              Nat.choose_eq_zero_of_lt (by lia : n < k + 1)]
            simp

private def normalizedNextRow (n : ℕ) (p q : ℝ[X]) : ℝ[X] :=
  C ((8 * (n : ℝ) + 10) / ((n : ℝ) + 2) ^ 2) * X * (1 - X) * p.derivative +
    (C ((1 - 2 * (n : ℝ) ^ 2 - 2 * (n : ℝ)) / ((n : ℝ) + 2) ^ 2) +
      C ((12 * (n : ℝ) ^ 2 + 32 * (n : ℝ) + 22) /
        ((n : ℝ) + 2) ^ 2) * X) * p +
    C (3 * ((n : ℝ) + 1) ^ 2 / ((n : ℝ) + 2) ^ 2) * (1 - 4 * X) * q

/-- The coefficient model satisfies a normalized form of the downstream recurrence. -/
theorem polynomial_recurrence_normalized (n : ℕ) :
    polynomial (n + 2) =
      C ((8 * (n : ℝ) + 10) / ((n : ℝ) + 2) ^ 2) * X * (1 - X) *
          (polynomial (n + 1)).derivative +
        (C ((1 - 2 * (n : ℝ) ^ 2 - 2 * (n : ℝ)) /
            ((n : ℝ) + 2) ^ 2) +
          C ((12 * (n : ℝ) ^ 2 + 32 * (n : ℝ) + 22) /
            ((n : ℝ) + 2) ^ 2) * X) * polynomial (n + 1) +
        C (3 * ((n : ℝ) + 1) ^ 2 / ((n : ℝ) + 2) ^ 2) *
          (1 - 4 * X) * polynomial n := by
  have hden : ((n : ℝ) + 2) ^ 2 ≠ 0 := by positivity
  have hC : C (((n : ℝ) + 2) ^ 2) ≠ 0 := by
    intro hz
    have h := congrArg (fun p : ℝ[X] ↦ p.eval 0) hz
    simp only [eval_C, eval_zero] at h
    simp_all
  apply mul_left_cancel₀ hC
  rw [polynomial_recurrence_cleared]
  apply Polynomial.funext
  intro r
  simp only [eval_add, eval_mul, eval_C, eval_X, eval_sub, eval_one]
  grind

/-- The generated downstream lag-two update for A367177. -/
def nextRow (n : ℕ) (p q : ℝ[X]) : ℝ[X] :=
  (C ((1 / (-5 + (3 + (n : ℝ)) ^ 2 + -2 * (n : ℝ))) *
        (10 + 8 * (n : ℝ))) * X +
      C ((1 / (-5 + (3 + (n : ℝ)) ^ 2 + -2 * (n : ℝ))) *
        (-10 + -8 * (n : ℝ))) * X ^ 2) * p.derivative +
    (C ((1 / (-5 + (3 + (n : ℝ)) ^ 2 + -2 * (n : ℝ))) *
        (19 + -2 * (3 + (n : ℝ)) ^ 2 + 10 * (n : ℝ))) +
      C ((1 / (-5 + (3 + (n : ℝ)) ^ 2 + -2 * (n : ℝ))) *
        (-86 + -40 * (n : ℝ) + 12 * (3 + (n : ℝ)) ^ 2)) * X) * p +
    (C ((1 / (-5 + (3 + (n : ℝ)) ^ 2 + -2 * (n : ℝ))) *
        (-24 + -12 * (n : ℝ) + 3 * (3 + (n : ℝ)) ^ 2)) +
      C ((1 / (-5 + (3 + (n : ℝ)) ^ 2 + -2 * (n : ℝ))) *
        (96 + -12 * (3 + (n : ℝ)) ^ 2 + 48 * (n : ℝ))) * X) * q

private theorem nextRow_eq_normalized (n : ℕ) (p q : ℝ[X]) :
    nextRow n p q = normalizedNextRow n p q := by
  apply Polynomial.funext
  intro x
  simp only [nextRow, normalizedNextRow, eval_add, eval_mul, eval_C, eval_X,
    eval_sub, eval_one, eval_pow, eval_ofNat]
  grind

/-- The coefficient model satisfies the generated downstream recurrence. -/
theorem polynomial_recurrence (n : ℕ) :
    polynomial (n + 2) = nextRow n (polynomial (n + 1)) (polynomial n) := by
  rw [nextRow_eq_normalized]
  exact polynomial_recurrence_normalized n

/-- Consecutive A367177 model rows are in directed proper position. -/
theorem polynomial_strictInterl_succ (n : ℕ) :
    StrictInterl (polynomial n) (polynomial (n + 1)) :=
  strictInterl_reciprocalShift_doubleNarayanaPolynomial_succ n

/-- Consecutive A367177 model rows interlace. -/
theorem polynomial_interlaces (n : ℕ) :
    Interlaces (polynomial n) (polynomial (n + 1)) :=
  (polynomial_strictInterl_succ n).toInterlaces (by
    rw [polynomial_natDegree, polynomial_natDegree])

/-- Every A367177 model row splits over the reals. -/
theorem polynomial_splits (n : ℕ) : (polynomial n).Splits :=
  (polynomial_strictInterl_succ n).1.2

private theorem polynomial_zero : polynomial 0 = 1 := by
  ext k
  rw [coeff_polynomial]
  cases k <;> simp [coeff_one, Nat.choose_eq_zero_of_lt]

private theorem polynomial_one : polynomial 1 = 1 + 2 * X := by
  ext k
  rw [coeff_polynomial]
  rcases k with _ | _ | k
  · simp [coeff_add, coeff_one, coeff_X]
  · norm_num [coeff_add, coeff_one, coeff_X]
  · simp [coeff_add, coeff_one, coeff_X,
      Nat.choose_eq_zero_of_lt (by lia : 1 < k + 2)]

/-- A sequence with the A367177 initial rows and update has split rows. -/
@[rr_row_model]
theorem splits_of_recurrence
    {P : ℕ → ℝ[X]}
    (hzero : P 0 = 1)
    (hone : P 1 = 1 + 2 * X)
    (hrec : ∀ n : ℕ, P (n + 2) = nextRow n (P (n + 1)) (P n))
    (n : ℕ) :
    (P n).Splits := by
  have heq := sequence_eq_of_same_lag_two_recurrence nextRow
    (hzero.trans polynomial_zero.symm) (hone.trans polynomial_one.symm)
    hrec polynomial_recurrence
  rw [heq n]
  exact polynomial_splits n

/-- Consecutive rows of a sequence with the A367177 initial rows and update interlace. -/
@[rr_row_model]
theorem interlaces_of_recurrence
    {P : ℕ → ℝ[X]}
    (hzero : P 0 = 1)
    (hone : P 1 = 1 + 2 * X)
    (hrec : ∀ n : ℕ, P (n + 2) = nextRow n (P (n + 1)) (P n))
    (n : ℕ) :
    Interlaces (P n) (P (n + 1)) := by
  have heq := sequence_eq_of_same_lag_two_recurrence nextRow
    (hzero.trans polynomial_zero.symm) (hone.trans polynomial_one.symm)
    hrec polynomial_recurrence
  rw [heq n, heq (n + 1)]
  exact polynomial_interlaces n

end RealRooted.Applications.OEIS.A367177
