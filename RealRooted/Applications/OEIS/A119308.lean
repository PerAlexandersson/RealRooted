module

import RealRooted.EulerOperator
import RealRooted.Mathlib.RingTheory.Polynomial.Pochhammer
public import RealRooted.FiniteFreeRootCount
public import RealRooted.Hadamard
public import RealRooted.Interlacing.ReversalCommonFactor
public import RealRooted.LinearPowerFamily
import RealRooted.MultiplierSequence.EulerCoefficientRatio
public import RealRooted.MultiplierSequence.InvPochhammer
public import RealRooted.MultiplierSequence.Infinite
public import RealRooted.MultiplierSequence.JensenAffineTheta
public import RealRooted.MultiplierSequence.ProperPosition
public import RealRooted.NarayanaTransformation
import RealRooted.Recurrence.RowModel
import RealRooted.Recurrence.Uniqueness
import RealRooted.Hadamard.Grace
import RealRooted.NarayanaTransformation.Endpoints
import RealRooted.NarayanaTransformation.Recurrences.Identities
import RealRooted.NarayanaTransformation.Rectangular.Narayana

/-!
# The A119308 hypergeometric model

The row has coefficient `C(n+1,k) (2 C(n+1,k+2) + C(n+1,k+1)) / (n+1)`.
-/

@[expose] public section

open RealRooted Polynomial

noncomputable section

namespace RealRooted.Applications.OEIS.A119308

/-- The downstream lag-three update for A119308. -/
def nextRow (n : ℕ) (p q r : ℝ[X]) : ℝ[X] :=
  (C ((1 / (3 + (1 / 2) * (n : ℝ))) * ((13 / 2) + (3 / 2) * (n : ℝ))) +
      C ((1 / (3 + (1 / 2) * (n : ℝ))) * ((9 / 2) + (n : ℝ))) * X) * p +
    (C ((1 / (3 + (1 / 2) * (n : ℝ))) * (-4 + (-3 / 2) * (n : ℝ))) +
      C ((1 / 2) * (1 / (3 + (1 / 2) * (n : ℝ)))) * X +
      C ((1 / (3 + (1 / 2) * (n : ℝ))) * ((-3 / 2) + (-1 / 2) * (n : ℝ))) *
        X ^ 2) * q +
    (C ((1 / (3 + (1 / 2) * (n : ℝ))) * ((1 / 2) + (1 / 2) * (n : ℝ))) +
      C ((1 / (3 + (1 / 2) * (n : ℝ))) * (-1 + -1 * (n : ℝ))) * X +
      C ((1 / (3 + (1 / 2) * (n : ℝ))) * ((1 / 2) + (1 / 2) * (n : ℝ))) *
        X ^ 2) * r

/-- The row polynomials of A119308, given by the lag-three recurrence with update `nextRow`. -/
def recurrencePolynomial : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 2 + X
  | 2 => 3 + 5 * X + X ^ 2
  | n + 3 => nextRow n (recurrencePolynomial (n + 2))
      (recurrencePolynomial (n + 1)) (recurrencePolynomial n)

example : recurrencePolynomial 0 = 1 := by
  rfl
example : recurrencePolynomial 1 = 2 + X := by
  rfl
example : recurrencePolynomial 2 = 3 + 5 * X + X ^ 2 := by
  rfl
example : recurrencePolynomial 3 = 4 + 14 * X + 9 * X ^ 2 + X ^ 3 := by
  simp only [recurrencePolynomial, nextRow]
  apply Polynomial.funext
  intro r
  simp only [eval_add, eval_mul, eval_C, eval_X, eval_one, eval_pow, eval_ofNat]
  grind
example : recurrencePolynomial 4 = 5 + 30 * X + 40 * X ^ 2 + 14 * X ^ 3 + X ^ 4 := by
  simp only [recurrencePolynomial, nextRow]
  apply Polynomial.funext
  intro r
  simp only [eval_add, eval_mul, eval_C, eval_X, eval_one, eval_pow, eval_ofNat]
  grind

private lemma A119308_coeff_succ_succ_succ (n k : ℕ) :
    AddMonoidAlgebra.coeff (recurrencePolynomial (n + 3)) (k + 3) =
      (((1 / (3 + (1 / 2) * (n : ℝ))) * ((13 / 2) + (3 / 2) * (n : ℝ))) *
          AddMonoidAlgebra.coeff (recurrencePolynomial (n + 2)) (k + 3))
        + (((1 / (3 + (1 / 2) * (n : ℝ))) * ((9 / 2) + (n : ℝ))) *
          AddMonoidAlgebra.coeff (recurrencePolynomial (n + 2)) (k + 2))
        + (((1 / (3 + (1 / 2) * (n : ℝ))) * (-4 + (-3 / 2) * (n : ℝ))) *
          AddMonoidAlgebra.coeff (recurrencePolynomial (n + 1)) (k + 3))
        + (((1 / 2) * (1 / (3 + (1 / 2) * (n : ℝ)))) *
          AddMonoidAlgebra.coeff (recurrencePolynomial (n + 1)) (k + 2))
        + (((1 / (3 + (1 / 2) * (n : ℝ))) * ((-3 / 2) + (-1 / 2) * (n : ℝ))) *
          AddMonoidAlgebra.coeff (recurrencePolynomial (n + 1)) (k + 1))
        + (((1 / (3 + (1 / 2) * (n : ℝ))) * ((1 / 2) + (1 / 2) * (n : ℝ))) *
          AddMonoidAlgebra.coeff (recurrencePolynomial n) (k + 3))
        + (((1 / (3 + (1 / 2) * (n : ℝ))) * (-1 + -1 * (n : ℝ))) *
          AddMonoidAlgebra.coeff (recurrencePolynomial n) (k + 2))
        + (((1 / (3 + (1 / 2) * (n : ℝ))) * ((1 / 2) + (1 / 2) * (n : ℝ))) *
          AddMonoidAlgebra.coeff (recurrencePolynomial n) (k + 1)) := by
  rw [recurrencePolynomial, nextRow]
  simp only [add_mul, coeff_add, mul_assoc, coeff_C_mul, coeff_X_mul,
    coeff_X_pow_mul']
  grind

private def A119308Coeff (n k : ℕ) : ℝ :=
  (Nat.choose (n + 1) k : ℝ) *
    (2 * (Nat.choose (n + 1) (k + 2) : ℝ) +
      (Nat.choose (n + 1) (k + 1) : ℝ)) /
    ((n : ℝ) + 1)

private lemma A119308Coeff_eq_factorial (n k : ℕ) (hk : k < n) :
    A119308Coeff n k =
      ((Nat.factorial n : ℝ) * (Nat.factorial (n + 1) : ℝ) *
        (((2 * n + 2 - k : ℕ) : ℝ))) /
      ((Nat.factorial k : ℝ) * (Nat.factorial (k + 2) : ℝ) *
        (Nat.factorial (n + 1 - k) : ℝ) * (Nat.factorial (n - k) : ℝ)) := by
  unfold A119308Coeff
  have hk0 : k ≤ n + 1 := by lia
  have hk1 : k + 1 ≤ n + 1 := by lia
  have hk2 : k + 2 ≤ n + 1 := by lia
  rw [Nat.cast_choose ℝ hk0, Nat.cast_choose ℝ hk2,
    Nat.cast_choose ℝ hk1]
  have hsub0 : n + 1 - k = n - k + 1 := by lia
  have hsub1 : n + 1 - (k + 1) = n - k := by lia
  have hsub2 : n + 1 - (k + 2) = n - k - 1 := by lia
  rw [hsub0, hsub1, hsub2, factorial_succ_cast n,
    factorial_succ_cast k, factorial_succ_succ_cast k,
    factorial_succ_cast (n - k)]
  have hnk : n - k ≠ 0 := by lia
  rw [factorial_cast_pred hnk]
  have hfac : ∀ m : ℕ, (Nat.factorial m : ℝ) ≠ 0 :=
    fun m => Nat.cast_ne_zero.mpr (Nat.factorial_pos m).ne'
  field_simp [hfac]
  rw [Nat.cast_sub (by lia : k ≤ 2 * n + 2)]
  rw [Nat.cast_sub (by lia : k ≤ n)]
  grind

private def A119308CoeffRecRhs (n k : ℕ) : ℝ :=
  (((1 / (3 + (1 / 2) * (n : ℝ))) * ((13 / 2) + (3 / 2) * (n : ℝ))) *
          A119308Coeff (n + 2) (k + 3))
    + (((1 / (3 + (1 / 2) * (n : ℝ))) * ((9 / 2) + (n : ℝ))) *
          A119308Coeff (n + 2) (k + 2))
    + (((1 / (3 + (1 / 2) * (n : ℝ))) * (-4 + (-3 / 2) * (n : ℝ))) *
          A119308Coeff (n + 1) (k + 3))
    + (((1 / 2) * (1 / (3 + (1 / 2) * (n : ℝ)))) *
          A119308Coeff (n + 1) (k + 2))
    + (((1 / (3 + (1 / 2) * (n : ℝ))) * ((-3 / 2) + (-1 / 2) * (n : ℝ))) *
          A119308Coeff (n + 1) (k + 1))
    + (((1 / (3 + (1 / 2) * (n : ℝ))) * ((1 / 2) + (1 / 2) * (n : ℝ))) *
          A119308Coeff n (k + 3))
    + (((1 / (3 + (1 / 2) * (n : ℝ))) * (-1 + -1 * (n : ℝ))) *
          A119308Coeff n (k + 2))
    + (((1 / (3 + (1 / 2) * (n : ℝ))) * ((1 / 2) + (1 / 2) * (n : ℝ))) *
          A119308Coeff n (k + 1))

private lemma A119308Coeff_horizontal (n k : ℕ) (hk : k + 1 < n) :
    A119308Coeff n (k + 1) *
        ((k : ℝ) + 1) * ((k : ℝ) + 3) *
          (2 * (n : ℝ) + 2 - (k : ℝ)) =
      A119308Coeff n k *
        ((n : ℝ) + 1 - (k : ℝ)) * ((n : ℝ) - (k : ℝ)) *
          (2 * (n : ℝ) + 1 - (k : ℝ)) := by
  rw [A119308Coeff_eq_factorial n (k + 1) hk,
    A119308Coeff_eq_factorial n k (by lia)]
  have hsub1 : n + 1 - (k + 1) = n - k := by lia
  have hsub2 : n - (k + 1) = n - k - 1 := by lia
  have hsub0 : n + 1 - k = n - k + 1 := by lia
  have hnk : n - k ≠ 0 := by lia
  rw [hsub1, hsub2, hsub0, factorial_succ_cast (k + 2),
    factorial_succ_cast (k + 1), factorial_succ_cast k,
    factorial_succ_cast (n - k), factorial_cast_pred hnk]
  have hfac : ∀ m : ℕ, (Nat.factorial m : ℝ) ≠ 0 :=
    fun m => Nat.cast_ne_zero.mpr (Nat.factorial_pos m).ne'
  field_simp [hfac]
  rw [Nat.cast_sub (by lia : k + 1 ≤ 2 * n + 2),
    Nat.cast_sub (by lia : k ≤ 2 * n + 2)]
  have hcast : ((n - k : ℕ) : ℝ) = (n : ℝ) - (k : ℝ) :=
    Nat.cast_sub (by lia)
  grind

private lemma A119308Coeff_vertical (n k : ℕ) (hk : k < n) :
    A119308Coeff (n + 1) k *
        ((n : ℝ) + 2 - (k : ℝ)) * ((n : ℝ) + 1 - (k : ℝ)) *
          (2 * (n : ℝ) + 2 - (k : ℝ)) =
      A119308Coeff n k *
        ((n : ℝ) + 1) * ((n : ℝ) + 2) *
          (2 * (n : ℝ) + 4 - (k : ℝ)) := by
  rw [A119308Coeff_eq_factorial (n + 1) k (by lia),
    A119308Coeff_eq_factorial n k hk]
  have hsub1 : n + 2 - k = n + 1 - k + 1 := by lia
  have hsub2 : n + 1 - k = n - k + 1 := by lia
  rw [hsub1, hsub2, factorial_succ_cast (n + 1),
    factorial_succ_cast n, factorial_succ_cast (n - k + 1),
    factorial_succ_cast (n - k)]
  have hfac : ∀ m : ℕ, (Nat.factorial m : ℝ) ≠ 0 :=
    fun m => Nat.cast_ne_zero.mpr (Nat.factorial_pos m).ne'
  field_simp [hfac]
  rw [Nat.cast_sub (by lia : k ≤ 2 * (n + 1) + 2),
    Nat.cast_sub (by lia : k ≤ 2 * n + 2)]
  have hcast : ((n - k : ℕ) : ℝ) = (n : ℝ) - (k : ℝ) :=
    Nat.cast_sub (by lia)
  grind

private def A119308CoeffH (n k : ℕ) : ℝ :=
  (((n : ℝ) + 1 - (k : ℝ)) * ((n : ℝ) - (k : ℝ)) *
      (2 * (n : ℝ) + 1 - (k : ℝ))) /
    (((k : ℝ) + 1) * ((k : ℝ) + 3) *
      (2 * (n : ℝ) + 2 - (k : ℝ)))

private lemma A119308Coeff_horizontal_eq (n k : ℕ) (hk : k + 1 < n) :
    A119308Coeff n (k + 1) =
      A119308Coeff n k * A119308CoeffH n k := by
  have hden :
      ((k : ℝ) + 1) * ((k : ℝ) + 3) *
          (2 * (n : ℝ) + 2 - (k : ℝ)) ≠ 0 := by
    have hkn : (k : ℝ) + 1 < (n : ℝ) := by exact_mod_cast hk
    have hpos : 0 <
        ((k : ℝ) + 1) * ((k : ℝ) + 3) *
          (2 * (n : ℝ) + 2 - (k : ℝ)) := by
      have : 0 < 2 * (n : ℝ) + 2 - (k : ℝ) := by linarith
      positivity
    grind
  rw [A119308CoeffH]
  rw [← mul_div_assoc]
  apply (eq_div_iff hden).2
  linear_combination A119308Coeff_horizontal n k hk

private def A119308CoeffV (n k : ℕ) : ℝ :=
  (((n : ℝ) + 1) * ((n : ℝ) + 2) *
      (2 * (n : ℝ) + 4 - (k : ℝ))) /
    (((n : ℝ) + 2 - (k : ℝ)) * ((n : ℝ) + 1 - (k : ℝ)) *
      (2 * (n : ℝ) + 2 - (k : ℝ)))

private lemma A119308Coeff_vertical_eq (n k : ℕ) (hk : k < n) :
    A119308Coeff (n + 1) k =
      A119308Coeff n k * A119308CoeffV n k := by
  have hden :
      ((n : ℝ) + 2 - (k : ℝ)) * ((n : ℝ) + 1 - (k : ℝ)) *
          (2 * (n : ℝ) + 2 - (k : ℝ)) ≠ 0 := by
    have : (k : ℝ) < (n : ℝ) := by simp_all
    have hpos : 0 <
        ((n : ℝ) + 2 - (k : ℝ)) * ((n : ℝ) + 1 - (k : ℝ)) *
          (2 * (n : ℝ) + 2 - (k : ℝ)) := by
      have h₁ : 0 < (n : ℝ) + 2 - (k : ℝ) := by linarith
      have h₂ : 0 < (n : ℝ) + 1 - (k : ℝ) := by linarith
      have h₃ : 0 < 2 * (n : ℝ) + 2 - (k : ℝ) := by grind
      positivity
    grind
  rw [A119308CoeffV]
  rw [← mul_div_assoc]
  apply (eq_div_iff hden).2
  linear_combination A119308Coeff_vertical n k hk

private lemma A119308_choose_two_cast (m : ℕ) (hm : 1 ≤ m) :
    (Nat.choose m 2 : ℝ) =
      (m : ℝ) * ((m : ℝ) - 1) / 2 := by
  have hc := Nat.choose_succ_right_eq m 1
  norm_num [Nat.choose_one_right] at hc
  have hcr := congrArg (fun z : ℕ ↦ (z : ℝ)) hc
  norm_num at hcr
  rw [Nat.cast_sub hm] at hcr
  grind

private lemma A119308_choose_three_cast (m : ℕ) (hm : 2 ≤ m) :
    (Nat.choose m 3 : ℝ) =
      (m : ℝ) * ((m : ℝ) - 1) * ((m : ℝ) - 2) / 6 := by
  have hc := Nat.choose_succ_right_eq m 2
  norm_num at hc
  have hcr := congrArg (fun z : ℕ => (z : ℝ)) hc
  norm_num at hcr
  rw [Nat.cast_sub hm] at hcr
  norm_num at hcr
  rw [A119308_choose_two_cast m (by lia)] at hcr
  linarith

private lemma A119308_choose_four_cast (m : ℕ) (hm : 3 ≤ m) :
    (Nat.choose m 4 : ℝ) =
      (m : ℝ) * ((m : ℝ) - 1) * ((m : ℝ) - 2) *
        ((m : ℝ) - 3) / 24 := by
  have hc := Nat.choose_succ_right_eq m 3
  norm_num at hc
  have hcr := congrArg (fun z : ℕ => (z : ℝ)) hc
  norm_num at hcr
  rw [Nat.cast_sub hm] at hcr
  norm_num at hcr
  rw [A119308_choose_three_cast m (by lia)] at hcr
  linarith

private lemma A119308Coeff_rec_high_of_le (n k : ℕ) (hnk : n ≤ k + 2) :
    A119308Coeff (n + 3) (k + 3) = A119308CoeffRecRhs n k := by
  unfold A119308CoeffRecRhs
  rcases lt_trichotomy n k with hnk | rfl | hkn
  · have h0 : ∀ a b : ℕ, a < b →
        A119308Coeff a b = 0 := by
      intro a b hab
      unfold A119308Coeff
      rw [Nat.choose_eq_zero_of_lt (by lia : a + 1 < b + 2),
        Nat.choose_eq_zero_of_lt (by lia : a + 1 < b + 1)]
      ring
    grind
  · unfold A119308Coeff
    simp [Nat.choose_eq_zero_of_lt, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
    grind
  · rcases eq_or_lt_of_le (by lia : k + 1 ≤ n) with h | h
    · subst n
      unfold A119308Coeff
      simp only [Nat.choose_self, Nat.cast_one, mul_one,
        Nat.choose_succ_self_right, Nat.cast_add, Nat.cast_ofNat, one_div,
        Nat.choose_succ_self, CharP.cast_eq_zero, mul_zero, zero_add, add_zero,
        one_mul, zero_mul, zero_div, neg_mul, neg_add_rev]
      rw [Nat.choose_symm_of_eq_add
          (show k + 5 = (k + 3) + 2 by lia),
        Nat.choose_symm_of_eq_add
          (show k + 4 = (k + 2) + 2 by lia),
        Nat.choose_symm_of_eq_add
          (show k + 3 = (k + 1) + 2 by lia)]
      rw [Nat.choose_eq_zero_of_lt
          (by lia : k + 1 + 1 + 1 < k + 3 + 2),
        Nat.choose_eq_zero_of_lt (by lia : k + 1 + 1 < k + 2 + 2)]
      simp [Nat.choose]
      field_simp
      by_cases hk : k = 0
      · subst k
        norm_num
      · rw [A119308_choose_two_cast k (Nat.one_le_iff_ne_zero.mpr hk)]
        grind
    · rcases eq_or_lt_of_le (by lia : k + 2 ≤ n) with h | h
      · subst n
        unfold A119308Coeff
        simp only [Nat.choose_succ_self_right, Nat.cast_add, Nat.cast_ofNat,
          Nat.cast_one, one_div, Nat.choose_self, mul_one,
          Nat.choose_succ_self, CharP.cast_eq_zero, mul_zero, zero_add,
          add_zero, one_mul, neg_mul, neg_add_rev]
        rw [Nat.choose_symm_of_eq_add
            (show k + 6 = (k + 3) + 3 by lia),
          Nat.choose_symm_of_eq_add
            (show k + 6 = (k + 4) + 2 by lia),
          Nat.choose_symm_of_eq_add
            (show k + 5 = (k + 3) + 2 by lia),
          Nat.choose_symm_of_eq_add
            (show k + 5 = (k + 2) + 3 by lia),
          Nat.choose_symm_of_eq_add
            (show k + 4 = (k + 2) + 2 by lia),
          Nat.choose_symm_of_eq_add
            (show k + 4 = (k + 1) + 3 by lia),
          Nat.choose_symm_of_eq_add
            (show k + 3 = (k + 1) + 2 by lia)]
        rw [Nat.choose_eq_zero_of_lt
          (by lia : k + 2 + 1 < k + 3 + 2)]
        simp [Nat.choose]
        field_simp
        by_cases hk0 : k = 0
        · subst k
          norm_num
        · by_cases hk1 : k = 1
          · subst k
            norm_num [Nat.choose]
          · have hktwo : 2 ≤ k := by lia
            rw [A119308_choose_two_cast k (by lia),
              A119308_choose_three_cast k hktwo]
            grind
      · lia

private lemma A119308Coeff_rec_low (n k : ℕ) (hnk : k + 3 < n) :
    A119308Coeff (n + 3) (k + 3) = A119308CoeffRecRhs n k := by
  have hn2k2 :
      A119308Coeff (n + 2) (k + 2) =
        A119308Coeff n (k + 1) *
          A119308CoeffV n (k + 1) *
          A119308CoeffH (n + 1) (k + 1) *
          A119308CoeffV (n + 1) (k + 2) := by
    rw [A119308Coeff_vertical_eq (n + 1) (k + 2) (by lia),
      A119308Coeff_horizontal_eq (n + 1) (k + 1) (by lia),
      A119308Coeff_vertical_eq n (k + 1) (by lia)]
  have hn2k3 :
      A119308Coeff (n + 2) (k + 3) =
        A119308Coeff n (k + 1) *
          A119308CoeffV n (k + 1) *
          A119308CoeffH (n + 1) (k + 1) *
          A119308CoeffV (n + 1) (k + 2) *
          A119308CoeffH (n + 2) (k + 2) := by
    rw [A119308Coeff_horizontal_eq (n + 2) (k + 2) (by lia),
      hn2k2]
  have hn1k1 :
      A119308Coeff (n + 1) (k + 1) =
        A119308Coeff n (k + 1) * A119308CoeffV n (k + 1) :=
    A119308Coeff_vertical_eq n (k + 1) (by lia)
  have hn1k2 :
      A119308Coeff (n + 1) (k + 2) =
        A119308Coeff n (k + 1) *
          A119308CoeffV n (k + 1) *
          A119308CoeffH (n + 1) (k + 1) := by
    rw [A119308Coeff_horizontal_eq (n + 1) (k + 1) (by lia),
      hn1k1]
  have hn1k3 :
      A119308Coeff (n + 1) (k + 3) =
        A119308Coeff n (k + 1) *
          A119308CoeffH n (k + 1) *
          A119308CoeffH n (k + 2) *
          A119308CoeffV n (k + 3) := by
    rw [A119308Coeff_vertical_eq n (k + 3) (by assumption),
      A119308Coeff_horizontal_eq n (k + 2) (by assumption),
      A119308Coeff_horizontal_eq n (k + 1) (by lia)]
  have hnk2 :
      A119308Coeff n (k + 2) =
        A119308Coeff n (k + 1) * A119308CoeffH n (k + 1) :=
    A119308Coeff_horizontal_eq n (k + 1) (by lia)
  have hnk3 :
      A119308Coeff n (k + 3) =
        A119308Coeff n (k + 1) *
          A119308CoeffH n (k + 1) *
          A119308CoeffH n (k + 2) := by
    rw [A119308Coeff_horizontal_eq n (k + 2) (by assumption), hnk2]
  unfold A119308CoeffRecRhs
  rw [hn2k3, hn2k2, hn1k3, hn1k2, hn1k1, hnk3, hnk2,
    A119308Coeff_vertical_eq (n + 2) (k + 3) (by lia), hn2k3]
  unfold A119308CoeffH A119308CoeffV
  push_cast
  have hkn : (k : ℝ) + 3 < n := by exact_mod_cast hnk
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  field_simp (disch := linarith)
  ring

private lemma A119308Coeff_rec_boundary (k : ℕ) :
    A119308Coeff (k + 6) (k + 3) =
      A119308CoeffRecRhs (k + 3) k := by
  unfold A119308CoeffRecRhs A119308Coeff
  simp only [Nat.add_assoc]
  rw [Nat.choose_symm_of_eq_add
      (show k + 7 = (k + 3) + 4 by lia),
    Nat.choose_symm_of_eq_add
      (show k + 7 = (k + 5) + 2 by lia),
    Nat.choose_symm_of_eq_add
      (show k + 7 = (k + 4) + 3 by lia),
    Nat.choose_symm_of_eq_add
      (show k + 6 = (k + 2) + 4 by lia),
    Nat.choose_symm_of_eq_add
      (show k + 6 = (k + 3) + 3 by lia),
    Nat.choose_symm_of_eq_add
      (show k + 6 = (k + 4) + 2 by lia),
    Nat.choose_symm_of_eq_add
      (show k + 6 = (k + 5) + 1 by lia),
    Nat.choose_symm_of_eq_add
      (show k + 5 = (k + 1) + 4 by lia),
    Nat.choose_symm_of_eq_add
      (show k + 5 = (k + 2) + 3 by lia),
    Nat.choose_symm_of_eq_add
      (show k + 5 = (k + 3) + 2 by lia),
    Nat.choose_symm_of_eq_add
      (show k + 5 = (k + 4) + 1 by lia),
    Nat.choose_symm_of_eq_add
      (show k + 5 = (k + 5) + 0 by lia),
    Nat.choose_symm_of_eq_add
      (show k + 4 = (k + 1) + 3 by lia),
    Nat.choose_symm_of_eq_add
      (show k + 4 = (k + 2) + 2 by lia),
    Nat.choose_symm_of_eq_add
      (show k + 4 = (k + 3) + 1 by lia),
    Nat.choose_symm_of_eq_add
      (show k + 4 = (k + 4) + 0 by lia)]
  simp only [Nat.choose_zero_right, Nat.choose_one_right]
  rw [A119308_choose_two_cast (k + 7) (by lia),
    A119308_choose_three_cast (k + 7) (by lia),
    A119308_choose_four_cast (k + 7) (by lia),
    A119308_choose_two_cast (k + 6) (by lia),
    A119308_choose_three_cast (k + 6) (by lia),
    A119308_choose_four_cast (k + 6) (by lia),
    A119308_choose_two_cast (k + 5) (by lia),
    A119308_choose_three_cast (k + 5) (by lia),
    A119308_choose_four_cast (k + 5) (by lia),
    A119308_choose_two_cast (k + 4) (by lia),
    A119308_choose_three_cast (k + 4) (by lia)]
  simp [Nat.add_comm]
  field_simp
  ring

private lemma A119308Coeff_rec (n k : ℕ) :
    A119308Coeff (n + 3) (k + 3) = A119308CoeffRecRhs n k := by
  by_cases hhigh : n ≤ k + 2
  · exact A119308Coeff_rec_high_of_le n k hhigh
  · rcases eq_or_lt_of_le (by lia : k + 3 ≤ n) with h | h
    · subst n
      exact A119308Coeff_rec_boundary k
    · exact A119308Coeff_rec_low n k h

private lemma A119308Coeff_zero (n : ℕ) :
    A119308Coeff n 0 = (n : ℝ) + 1 := by
  unfold A119308Coeff
  simp [Nat.choose, Nat.add_comm]
  field_simp
  by_cases hn : n = 0
  · simp_all [Nat.choose_eq_zero_of_lt]
  rw [A119308_choose_two_cast n (Nat.one_le_iff_ne_zero.mpr hn)]
  ring

private lemma A119308Coeff_rec_zero (n : ℕ) :
    A119308Coeff (n + 3) 0 =
      (((13 / 2 : ℝ) + (3 / 2) * (n : ℝ)) /
          (3 + (1 / 2) * (n : ℝ))) * A119308Coeff (n + 2) 0 +
      ((-4 + (-3 / 2) * (n : ℝ)) /
          (3 + (1 / 2) * (n : ℝ))) * A119308Coeff (n + 1) 0 +
      (((1 / 2 : ℝ) + (1 / 2) * (n : ℝ)) /
          (3 + (1 / 2) * (n : ℝ))) * A119308Coeff n 0 := by
  rw [A119308Coeff_zero, A119308Coeff_zero, A119308Coeff_zero,
    A119308Coeff_zero]
  grind

private lemma A119308Coeff_one (n : ℕ) :
    A119308Coeff n 1 =
      (n : ℝ) * ((n : ℝ) + 1) * (2 * (n : ℝ) + 1) / 6 := by
  unfold A119308Coeff
  by_cases hn : n = 0
  · simp_all [Nat.choose_eq_zero_of_lt]
  have hm1 : 1 ≤ n + 1 := by lia
  have hm2 : 2 ≤ n + 1 := by lia
  rw [A119308_choose_two_cast (n + 1) hm1,
    A119308_choose_three_cast (n + 1) hm2]
  simp [Nat.choose_one_right]
  grind

private lemma A119308Coeff_rec_one (n : ℕ) :
    A119308Coeff (n + 3) 1 =
      (((13 / 2 : ℝ) + (3 / 2) * (n : ℝ)) /
          (3 + (1 / 2) * (n : ℝ))) * A119308Coeff (n + 2) 1 +
      (((9 / 2 : ℝ) + (n : ℝ)) /
          (3 + (1 / 2) * (n : ℝ))) * A119308Coeff (n + 2) 0 +
      ((-4 + (-3 / 2) * (n : ℝ)) /
          (3 + (1 / 2) * (n : ℝ))) * A119308Coeff (n + 1) 1 +
      ((1 / 2 : ℝ) / (3 + (1 / 2) * (n : ℝ))) *
          A119308Coeff (n + 1) 0 +
      (((1 / 2 : ℝ) + (1 / 2) * (n : ℝ)) /
          (3 + (1 / 2) * (n : ℝ))) * A119308Coeff n 1 +
      ((-1 - (n : ℝ)) / (3 + (1 / 2) * (n : ℝ))) *
          A119308Coeff n 0 := by
  rw [A119308Coeff_one, A119308Coeff_one, A119308Coeff_zero,
    A119308Coeff_one, A119308Coeff_zero, A119308Coeff_one,
    A119308Coeff_zero]
  grind

private lemma A119308Coeff_two (n : ℕ) :
    A119308Coeff n 2 =
      (n : ℝ) ^ 3 * ((n : ℝ) + 1) * ((n : ℝ) - 1) / 24 := by
  unfold A119308Coeff
  by_cases hn : n < 2
  · interval_cases n <;> norm_num [Nat.choose]
  have hm1 : 1 ≤ n + 1 := by lia
  have hm2 : 2 ≤ n + 1 := by lia
  have hm3 : 3 ≤ n + 1 := by lia
  rw [A119308_choose_two_cast (n + 1) hm1,
    A119308_choose_three_cast (n + 1) hm2,
    A119308_choose_four_cast (n + 1) hm3]
  grind

private lemma A119308Coeff_rec_two (n : ℕ) :
    A119308Coeff (n + 3) 2 =
      (((13 / 2 : ℝ) + (3 / 2) * (n : ℝ)) /
          (3 + (1 / 2) * (n : ℝ))) * A119308Coeff (n + 2) 2 +
      (((9 / 2 : ℝ) + (n : ℝ)) /
          (3 + (1 / 2) * (n : ℝ))) * A119308Coeff (n + 2) 1 +
      ((-4 + (-3 / 2) * (n : ℝ)) /
          (3 + (1 / 2) * (n : ℝ))) * A119308Coeff (n + 1) 2 +
      ((1 / 2 : ℝ) / (3 + (1 / 2) * (n : ℝ))) *
          A119308Coeff (n + 1) 1 +
      (((-3 / 2 : ℝ) + (-1 / 2) * (n : ℝ)) /
          (3 + (1 / 2) * (n : ℝ))) * A119308Coeff (n + 1) 0 +
      (((1 / 2 : ℝ) + (1 / 2) * (n : ℝ)) /
          (3 + (1 / 2) * (n : ℝ))) * A119308Coeff n 2 +
      ((-1 - (n : ℝ)) / (3 + (1 / 2) * (n : ℝ))) *
          A119308Coeff n 1 +
      (((1 / 2 : ℝ) + (1 / 2) * (n : ℝ)) /
          (3 + (1 / 2) * (n : ℝ))) * A119308Coeff n 0 := by
  rw [A119308Coeff_two, A119308Coeff_two, A119308Coeff_one,
    A119308Coeff_two, A119308Coeff_one, A119308Coeff_zero,
    A119308Coeff_two, A119308Coeff_one, A119308Coeff_zero]
  grind

private lemma A119308_coeff_recurrence_raw (n m : ℕ) :
    (recurrencePolynomial (n + 3)).coeff m =
      (((13 / 2 : ℝ) + (3 / 2) * (n : ℝ)) /
          (3 + (1 / 2) * (n : ℝ))) * (recurrencePolynomial (n + 2)).coeff m +
      (((9 / 2 : ℝ) + (n : ℝ)) /
          (3 + (1 / 2) * (n : ℝ))) *
        (X * recurrencePolynomial (n + 2)).coeff m +
      ((-4 + (-3 / 2) * (n : ℝ)) /
          (3 + (1 / 2) * (n : ℝ))) * (recurrencePolynomial (n + 1)).coeff m +
      ((1 / 2 : ℝ) / (3 + (1 / 2) * (n : ℝ))) *
        (X * recurrencePolynomial (n + 1)).coeff m +
      (((-3 / 2 : ℝ) + (-1 / 2) * (n : ℝ)) /
          (3 + (1 / 2) * (n : ℝ))) *
        (X ^ 2 * recurrencePolynomial (n + 1)).coeff m +
      (((1 / 2 : ℝ) + (1 / 2) * (n : ℝ)) /
          (3 + (1 / 2) * (n : ℝ))) * (recurrencePolynomial n).coeff m +
      ((-1 - (n : ℝ)) / (3 + (1 / 2) * (n : ℝ))) *
        (X * recurrencePolynomial n).coeff m +
      (((1 / 2 : ℝ) + (1 / 2) * (n : ℝ)) /
          (3 + (1 / 2) * (n : ℝ))) *
        (X ^ 2 * recurrencePolynomial n).coeff m := by
  rw [recurrencePolynomial, nextRow]
  simp only [add_mul, coeff_add, mul_assoc, coeff_C_mul]
  ring

private lemma A119308_coeff_closed (n k : ℕ) :
    (recurrencePolynomial n).coeff k = A119308Coeff n k := by
  induction n using Nat.strong_induction_on generalizing k with
  | ind n ih =>
      rcases n with _ | _ | _ | n
      · rcases k with _ | k
        · norm_num [recurrencePolynomial, nextRow, A119308Coeff]
        · simp [recurrencePolynomial, A119308Coeff, Nat.choose, coeff_one]
      · rcases k with _ | _ | k
        · norm_num [recurrencePolynomial, nextRow, A119308Coeff]
        · norm_num [recurrencePolynomial, nextRow, A119308Coeff]
        · simp [recurrencePolynomial, A119308Coeff, Nat.choose, coeff_X]
      · rcases k with _ | _ | _ | k
        · norm_num [recurrencePolynomial, nextRow, A119308Coeff]
        · norm_num [recurrencePolynomial, nextRow, A119308Coeff]
        · norm_num [recurrencePolynomial, nextRow, A119308Coeff, coeff_X]
        · simp [recurrencePolynomial, A119308Coeff, Nat.choose, coeff_X]
      · rcases k with _ | _ | _ | k
        · rw [A119308_coeff_recurrence_raw n 0]
          simp only [one_div, mul_coeff_zero, coeff_X_zero, zero_mul, mul_zero,
            add_zero, coeff_X_pow, OfNat.zero_ne_ofNat, ↓reduceIte]
          simp_rw [ih (n + 2) (by lia), ih (n + 1) (by lia),
            ih n (by lia)]
          simpa [Nat.add_assoc] using (A119308Coeff_rec_zero n).symm
        · rw [A119308_coeff_recurrence_raw n 1]
          simp only [one_div, coeff_X_mul, coeff_X_pow_mul', zero_add]
          simp_rw [ih (n + 2) (by lia), ih (n + 1) (by lia),
            ih n (by lia)]
          simpa [Nat.add_assoc] using (A119308Coeff_rec_one n).symm
        · rw [A119308_coeff_recurrence_raw n 2]
          simp only [one_div, coeff_X_mul, coeff_X_pow_mul', zero_add,
            Nat.reduceAdd]
          simp_rw [ih (n + 2) (by lia), ih (n + 1) (by lia),
            ih n (by lia)]
          simpa [Nat.add_assoc] using (A119308Coeff_rec_two n).symm
        · rw [A119308_coeff_succ_succ_succ n k]
          simp_rw [ih (n + 2) (by lia), ih (n + 1) (by lia),
            ih n (by lia)]
          simpa [A119308CoeffRecRhs, Nat.add_assoc] using
            (A119308Coeff_rec n k).symm

private lemma A119308Coeff_above (n k : ℕ) (hk : n < k) :
    A119308Coeff n k = 0 := by
  unfold A119308Coeff
  rw [Nat.choose_eq_zero_of_lt (by lia : n + 1 < k + 2),
    Nat.choose_eq_zero_of_lt (by lia : n + 1 < k + 1)]
  ring

/-- The strictly interlacing coefficient model for A119308. -/
def polynomial (n : ℕ) : ℝ[X] :=
  affineThetaJensenPolynomial n

private lemma polynomial_coeff_of_le (n k : ℕ) (hk : k ≤ n) :
    (polynomial n).coeff k = A119308Coeff n k := by
  rw [polynomial, coeff_affineThetaJensenPolynomial_of_le n k hk]
  rcases eq_or_lt_of_le hk with rfl | hklt
  · simp only [Nat.sub_self, Nat.choose_zero_right, Nat.cast_one,
      affineThetaLeftWeight, affineThetaRightWeight, A119308Coeff,
      Nat.choose_succ_self_right, Nat.cast_add, Nat.choose_self, mul_one]
    rw [Nat.choose_eq_zero_of_lt (by lia : k + 1 < k + 2)]
    simp only [Nat.cast_zero, mul_zero, zero_add]
    rw [ascPochhammer_eval_two, show (k + 1).factorial = (k + 1) * k.factorial by
      rw [Nat.factorial_succ]]
    have hthree := two_mul_ascPochhammer_eval_three (R := ℝ) k
    rw [Nat.factorial_succ (k + 1), Nat.factorial_succ k] at hthree
    push_cast at hthree
    have hfac : ∀ m : ℕ, (m.factorial : ℝ) ≠ 0 := fun m => by positivity
    have heval : (ascPochhammer ℝ k).eval 3 ≠ 0 := by
      intro heval
      rw [heval, mul_zero] at hthree
      have hpos :
          0 < ((k : ℝ) + 1 + 1) * (((k : ℝ) + 1) * (k.factorial : ℝ)) := by
        positivity
      linarith
    field_simp [hfac, heval]
    norm_num only [Nat.factorial_one, Nat.cast_one]
    push_cast
    nlinarith
  · rw [A119308Coeff_eq_factorial n k hklt]
    rw [affineThetaLeftWeight, affineThetaRightWeight,
      ascPochhammer_eval_two]
    have hthree := two_mul_ascPochhammer_eval_three (R := ℝ) k
    rw [Nat.cast_choose ℝ (Nat.sub_le n k), Nat.sub_sub_self hk]
    have hfac : ∀ m : ℕ, (m.factorial : ℝ) ≠ 0 := fun m => by positivity
    field_simp [hfac]
    rw [Nat.cast_sub (by lia : k ≤ 2 * n + 2)]
    grind

private lemma polynomial_coeff (n k : ℕ) :
    (polynomial n).coeff k = A119308Coeff n k := by
  by_cases hk : k ≤ n
  · exact polynomial_coeff_of_le n k hk
  · rw [coeff_eq_zero_of_natDegree_lt (by
        rw [polynomial, natDegree_affineThetaJensenPolynomial]
        lia), A119308Coeff_above n k (by lia)]

private lemma recurrencePolynomial_eq_polynomial (n : ℕ) :
    recurrencePolynomial n = polynomial n := by
  ext k
  rw [A119308_coeff_closed, polynomial_coeff]

private lemma polynomial_coeff_eq_euler (n k : ℕ) (hk : k ≤ n) :
    (polynomial n).coeff k = (n + 1).factorial / 2 *
      (eulerPochhammerPolynomial n [3] [2] [] [(n : ℝ) + 2]).coeff k := by
  rw [polynomial, coeff_affineThetaJensenPolynomial_of_le n k hk,
    eulerPochhammerPolynomial_coeff (by simp)
        (by simpa using (show (0 : ℝ) < n + 2 by positivity)),
    pochhammerJensenPolynomial,
    coeff_twoSidedJensenPolynomial (invPochhammerProduct_pos (by simp))]
  simp only [hk, ite_true, invPochhammerProduct, eulerWeight, eulerProduct,
    List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, one_mul,
    affineThetaLeftWeight, affineThetaRightWeight]
  rw [Nat.cast_sub hk, Nat.choose_symm hk]
  ring

/-- The A119308 coefficient ratio has the Euler factor `2n + 2 - k`. -/
theorem polynomial_coeff_ratio (n k : ℕ) (hk : k < n) :
    ((k : ℝ) + 1) * (3 + k) * (2 * n + 2 - k) * (polynomial n).coeff (k + 1) =
      ((n : ℝ) - k) * (n + 1 - k) * (2 * n + 1 - k) * (polynomial n).coeff k := by
  have h := eulerPochhammerPolynomial_coeff_ratio
    (lower := [3]) (upper := [2]) (rising := []) (falling := [(n : ℝ) + 2])
    (by simp) (by simp) (by simpa using (show (0 : ℝ) < n + 2 by positivity)) hk
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    eulerWeight, eulerProduct, one_mul, Nat.cast_sub hk.le,
    Nat.cast_sub (by lia : k + 1 ≤ n), Nat.cast_add, Nat.cast_one] at h
  rw [polynomial_coeff_eq_euler n (k + 1) (by lia), polynomial_coeff_eq_euler n k hk.le]
  linear_combination ((n + 1).factorial / 2 : ℝ) * h

/-- The common Euler-Pochhammer coefficient certificate proves A119308 is PF. -/
theorem polynomial_isPF (n : ℕ) : IsPFPolynomial (polynomial n) := by
  apply isPFPolynomial_of_euler_pochhammer_coeff_ratio
    (d := n) (lower := [3]) (upper := [2]) (rising := []) (falling := [(n : ℝ) + 2])
    (by simp) (by simp) (by simp) (by simpa using (show (0 : ℝ) < n + 2 by positivity))
  · exact (natDegree_affineThetaJensenPolynomial n).le
  · rw [polynomial_coeff_eq_euler n 0 (Nat.zero_le n),
      eulerPochhammerPolynomial_coeff (by simp)
        (by simpa using (show (0 : ℝ) < n + 2 by positivity))]
    exact mul_pos (by positivity) (mul_pos
      (eulerWeight_pos (by simp) (by simpa using (show (0 : ℝ) < n + 2 by positivity)) n 0)
      (pochhammerJensenPolynomial_coeff_pos (by simp) (by simp) (Nat.zero_le n)))
  · intro k hk
    have h := polynomial_coeff_ratio n k hk
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
      eulerWeight, eulerProduct, one_mul, Nat.cast_sub hk.le,
      Nat.cast_sub (by lia : k + 1 ≤ n), Nat.cast_add, Nat.cast_one]
    linear_combination h

/-- Consecutive A119308 model rows are in directed proper position. -/
theorem polynomial_strictInterl_succ (n : ℕ) :
    StrictInterl (polynomial n) (polynomial (n + 1)) :=
  affineThetaJensenPolynomial_strictInterl_succ n

/-- Consecutive A119308 model rows interlace. -/
theorem polynomial_interlaces (n : ℕ) :
    Interlaces (polynomial n) (polynomial (n + 1)) :=
  (polynomial_strictInterl_succ n).toInterlaces (by
    rw [polynomial, polynomial, natDegree_affineThetaJensenPolynomial,
      natDegree_affineThetaJensenPolynomial])

/-- Every A119308 model row splits over the reals. -/
theorem polynomial_splits (n : ℕ) : (polynomial n).Splits :=
  (polynomial_isPF n).splits

/-- The A119308 model satisfies the downstream lag-three recurrence. -/
theorem polynomial_recurrence (n : ℕ) :
    polynomial (n + 3) =
      nextRow n (polynomial (n + 2)) (polynomial (n + 1)) (polynomial n) := by
  rw [← recurrencePolynomial_eq_polynomial, ← recurrencePolynomial_eq_polynomial,
    ← recurrencePolynomial_eq_polynomial, ← recurrencePolynomial_eq_polynomial]
  rfl

private theorem polynomial_zero : polynomial 0 = 1 := by
  simpa only [recurrencePolynomial] using
    (recurrencePolynomial_eq_polynomial 0).symm

private theorem polynomial_one : polynomial 1 = 2 + X := by
  simpa only [recurrencePolynomial] using
    (recurrencePolynomial_eq_polynomial 1).symm

private theorem polynomial_two : polynomial 2 = 3 + 5 * X + X ^ 2 := by
  simpa only [recurrencePolynomial] using
    (recurrencePolynomial_eq_polynomial 2).symm

/-- Consecutive rows with the A119308 initial rows and update interlace. -/
@[rr_row_model]
theorem interlaces_of_recurrence
    {P : ℕ → ℝ[X]}
    (hzero : P 0 = 1)
    (hone : P 1 = 2 + X)
    (htwo : P 2 = 3 + 5 * X + X ^ 2)
    (hrec : ∀ n : ℕ,
      P (n + 3) = nextRow n (P (n + 2)) (P (n + 1)) (P n))
    (n : ℕ) :
    Interlaces (P n) (P (n + 1)) := by
  have heq := sequence_eq_of_same_lag_three_recurrence nextRow
    (hzero.trans polynomial_zero.symm) (hone.trans polynomial_one.symm)
    (htwo.trans polynomial_two.symm) hrec polynomial_recurrence
  rw [heq n, heq (n + 1)]
  exact polynomial_interlaces n

/-- A sequence with the A119308 initial rows and update has split rows. -/
@[rr_row_model]
theorem splits_of_recurrence
    {P : ℕ → ℝ[X]}
    (hzero : P 0 = 1)
    (hone : P 1 = 2 + X)
    (htwo : P 2 = 3 + 5 * X + X ^ 2)
    (hrec : ∀ n : ℕ,
      P (n + 3) = nextRow n (P (n + 2)) (P (n + 1)) (P n))
    (n : ℕ) :
    (P n).Splits := by
  exact (interlaces_of_recurrence hzero hone htwo hrec n).2.1.2

/-- The downstream A119308 recurrence rows interlace. -/
theorem A119308_interlaces (n : ℕ) :
    RealRooted.Interlaces (recurrencePolynomial n) (recurrencePolynomial (n + 1)) := by
  rw [recurrencePolynomial_eq_polynomial, recurrencePolynomial_eq_polynomial]
  exact polynomial_interlaces n

/-- Every downstream A119308 recurrence row splits over the reals. -/
theorem A119308_splits (n : ℕ) : (recurrencePolynomial n).Splits := by
  rw [recurrencePolynomial_eq_polynomial]
  exact polynomial_splits n

/-- Every downstream A119308 recurrence row is nonzero. -/
theorem A119308_ne_zero (n : ℕ) : (recurrencePolynomial n) ≠ 0 :=
  (A119308_interlaces n).2.1.1

/-- Consecutive downstream A119308 recurrence rows are in directed proper position. -/
theorem A119308_prec (n : ℕ) :
    RealRooted.StrictInterl (recurrencePolynomial n) (recurrencePolynomial (n + 1)) := by
  rw [recurrencePolynomial_eq_polynomial, recurrencePolynomial_eq_polynomial]
  exact polynomial_strictInterl_succ n

end RealRooted.Applications.OEIS.A119308
