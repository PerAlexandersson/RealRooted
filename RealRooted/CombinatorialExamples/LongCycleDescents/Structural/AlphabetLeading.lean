/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import RealRooted.CombinatorialExamples.LongCycleDescents.Structural.AlphabetReflection
import Mathlib.Tactic

/-!
# The first three alphabet coefficients

Only the divisors three and two at lengths three and four can contribute a
positive degree loss at most two. In particular every nonnegative long-cutoff
mixture has vanishing next coefficient and nonpositive second next coefficient.

Adapted from Bowen Zuo, cycle-minimum-descent-real-roots v1.0.0 (Apache-2.0)
-/

public section

noncomputable section

open Polynomial Finset
open scoped ArithmeticFunction.Moebius

namespace RealRooted.LongCycleDescents.Structural

private theorem small_loss {i j d h : ℕ} (hj : 3 ≤ j) (hi : j ≤ i)
    (hji : j ∣ i) (hd : d ∣ j) (hh : h ≤ 2) (he : i - j / d = h) :
    (i = j ∧ d = 1 ∧ h = 0) ∨ i ≤ 4 := by
  have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hd (by lia)
  have hq : j / d ≤ i := (Nat.div_le_self _ _).trans hi
  have heq : i = j / d + h := by lia
  have hjq := Nat.div_mul_cancel hd
  by_cases hd1 : d = 1
  · have hid : i = j + h := by simpa [hd1] using heq
    have hdiv : j ∣ h := by
      rw [← he, hd1, Nat.div_one]
      exact Nat.dvd_sub hji dvd_rfl
    have hz := Nat.eq_zero_of_dvd_of_lt hdiv (by lia)
    exact Or.inl ⟨by lia, hd1, hz⟩
  · have hd2 : 2 ≤ d := by lia
    have ht : j / d * 2 ≤ j / d * d := Nat.mul_le_mul_left _ hd2
    exact Or.inr (by nlinarith)

private theorem zero_loss {i j d : ℕ} (hj : 0 < j) (hi : j ≤ i)
    (hd : d ∣ j) (he : i - j / d = 0) : i = j ∧ d = 1 := by
  have hq : j / d ≤ j := Nat.div_le_self _ _
  have heq : i = j := by lia
  have hdiv : j / d = j := by lia
  have hm := Nat.div_mul_cancel hd
  rw [hdiv] at hm
  exact ⟨heq, by nlinarith⟩

private theorem coeff_lossKernel (k i h : ℕ) :
    (lossKernel k i).coeff h = ∑ j ∈ range i,
      if k ≤ j + 1 ∧ j + 1 ∣ i then
        ∑ d ∈ (j + 1).divisors,
          if i - (j + 1) / d = h then (μ d : ℚ) else 0 else 0 := by
  simp only [lossKernel, finsetSum_coeff, apply_ite (fun p : ℚ[X] => p.coeff h),
    coeff_zero, coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero, eq_comm]

/-- The constant kernel coefficient is exactly the permitted-length indicator. -/
theorem coeff_lossKernel_zero (k i : ℕ) :
    (lossKernel k i).coeff 0 = if k ≤ i ∧ i ≠ 0 then 1 else 0 := by
  rw [coeff_lossKernel]
  by_cases hi : i = 0
  · simp [hi]
  · have hip : 0 < i := Nat.pos_of_ne_zero hi
    rw [sum_eq_single (i - 1)]
    · rw [Nat.sub_add_cancel (by lia : 1 ≤ i)]
      simp only [dvd_refl, and_true]
      by_cases hk : k ≤ i
      · rw [ite_eq_left hk, ite_eq_left ⟨hk, hi⟩, sum_eq_single 1]
        · simp
        · intro d hd hd1
          apply ite_eq_right
          intro he
          exact hd1 (zero_loss hip le_rfl (Nat.dvd_of_mem_divisors hd) he).2
        · simp [hi]
      · simp [hk]
    · intro j hj hji
      by_cases hk : k ≤ j + 1 ∧ j + 1 ∣ i
      · rw [ite_eq_left hk]
        apply sum_eq_zero
        intro d hd
        apply ite_eq_right
        intro he
        have hz := (zero_loss (Nat.succ_pos j) (by simpa using mem_range.mp hj)
          (Nat.dvd_of_mem_divisors hd) he).1
        lia
      · simp [hk]
    · intro hn
      exact (hn (mem_range.mpr (by lia))).elim

private theorem coeff_lossKernel_small_eq_zero {i k h : ℕ} (hi : 5 ≤ i)
    (hk : 3 ≤ k) (hh : h = 1 ∨ h = 2) : (lossKernel k i).coeff h = 0 := by
  rw [coeff_lossKernel]
  apply sum_eq_zero
  intro j hj
  by_cases hc : k ≤ j + 1 ∧ j + 1 ∣ i
  · rw [ite_eq_left hc]
    apply sum_eq_zero
    intro d hd
    apply ite_eq_right
    intro he
    have ht := small_loss (by lia : 3 ≤ j + 1) (by simpa using mem_range.mp hj)
      hc.2 (Nat.dvd_of_mem_divisors hd) (by rcases hh with rfl | rfl <;> decide) he
    rcases ht with ⟨_, _, hz⟩ | ht <;> lia
  · simp [hc]

/-- The coefficient of degree loss one vanishes. -/
theorem coeff_lossKernel_one {k : ℕ} (hk : 3 ≤ k) (i : ℕ) :
    (lossKernel k i).coeff 1 = 0 := by
  by_cases hi : 5 ≤ i
  · exact coeff_lossKernel_small_eq_zero hi hk (Or.inl rfl)
  · have hit : i ≤ 4 := by lia
    by_cases hki : k ≤ 4
    · rw [coeff_lossKernel]
      interval_cases i <;> interval_cases k <;>
        norm_num [sum_range_succ,
          show (3 : ℕ).divisors = {1, 3} from by decide +kernel,
          show (4 : ℕ).divisors = {1, 2, 4} from by decide +kernel,
          ArithmeticFunction.moebius_apply_prime (by decide : Nat.Prime 2),
          ArithmeticFunction.moebius_apply_prime (by decide : Nat.Prime 3)]
    · have he : lossKernel k i = 0 := by
        apply sum_eq_zero
        intro j hj
        exact ite_eq_right (by have := mem_range.mp hj; lia)
      rw [he, coeff_zero]

/-- The coefficient of degree loss two is nonpositive. -/
theorem coeff_lossKernel_two_nonpos {k : ℕ} (hk : 3 ≤ k) (i : ℕ) :
    (lossKernel k i).coeff 2 ≤ 0 := by
  by_cases hi : 5 ≤ i
  · rw [coeff_lossKernel_small_eq_zero hi hk (Or.inr rfl)]
  · have hit : i ≤ 4 := by lia
    by_cases hki : k ≤ 4
    · rw [coeff_lossKernel]
      interval_cases i <;> interval_cases k <;>
        norm_num [sum_range_succ,
          show (3 : ℕ).divisors = {1, 3} from by decide +kernel,
          show (4 : ℕ).divisors = {1, 2, 4} from by decide +kernel,
          ArithmeticFunction.moebius_apply_prime (by decide : Nat.Prime 2),
          ArithmeticFunction.moebius_apply_prime (by decide : Nat.Prime 3)]
    · have he : lossKernel k i = 0 := by
        apply sum_eq_zero
        intro j hj
        exact ite_eq_right (by have := mem_range.mp hj; lia)
      rw [he, coeff_zero]

private theorem mul_coeff_two (p q : ℚ[X]) :
    (p * q).coeff 2 = p.coeff 0 * q.coeff 2 + p.coeff 1 * q.coeff 1 +
      p.coeff 2 * q.coeff 0 := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num [sum_range_succ]

/-- The leading three alphabet coefficients satisfy the signs required by
Newton's second identity, at every size and every long cutoff. -/
theorem lossRow_leading_signs {k : ℕ} (hk : 3 ≤ k) (n : ℕ) :
    0 ≤ (lossRow k n).coeff 0 ∧ (lossRow k n).coeff 1 = 0 ∧
      (lossRow k n).coeff 2 ≤ 0 := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    by_cases hn : n = 0
    · rw [hn, lossRow_zero]
      simp only [coeff_one]
      norm_num
    · have he (h : ℕ) := congrArg (fun p : ℚ[X] => p.coeff h) (lossRow_equation k hn)
      simp only [← C_eq_natCast, coeff_C_mul, finsetSum_coeff] at he
      have hnq : (0 : ℚ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
      have h0 : 0 ≤ (lossRow k n).coeff 0 := by
        have hh : 0 ≤ ∑ i ∈ range n,
            (lossKernel k (n - i) * lossRow k i).coeff 0 := by
          apply sum_nonneg
          intro i hi
          rw [mul_coeff_zero, coeff_lossKernel_zero]
          exact mul_nonneg (by split_ifs <;> norm_num) (ih i (mem_range.mp hi)).1
        rw [← he 0] at hh
        exact nonneg_of_mul_nonneg_right hh hnq
      have h1 : (lossRow k n).coeff 1 = 0 := by
        have hh : (∑ i ∈ range n,
            (lossKernel k (n - i) * lossRow k i).coeff 1) = 0 := by
          apply sum_eq_zero
          intro i hi
          rw [mul_coeff_one, coeff_lossKernel_one hk, (ih i (mem_range.mp hi)).2.1]
          ring
        rw [← he 1] at hh
        exact (mul_eq_zero.mp hh).resolve_left hnq.ne'
      refine ⟨h0, h1, ?_⟩
      have hh : (∑ i ∈ range n,
          (lossKernel k (n - i) * lossRow k i).coeff 2) ≤ 0 := by
        apply sum_nonpos
        intro i hi
        rw [mul_coeff_two, coeff_lossKernel_one hk, zero_mul, add_zero]
        apply add_nonpos
        · rw [coeff_lossKernel_zero]
          exact mul_nonpos_of_nonneg_of_nonpos (by split_ifs <;> norm_num)
            (ih i (mem_range.mp hi)).2.2
        · exact mul_nonpos_of_nonpos_of_nonneg (coeff_lossKernel_two_nonpos hk _)
            (ih i (mem_range.mp hi)).1
      rw [← he 2] at hh
      exact nonpos_of_mul_nonpos_right hh hnq

/-- The leading mass includes the contribution of the single full cycle. -/
theorem one_le_mul_coeff_lossRow_zero {n k : ℕ} (hk : 3 ≤ k) (hkn : k ≤ n) :
    1 ≤ (n : ℚ) * (lossRow k n).coeff 0 := by
  have hn : n ≠ 0 := by lia
  have he := congrArg (fun p : ℚ[X] => p.coeff 0) (lossRow_equation k hn)
  simp only [← C_eq_natCast, finsetSum_coeff, mul_coeff_zero,
    coeff_C_zero, coeff_lossKernel_zero] at he
  have hb : 1 ≤ ∑ i ∈ range n,
      (if k ≤ n - i ∧ n - i ≠ 0 then (1 : ℚ) else 0) * (lossRow k i).coeff 0 := by
    have hh := single_le_sum (f := fun i =>
      (if k ≤ n - i ∧ n - i ≠ 0 then (1 : ℚ) else 0) * (lossRow k i).coeff 0)
      (fun i _ => mul_nonneg (by split_ifs <;> norm_num) (lossRow_leading_signs hk i).1)
      (mem_range.mpr (Nat.pos_of_ne_zero hn) : 0 ∈ range n)
    simpa [hkn, hn] using hh
  rw [← he] at hb
  exact hb

/-- The leading alphabet coefficient is strictly positive for an allowed long cutoff. -/
theorem coeff_lossRow_zero_pos {n k : ℕ} (hk : 3 ≤ k) (hkn : k ≤ n) :
    0 < (lossRow k n).coeff 0 := by
  have hb := one_le_mul_coeff_lossRow_zero hk hkn
  have hnq : (0 : ℚ) < n := by exact_mod_cast (show 0 < n by lia)
  nlinarith

/-- The same first-three-coefficient signs hold for the original real alphabet. -/
theorem descentAlphabetPolynomial_leading_signs {n k : ℕ} (hn : 2 ≤ n)
    (hk : 3 ≤ k) (hkn : k ≤ n) :
    0 < (descentAlphabetPolynomial n k).coeff n ∧
      (descentAlphabetPolynomial n k).coeff (n - 1) = 0 ∧
      (descentAlphabetPolynomial n k).coeff (n - 2) ≤ 0 := by
  have h0 := coeff_lossRow_zero_pos hk hkn
  have hs := lossRow_leading_signs hk n
  have he (i : ℕ) (hi : i ≤ n) :
      ((lossRow k n).coeff i : ℝ) = (descentAlphabetPolynomial n k).coeff (n - i) := by
    rw [lossRow, coeff_reflect, revAt_le hi, ← map_alphabetRow (by lia : 0 < n), coeff_map]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · have hh : (0 : ℝ) < ((lossRow k n).coeff 0 : ℝ) := by exact_mod_cast h0
    simpa only [he 0 (by lia), Nat.sub_zero] using hh
  · have hh : ((lossRow k n).coeff 1 : ℝ) = 0 := by exact_mod_cast hs.2.1
    rwa [he 1 (by lia)] at hh
  · have hh : ((lossRow k n).coeff 2 : ℝ) ≤ 0 := by exact_mod_cast hs.2.2
    rwa [he 2 hn] at hh

end RealRooted.LongCycleDescents.Structural
