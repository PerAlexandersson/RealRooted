/-
Copyright (c) 2026 Bowen Zuo and Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bowen Zuo, Per Alexandersson
-/
module

import Mathlib.Analysis.Complex.Polynomial.Basic
public import RealRooted.CombinatorialExamples.LongCycleDescents.Structural.AlphabetRecurrence
import RealRooted.CombinatorialExamples.LongCycleDescents.Structural.AlphabetTransform
import RealRooted.RootVieta.Newton
import Mathlib.Tactic

/-!
# Leading alphabet coefficients and mass

The first three coefficients give the signs in Newton's second identity. The leading
mass lies between half the reciprocal cutoff and the reciprocal cutoff. Removing
the three alphabet factors subtracts two from the second root power sum.

Adapted from Bowen Zuo, cycle-minimum-descent-real-roots v1.0.0 (Apache-2.0).
-/

public noncomputable section

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

open Polynomial Finset

namespace RealRooted.LongCycleDescents.Structural

private theorem mass_equation (k : ℕ) {n : ℕ} (hn : n ≠ 0) :
    (n : ℚ) * (lossRow k n).coeff 0 = ∑ i ∈ range n,
      (if k ≤ n - i ∧ n - i ≠ 0 then (1 : ℚ) else 0) * (lossRow k i).coeff 0 := by
  have he := congrArg (fun p : ℚ[X] => p.coeff 0) (lossRow_equation k hn)
  simpa only [← C_eq_natCast, finsetSum_coeff, mul_coeff_zero, coeff_C_zero,
    coeff_lossKernel_zero] using he

/-- The leading mass vanishes below the positive cutoff. -/
theorem coeff_lossRow_zero_eq_zero {n k : ℕ} (hn : 0 < n) (hk : n < k) :
    (lossRow k n).coeff 0 = 0 := by
  have he := mass_equation k hn.ne'
  have hz : (∑ i ∈ range n,
      (if k ≤ n - i ∧ n - i ≠ 0 then (1 : ℚ) else 0) * (lossRow k i).coeff 0) = 0 := by
    apply sum_eq_zero
    intro i _
    rw [ite_eq_right (by lia), zero_mul]
  rw [hz] at he
  exact (mul_eq_zero.mp he).resolve_left (by exact_mod_cast hn.ne')

/-- The leading-mass recurrence with zero terms removed. -/
theorem coeff_lossRow_zero_equation {n k : ℕ} (hk : 0 < k) (hkn : k ≤ n) :
    (n : ℚ) * (lossRow k n).coeff 0 =
      ∑ i ∈ range (n - k + 1), (lossRow k i).coeff 0 := by
  rw [mass_equation k (by lia)]
  symm
  calc
    _ = ∑ i ∈ range (n - k + 1),
        (if k ≤ n - i ∧ n - i ≠ 0 then (1 : ℚ) else 0) * (lossRow k i).coeff 0 := by
      apply sum_congr rfl
      intro i hi
      rw [ite_eq_left (by have := mem_range.mp hi; constructor <;> lia), one_mul]
    _ = _ := sum_subset (range_mono (by lia : n - k + 1 ≤ n)) (by
      intro i hi hin
      rw [ite_eq_right (by
        have := mem_range.mp hi
        have := not_lt.mp (fun h => hin (mem_range.mpr h))
        lia), zero_mul])

/-- At every positive size the leading mass is at most the reciprocal cutoff. -/
theorem coeff_lossRow_zero_le {k : ℕ} (hk : 3 ≤ k) {n : ℕ} (hn : 0 < n) :
    (lossRow k n).coeff 0 ≤ 1 / (k : ℚ) := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    by_cases hkn : k ≤ n
    · have he := coeff_lossRow_zero_equation (by lia : 0 < k) hkn
      have hb : (∑ i ∈ range (n - k + 1), (lossRow k i).coeff 0) ≤
          1 + (n - k : ℕ) * (1 / (k : ℚ)) := by
        rw [sum_range_succ']
        have hz : (lossRow k 0).coeff 0 = 1 := by
          rw [lossRow_zero]
          simp only [coeff_one]
          norm_num
        rw [hz]
        have ht : (∑ i ∈ range (n - k), (lossRow k (i + 1)).coeff 0) ≤
            ∑ _i ∈ range (n - k), 1 / (k : ℚ) := by
          exact sum_le_sum fun i hi => ih (i + 1) (by have := mem_range.mp hi; lia)
            (Nat.succ_pos _)
        simpa only [sum_const, card_range, nsmul_eq_mul, add_comm] using add_le_add_left ht 1
      have hkq : (0 : ℚ) < k := by exact_mod_cast (show 0 < k by lia)
      have hnq : (0 : ℚ) < n := by exact_mod_cast hn
      rw [← he, Nat.cast_sub hkn] at hb
      apply (mul_le_mul_iff_right₀ hnq).mp
      simp only [one_div] at hb ⊢
      nlinarith [mul_inv_cancel₀ hkq.ne']
    · rw [coeff_lossRow_zero_eq_zero hn (by lia)]
      positivity

/-- At an allowed size the leading mass is at least half the reciprocal cutoff. -/
theorem one_div_two_mul_le_coeff_lossRow_zero {n k : ℕ} (hk : 3 ≤ k) (hkn : k ≤ n) :
    1 / (2 * (k : ℚ)) ≤ (lossRow k n).coeff 0 := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    have he := coeff_lossRow_zero_equation (by lia : 0 < k) hkn
    have hkq : (0 : ℚ) < k := by exact_mod_cast (show 0 < k by lia)
    have hnq : (0 : ℚ) < n := by exact_mod_cast (show 0 < n by lia)
    by_cases hn2 : n < 2 * k
    · have hh : 1 ≤ ∑ i ∈ range (n - k + 1), (lossRow k i).coeff 0 := by
        have ht := single_le_sum (f := fun i => (lossRow k i).coeff 0)
          (fun i _ => (lossRow_leading_signs hk i).1)
          (mem_range.mpr (by lia) : 0 ∈ range (n - k + 1))
        simpa using ht
      rw [← he] at hh
      have hn2q : (n : ℚ) ≤ 2 * k := by exact_mod_cast hn2.le
      apply (div_le_iff₀ (by positivity : (0 : ℚ) < 2 * k)).mpr
      nlinarith [mul_nonneg (sub_nonneg.mpr hn2q) (lossRow_leading_signs hk n).1]
    · have hkr : k ≤ n - k + 1 := by lia
      have hz : (∑ i ∈ range k, (lossRow k i).coeff 0) = 1 := by
        rw [sum_eq_single 0]
        · simp
        · intro i hi hi0
          exact coeff_lossRow_zero_eq_zero (Nat.pos_of_ne_zero hi0) (mem_range.mp hi)
        · intro ht
          exact (ht (mem_range.mpr (by lia))).elim
      have hb : (∑ i ∈ Ico k (n - k + 1), 1 / (2 * (k : ℚ))) ≤
          ∑ i ∈ Ico k (n - k + 1), (lossRow k i).coeff 0 := by
        apply sum_le_sum
        intro i hi
        exact ih i (by have := mem_Ico.mp hi; lia) (mem_Ico.mp hi).1
      rw [← sum_range_add_sum_Ico _ hkr, hz] at he
      simp only [sum_const, Nat.card_Ico, nsmul_eq_mul] at hb
      have hcard : (n - k + 1 - k : ℕ) = n - 2 * k + 1 := by lia
      rw [hcard, Nat.cast_add, Nat.cast_sub (by lia : 2 * k ≤ n), Nat.cast_mul,
        Nat.cast_ofNat, Nat.cast_one] at hb
      apply (div_le_iff₀ (by positivity : (0 : ℚ) < 2 * k)).mpr
      have he' := congrArg (fun x : ℚ => 2 * k * x) he
      have hi2 : (2 * (k : ℚ)) * (2 * (k : ℚ))⁻¹ = 1 := mul_inv_cancel₀ (by positivity)
      have ht := mul_le_mul_of_nonneg_left hb (by positivity : (0 : ℚ) ≤ 2 * k)
      rw [one_div] at ht
      nlinarith

end RealRooted.LongCycleDescents.Structural

open Polynomial Finset

namespace RealRooted.LongCycleDescents.Structural

private theorem second_powerSum_nonneg {p : ℝ[X]} {n : ℕ} (hn : 2 ≤ n)
    (hd : p.natDegree ≤ n) (h0 : 0 < p.coeff n)
    (h1 : p.coeff (n - 1) = 0) (h2 : p.coeff (n - 2) ≤ 0) :
    0 ≤ (((p.map (algebraMap ℝ ℂ)).roots).map fun z => (z ^ 2).re).sum := by
  let f := p.map (algebraMap ℝ ℂ)
  have hpn : p ≠ 0 := by intro he; simp [he] at h0
  have hfn : f ≠ 0 := Polynomial.map_ne_zero hpn
  have hdeg : p.natDegree = n := hd.antisymm (le_natDegree_of_ne_zero h0.ne')
  have hfdeg : f.natDegree = n := by simpa [f] using hdeg
  have he := RootVieta.leadingCoeff_mul_roots_powerSum (IsAlgClosed.splits f) hfn
    2 (by decide) (by lia)
  have ha : (Finset.HasAntidiagonal.antidiagonal 2).filter
      (fun a : ℕ × ℕ => a.1 ∈ Set.Ioo 0 2) = {(1, 1)} := by decide
  rw [ha] at he
  simp only [sum_singleton, hfdeg] at he
  have hl : p.leadingCoeff = p.coeff n := by rw [leadingCoeff, hdeg]
  simp only [f, coeff_map, leadingCoeff_map, hl, h1, map_zero, zero_mul, sub_zero,
    Complex.coe_algebraMap] at he
  have hr := congrArg Complex.re he
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero, Complex.neg_re] at hr
  simp only [Complex.natCast_re, mul_zero, sub_zero] at hr
  have hs : Complex.re ((f.roots.map fun z => z ^ 2).sum) =
      ((f.roots.map fun z => (z ^ 2).re).sum) := by
    exact (map_multiset_sum Complex.reAddGroupHom _).trans (by simp)
  change p.coeff n * Complex.re ((f.roots.map fun z => z ^ 2).sum) = _ at hr
  rw [hs] at hr
  change 0 ≤ ((f.roots.map fun z => (z ^ 2).re).sum)
  nlinarith

/-- The second power sum of every actual long-cutoff alphabet is nonnegative. -/
theorem descentAlphabetPolynomial_second_powerSum_nonneg {n k : ℕ}
    (hk : 3 ≤ k) (hkn : k ≤ n) :
    0 ≤ ((((descentAlphabetPolynomial n k).map (algebraMap ℝ ℂ)).roots).map
      fun z => (z ^ 2).re).sum := by
  have hs := descentAlphabetPolynomial_leading_signs (by lia : 2 ≤ n) hk hkn
  exact second_powerSum_nonneg (by lia) (natDegree_descentAlphabetPolynomial_le n k)
    hs.1 hs.2.1 hs.2.2

/-- All nonzero nonnegative sums of long-cutoff alphabets have the same
leading-coefficient signs. -/
theorem sum_descentAlphabetPolynomial_leading_signs {n : ℕ} {s : Finset ℕ}
    (hs : ∀ k ∈ s, 3 ≤ k ∧ k ≤ n) {w : ℕ → ℝ}
    (hw : ∀ k ∈ s, 0 ≤ w k) (hp : ∃ k ∈ s, 0 < w k) :
    let f := ∑ k ∈ s, C (w k) * descentAlphabetPolynomial n k
    f.natDegree = n ∧ 0 < f.coeff n ∧ f.coeff (n - 1) = 0 ∧ f.coeff (n - 2) ≤ 0 := by
  classical
  dsimp only
  have hn : 2 ≤ n := by obtain ⟨k, hk, _⟩ := hp; have := hs k hk; lia
  have hl k hk := descentAlphabetPolynomial_leading_signs hn (hs k hk).1 (hs k hk).2
  have hd : (∑ k ∈ s, C (w k) * descentAlphabetPolynomial n k).natDegree ≤ n := by
    apply natDegree_sum_le_of_forall_le
    intro k _
    exact (natDegree_C_mul_le _ _).trans (natDegree_descentAlphabetPolynomial_le n k)
  have hz : 0 < (∑ k ∈ s, C (w k) * descentAlphabetPolynomial n k).coeff n := by
    simp only [finsetSum_coeff, coeff_C_mul]
    exact sum_pos' (fun k hk => mul_nonneg (hw k hk) (hl k hk).1.le)
      (hp.imp fun k hk => ⟨hk.1, mul_pos hk.2 (hl k hk.1).1⟩)
  refine ⟨hd.antisymm (le_natDegree_of_ne_zero hz.ne'), hz, ?_, ?_⟩
  · simp only [finsetSum_coeff, coeff_C_mul]
    exact sum_eq_zero (fun k hk => by rw [(hl k hk).2.1, mul_zero])
  · simp only [finsetSum_coeff, coeff_C_mul]
    exact sum_nonpos (fun k hk => mul_nonpos_of_nonneg_of_nonpos (hw k hk) (hl k hk).2.2)

/-- The second power sum is nonnegative for every nonzero nonnegative
long-cutoff alphabet mixture. -/
theorem sum_descentAlphabetPolynomial_second_powerSum_nonneg {n : ℕ} {s : Finset ℕ}
    (hs : ∀ k ∈ s, 3 ≤ k ∧ k ≤ n) {w : ℕ → ℝ}
    (hw : ∀ k ∈ s, 0 ≤ w k) (hp : ∃ k ∈ s, 0 < w k) :
    let f := ∑ k ∈ s, C (w k) * descentAlphabetPolynomial n k
    0 ≤ (((f.map (algebraMap ℝ ℂ)).roots).map fun z => (z ^ 2).re).sum := by
  have hn : 2 ≤ n := by obtain ⟨k, hk, _⟩ := hp; have := hs k hk; lia
  have hf := sum_descentAlphabetPolynomial_leading_signs hs hw hp
  exact second_powerSum_nonneg hn hf.1.le hf.2.1 hf.2.2.1 hf.2.2.2

private theorem cubic_second_powerSum :
    (((((X * (X ^ 2 - 1) : ℝ[X]).map (algebraMap ℝ ℂ)).roots).map
      fun z => (z ^ 2).re).sum) = 2 := by
  have hf : (X * (X ^ 2 - 1) : ℂ[X]) = X * ((X - C 1) * (X - C (-1))) := by
    simp only [map_neg, map_one]
    ring
  simp only [Polynomial.map_mul, Polynomial.map_X, Polynomial.map_sub,
    Polynomial.map_pow, Polynomial.map_one]
  rw [hf, roots_mul (mul_ne_zero X_ne_zero (mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _))),
    roots_mul (mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _)),
    roots_X, roots_X_sub_C, roots_X_sub_C]
  norm_num

/-- Removing the three alphabet factors subtracts exactly two from the second
power sum. This lemma also applies to nonnegative mixtures. -/
theorem quotient_second_powerSum_ge_neg_two {f Q : ℝ[X]} (hf : f ≠ 0)
    (he : f = X * (X ^ 2 - 1) * Q)
    (hp : 0 ≤ (((f.map (algebraMap ℝ ℂ)).roots).map fun z => (z ^ 2).re).sum) :
    -2 ≤ (((Q.map (algebraMap ℝ ℂ)).roots).map fun z => (z ^ 2).re).sum := by
  have hq : Q ≠ 0 := by intro hh; simp only [hh, mul_zero] at he; exact hf he
  have hm : (X * (X ^ 2 - 1) : ℝ[X]).map (algebraMap ℝ ℂ) *
      Q.map (algebraMap ℝ ℂ) ≠ 0 := by
    rw [← Polynomial.map_mul, ← he]
    exact Polynomial.map_ne_zero hf
  rw [he, Polynomial.map_mul, roots_mul hm,
    Multiset.map_add, Multiset.sum_add, cubic_second_powerSum] at hp
  linarith

/-- The actual alphabet quotient always satisfies the moment hypothesis of the
structural insertion theorem. -/
theorem descentAlphabetPolynomial_quotient_second_powerSum {n k : ℕ}
    (hk : 3 ≤ k) (hkn : k ≤ n) {Q : ℝ[X]}
    (he : descentAlphabetPolynomial n k = X * (X ^ 2 - 1) * Q) :
    -2 ≤ (((Q.map (algebraMap ℝ ℂ)).roots).map fun z => (z ^ 2).re).sum := by
  have hh := (descentAlphabetPolynomial_leading_signs (by lia) hk hkn).1
  exact quotient_second_powerSum_ge_neg_two
    (fun hz => by simp [hz] at hh) he
    (descentAlphabetPolynomial_second_powerSum_nonneg hk hkn)

end RealRooted.LongCycleDescents.Structural
