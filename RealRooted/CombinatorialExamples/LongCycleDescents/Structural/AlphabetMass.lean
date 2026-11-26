/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import RealRooted.CombinatorialExamples.LongCycleDescents.Structural.AlphabetLeading
import Mathlib.Tactic

/-!
# Bounds for the leading alphabet mass

The leading coefficient is the probability of the cycle-length restriction.
Its positive recurrence gives the factor-two comparison needed for the
uniform kernel estimate.

Adapted from Bowen Zuo, cycle-minimum-descent-real-roots v1.0.0 (Apache-2.0)
-/

public section

noncomputable section

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
