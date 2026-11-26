/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic

/-!
# Finite convolution estimates

These bounds use finite sums only. They give the exponential majorant needed
for an Euler recurrence without analytic limits or an exponential function.
-/

public section

open Finset

namespace RealRooted.IntervalDifferential

/-- A nonnegative truncated convolution has mass at most the product of the
truncated masses. -/
theorem sum_convolution_le (a b : ℕ → ℚ) (ha : ∀ i, 0 ≤ a i)
    (hb : ∀ i, 0 ≤ b i) (N : ℕ) :
    (∑ n ∈ range N, ∑ i ∈ range (n + 1), a i * b (n - i)) ≤
      (∑ i ∈ range N, a i) * ∑ j ∈ range N, b j := by
  have hs := sum_Ico_Ico_comm 0 N (fun i n => a i * b (n - i))
  simp only [Nat.Ico_zero_eq_range] at hs
  rw [← hs, sum_mul]
  apply sum_le_sum
  intro i hi
  rw [sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel_left, ← mul_sum]
  apply mul_le_mul_of_nonneg_left _ (ha i)
  exact sum_le_sum_of_subset_of_nonneg (range_mono (Nat.sub_le N i)) (fun j _ _ => hb j)

private theorem euler_convolution_le (u b : ℕ → ℚ) (hu : ∀ i, 0 ≤ u i)
    (hb : ∀ i, 0 ≤ b i) {n : ℕ} (hn : n ≠ 0)
    (he : (n : ℚ) * b n ≤ ∑ i ∈ range n, u (n - i) * b i) :
    b n ≤ ∑ i ∈ range (n + 1), (u i / (i : ℚ)) * b (n - i) := by
  have hnq : (0 : ℚ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  apply (mul_le_mul_iff_right₀ hnq).mp
  apply he.trans
  rw [sum_range_succ']
  simp only [Nat.cast_zero, div_zero, zero_mul, add_zero, mul_sum]
  rw [← sum_range_reflect (fun i => u (n - i) * b i) n]
  apply sum_le_sum
  intro i hi
  have hin := mem_range.mp hi
  rw [show n - (n - 1 - i) = i + 1 by lia,
    show n - 1 - i = n - (i + 1) by lia]
  have hp : (0 : ℚ) < ((i + 1 : ℕ) : ℚ) := by positivity
  have hl : ((i + 1 : ℕ) : ℚ) ≤ n := by exact_mod_cast (show i + 1 ≤ n by lia)
  have hx := mul_le_mul_of_nonneg_right hl (hu (i + 1))
  have hh : u (i + 1) ≤ (n : ℚ) * u (i + 1) / ((i + 1 : ℕ) : ℚ) :=
    (le_div_iff₀ hp).mpr (by simpa only [mul_comm] using hx)
  calc
    _ ≤ ((n : ℚ) * u (i + 1) / ((i + 1 : ℕ) : ℚ)) * b (n - (i + 1)) :=
      mul_le_mul_of_nonneg_right hh (hb _)
    _ = _ := by ring

/-- A finite Euler recurrence has bounded total mass when its logarithmic
kernel mass is less than one. -/
theorem sum_euler_bound (u b : ℕ → ℚ) (hu : ∀ i, 0 ≤ u i)
    (hb : ∀ i, 0 ≤ b i) (h0 : b 0 = 1)
    (he : ∀ (n : ℕ), n ≠ 0 → (n : ℚ) * b n ≤ ∑ i ∈ range n, u (n - i) * b i)
    {c : ℚ} (hc : c < 1) (hm : ∀ N, ∑ i ∈ range N, u i / (i : ℚ) ≤ c) (N : ℕ) :
    ∑ i ∈ range N, b i ≤ 1 / (1 - c) := by
  have hcn : 0 ≤ c := by simpa using hm 0
  by_cases hN : N = 0
  · simp [hN, hc.le]
  · have hpoint (n : ℕ) : b n ≤ (if n = 0 then 1 else 0) +
        ∑ i ∈ range (n + 1), (u i / (i : ℚ)) * b (n - i) := by
      by_cases hn : n = 0
      · simp [hn, h0]
      · simpa only [ite_eq_right hn, zero_add] using
          euler_convolution_le u b hu hb hn (he n hn)
    have hs := sum_le_sum (s := range N) (fun i _ => hpoint i)
    rw [sum_add_distrib] at hs
    have hz : (∑ i ∈ range N, if i = 0 then (1 : ℚ) else 0) = 1 := by
      simp [Nat.pos_of_ne_zero hN]
    rw [hz] at hs
    have ht := sum_convolution_le (fun i => u i / (i : ℚ)) b
      (fun i => div_nonneg (hu i) (Nat.cast_nonneg i)) hb N
    have hmass : 0 ≤ ∑ i ∈ range N, b i := sum_nonneg (fun i _ => hb i)
    have hm' := mul_le_mul_of_nonneg_right (hm N) hmass
    apply (le_div_iff₀ (sub_pos.mpr hc)).mpr
    nlinarith

/-- The index times an Euler coefficient has a uniform bound from the kernel
peak and total logarithmic mass. -/
theorem index_mul_euler_bound (u b : ℕ → ℚ) (hu : ∀ i, 0 ≤ u i)
    (hb : ∀ i, 0 ≤ b i) (h0 : b 0 = 1)
    (he : ∀ (n : ℕ), n ≠ 0 → (n : ℚ) * b n ≤ ∑ i ∈ range n, u (n - i) * b i)
    {c U : ℚ} (hc : c < 1) (hm : ∀ N, ∑ i ∈ range N, u i / (i : ℚ) ≤ c)
    (hU : ∀ i, u i ≤ U) (n : ℕ) : (n : ℚ) * b n ≤ U / (1 - c) := by
  have hUn : 0 ≤ U := (hu 0).trans (hU 0)
  by_cases hn : n = 0
  · simp [hn, div_nonneg hUn (sub_nonneg.mpr hc.le)]
  · calc
      _ ≤ ∑ i ∈ range n, u (n - i) * b i := he n hn
      _ ≤ ∑ i ∈ range n, U * b i :=
        sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (hU _) (hb i))
      _ = U * ∑ i ∈ range n, b i := (mul_sum ..).symm
      _ ≤ _ := by
        simpa only [div_eq_mul_inv, one_mul] using
          mul_le_mul_of_nonneg_left (sum_euler_bound u b hu hb h0 he hc hm n) hUn

/-- The factor-two leading-mass comparison turns the Euler bounds into strict
coefficient dominance. The constants give relative error at most `64/85`. -/
theorem convolution_lt_of_factor_two (p b : ℕ → ℚ) (hb : ∀ i, 0 ≤ b i)
    (hp0 : p 0 = 1) (hb0 : b 0 = 1) {n : ℕ} (hn : 0 < n)
    (hpn : 0 < p n) (hnp : 1 ≤ (n : ℚ) * p n)
    (hr : ∀ i ∈ Ico 1 n, p i ≤ 2 * p n)
    (hm : ∑ i ∈ range n, b i ≤ 20 / 17)
    (hi : (n : ℚ) * b n ≤ 2 / 5) :
    (∑ i ∈ range n, p i * b (n - i)) < p n := by
  have hbn : b n ≤ 2 / 5 * p n := by
    have ht := mul_le_mul_of_nonneg_right hnp (hb n)
    have hs := mul_le_mul_of_nonneg_left hi hpn.le
    nlinarith
  have hmass : (∑ i ∈ Ico 1 n, b i) ≤ 3 / 17 := by
    rw [← sum_range_add_sum_Ico _ (show 1 ≤ n by lia)] at hm
    simp only [sum_range_one, hb0] at hm
    linarith
  have hrest : (∑ i ∈ Ico 1 n, p i * b (n - i)) ≤
      2 * p n * (3 / 17) := by
    calc
      _ ≤ ∑ i ∈ Ico 1 n, (2 * p n) * b (n - i) :=
        sum_le_sum (fun i hi => mul_le_mul_of_nonneg_right (hr i hi) (hb _))
      _ = (2 * p n) * ∑ i ∈ Ico 1 n, b i := by
        rw [← mul_sum, sum_Ico_reflect b 1 (m := n) (n := n) (by lia)]
        simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hmass (by positivity)
  rw [← sum_range_add_sum_Ico _ (show 1 ≤ n by lia)]
  simp only [sum_range_one, hp0, Nat.sub_zero, one_mul]
  nlinarith

end RealRooted.IntervalDifferential
