/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Tactic

/-!
# Rational divisor majorants

For cutoffs at least thirteen we may replace every Möbius coefficient by one.
This slightly weaker majorant avoids computing Möbius values in its certificates.
Its tail is bounded by a geometric series with rational ratio `23/25`.

Adapted from Bowen Zuo, cycle-minimum-descent-real-roots v1.0.0 (Apache-2.0)
-/

@[expose] public section

open Finset

namespace RealRooted.LongCycleDescents.Structural

/-- Absolute degree-loss majorant for the length-divisor kernel at cutoff thirteen. -/
def divisorMajorant (i : ℕ) : ℚ :=
  ∑ j ∈ range i, if 13 ≤ j + 1 ∧ j + 1 ∣ i then
    ∑ d ∈ range (j + 1), if d + 1 ∣ j + 1 ∧ (j + 1) / (d + 1) < i then
      (4 / 5 : ℚ) ^ (i - (j + 1) / (d + 1)) else 0 else 0

/-- A rational geometric budget for all indices beyond 160. -/
def divisorTailBudget : ℚ := (161 : ℚ) ^ 2 * (9 / 10) ^ 161 / (1 - 23 / 25)

/-- The majorant coefficients are nonnegative. -/
theorem divisorMajorant_nonneg (i : ℕ) : 0 ≤ divisorMajorant i := by
  apply sum_nonneg
  intro j _
  split_ifs
  · apply sum_nonneg
    intro d _
    split_ifs <;> positivity
  · exact le_rfl

private theorem positive_loss_double {i j d : ℕ} (hi : j ≤ i)
    (hji : j ∣ i) (hd : 0 < d) (hdj : d ∣ j) (hq : j / d < i) :
    i ≤ 2 * (i - j / d) := by
  have hqj : j / d ≤ j := Nat.div_le_self _ _
  have hmul := Nat.div_mul_cancel hdj
  by_cases hd1 : d = 1
  · simp only [hd1, Nat.div_one] at hq ⊢
    obtain ⟨b, hb⟩ := hji
    have hb2 : 2 ≤ b := by
      by_contra hn
      interval_cases b <;> simp_all
    have ht := Nat.mul_le_mul_left j hb2
    lia
  · have ht := Nat.mul_le_mul_left (j / d) (show 2 ≤ d by lia)
    have hle : j / d ≤ i := hqj.trans hi
    lia

/-- A simple exponential envelope for every divisor majorant coefficient. -/
theorem divisorMajorant_le (i : ℕ) :
    divisorMajorant i ≤ (i : ℚ) ^ 2 * (9 / 10) ^ i := by
  have term {j d : ℕ} (hj : j ∈ range i) (hd : d ∈ range (j + 1))
      (hji : j + 1 ∣ i) (hdj : d + 1 ∣ j + 1)
      (hl : (j + 1) / (d + 1) < i) :
      (4 / 5 : ℚ) ^ (i - (j + 1) / (d + 1)) ≤ (9 / 10 : ℚ) ^ i := by
    have he := positive_loss_double (by simpa using mem_range.mp hj)
      hji (Nat.succ_pos _) hdj hl
    calc
      _ ≤ ((9 / 10 : ℚ) ^ 2) ^ (i - (j + 1) / (d + 1)) := by
        gcongr; norm_num
      _ = (9 / 10 : ℚ) ^ (2 * (i - (j + 1) / (d + 1))) := by rw [pow_mul]
      _ ≤ (9 / 10 : ℚ) ^ i := pow_le_pow_of_le_one (by norm_num) (by norm_num) he
  calc
    divisorMajorant i ≤ ∑ j ∈ range i, ∑ _d ∈ range i, (9 / 10 : ℚ) ^ i := by
      apply sum_le_sum
      intro j hj
      split_ifs with hc
      · apply (sum_le_sum ?_).trans
          (sum_le_sum_of_subset_of_nonneg (range_mono (by simpa using mem_range.mp hj))
            (by intros; positivity))
        intro d hd
        split_ifs with he
        · exact term hj hd hc.2 he.1 he.2
        · positivity
      · positivity
    _ = (i : ℚ) ^ 2 * (9 / 10) ^ i := by simp; ring

/-- The exponential envelope contracts geometrically beyond index 160. -/
theorem divisor_envelope_le {i : ℕ} (hi : 161 ≤ i) :
    (i : ℚ) ^ 2 * (9 / 10) ^ i ≤
      (161 : ℚ) ^ 2 * (9 / 10) ^ 161 * (23 / 25) ^ (i - 161) := by
  induction i, hi using Nat.le_induction with
  | base => simp
  | succ i hi ih =>
    have hq : (161 : ℚ) ≤ i := by exact_mod_cast hi
    have hs : ((i + 1 : ℕ) : ℚ) ^ 2 * (9 / 10) ≤ (i : ℚ) ^ 2 * (23 / 25) := by
      push_cast
      nlinarith [sq_nonneg ((i : ℚ) - 161)]
    rw [pow_succ, show i + 1 - 161 = (i - 161) + 1 by lia, pow_succ]
    calc
      _ = (((i + 1 : ℕ) : ℚ) ^ 2 * (9 / 10)) * (9 / 10) ^ i := by ring
      _ ≤ ((i : ℚ) ^ 2 * (23 / 25)) * (9 / 10) ^ i := by gcongr
      _ = ((i : ℚ) ^ 2 * (9 / 10) ^ i) * (23 / 25) := by ring
      _ ≤ _ := by
        rw [show (23 / 25 : ℚ) ^ (i - 161 + 1) =
          (23 / 25 : ℚ) ^ (i - 161) * (23 / 25) from pow_succ _ _]
        simpa only [mul_assoc] using
          mul_le_mul_of_nonneg_right ih (by norm_num : (0 : ℚ) ≤ 23 / 25)

/-- Every finite tail of the divisor majorant fits the same rational budget. -/
theorem sum_divisorMajorant_tail_le (N : ℕ) :
    ∑ i ∈ Ico 161 N, divisorMajorant i ≤ divisorTailBudget := by
  calc
    _ ≤ ∑ i ∈ Ico 161 N,
        (161 : ℚ) ^ 2 * (9 / 10) ^ 161 * (23 / 25) ^ (i - 161) := by
      exact sum_le_sum fun i hi => (divisorMajorant_le i).trans
        (divisor_envelope_le (mem_Ico.mp hi).1)
    _ = (161 : ℚ) ^ 2 * (9 / 10) ^ 161 *
        ∑ i ∈ range (N - 161), (23 / 25 : ℚ) ^ i := by
      rw [sum_Ico_eq_sum_range]
      simp only [Nat.add_sub_cancel_left, mul_sum]
    _ ≤ divisorTailBudget := by
      have hh := geom_sum_Ico_le_of_lt_one (m := 0) (n := N - 161)
        (by norm_num : (0 : ℚ) ≤ 23 / 25) (by norm_num : (23 / 25 : ℚ) < 1)
      simp only [Nat.Ico_zero_eq_range, pow_zero, one_div] at hh
      simpa only [divisorTailBudget, div_eq_mul_inv] using
        mul_le_mul_of_nonneg_left hh (by positivity :
          (0 : ℚ) ≤ 161 ^ 2 * (9 / 10) ^ 161)

/-- A kernel-checked mass bound for the finite part of the divisor majorant. -/
theorem divisorMajorant_mass_checked :
    (∑ i ∈ range 161, divisorMajorant i / (i : ℚ)) + divisorTailBudget < 3 / 20 := by
  decide +kernel

/-- A kernel-checked peak bound for the finite part of the divisor majorant. -/
theorem divisorMajorant_peak_checked :
    ∀ i : Fin 161, divisorMajorant i < 17 / 50 := by
  decide +kernel

/-- The geometric tail budget also lies below the peak bound. -/
theorem divisorTailBudget_lt : divisorTailBudget < 17 / 50 := by decide +kernel

/-- Every majorant coefficient is below the same rational peak. -/
theorem divisorMajorant_lt (i : ℕ) : divisorMajorant i < 17 / 50 := by
  by_cases hi : i < 161
  · exact divisorMajorant_peak_checked ⟨i, hi⟩
  · have hm : divisorMajorant i ≤ ∑ j ∈ Ico 161 (i + 1), divisorMajorant j :=
      single_le_sum (f := divisorMajorant)
      (fun j _ => divisorMajorant_nonneg j) (mem_Ico.mpr ⟨by lia, Nat.lt_succ_self i⟩)
    exact (hm.trans (sum_divisorMajorant_tail_le (i + 1))).trans_lt divisorTailBudget_lt

/-- Every partial logarithmic mass is below the same rational bound. -/
theorem sum_divisorMajorant_div_lt (N : ℕ) :
    ∑ i ∈ range N, divisorMajorant i / (i : ℚ) < 3 / 20 := by
  have hn i : 0 ≤ divisorMajorant i / (i : ℚ) :=
    div_nonneg (divisorMajorant_nonneg i) (Nat.cast_nonneg i)
  by_cases hN : N ≤ 161
  · have hb := sum_le_sum_of_subset_of_nonneg (range_mono hN) (fun i _ _ => hn i)
    have hv : 0 ≤ divisorTailBudget := by unfold divisorTailBudget; positivity
    linarith [divisorMajorant_mass_checked]
  · have hN' : 161 ≤ N := by lia
    rw [← sum_range_add_sum_Ico _ hN']
    have hb : (∑ i ∈ Ico 161 N, divisorMajorant i / (i : ℚ)) ≤ divisorTailBudget := by
      apply le_trans (sum_le_sum ?_) (sum_divisorMajorant_tail_le N)
      intro i hi
      exact div_le_self (divisorMajorant_nonneg i) (by
        have := (mem_Ico.mp hi).1
        exact_mod_cast (show 1 ≤ i by lia))
    exact (add_le_add_right hb _).trans_lt divisorMajorant_mass_checked

end RealRooted.LongCycleDescents.Structural
