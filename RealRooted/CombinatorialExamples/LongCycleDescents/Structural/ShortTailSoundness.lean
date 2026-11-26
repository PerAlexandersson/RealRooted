/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import RealRooted.CombinatorialExamples.LongCycleDescents.Structural.ShortTailCheck
import Mathlib.Tactic

/-!
# Soundness of the denominator-free tail check

The integer margins are exactly the rational coefficient norms. Clearing their
positive denominators introduces no additional assumption about the actual rows.

Adapted from Bowen Zuo, cycle-minimum-descent-real-roots v1.0.0 (Apache-2.0)
-/

public section

noncomputable section

open Polynomial Finset

namespace RealRooted.LongCycleDescents.Structural

/-- The same finite table computes every earlier anchor exactly. -/
theorem shortAnchorNumerator_eq_of_le (k H n : ℕ) (hn : n ≤ H) {h : ℕ} (hh : h ≤ n) :
    (shortAnchorNumerator n (shortCoefficientTable k H) h : ℚ) =
      (n.factorial : ℚ) * (lossRow k n).coeff h := by
  rw [shortAnchorNumerator, lossRow_eq_sum_differenceRow, finsetSum_coeff]
  simp only [Int.cast_sum, Int.cast_mul, Int.cast_natCast, mul_sum]
  apply sum_congr rfl
  intro j hj
  have hjn : j ≤ n := Nat.le_of_lt_succ (mem_range.mp hj)
  rw [shortCoefficientTable_correct k H (hjn.trans hn) (hh.trans hn)]
  have hf : ((n.factorial / j.factorial : ℕ) : ℚ) * j.factorial = n.factorial := by
    exact_mod_cast Nat.div_mul_cancel (Nat.factorial_dvd_factorial hjn)
  linear_combination (differenceRow k j).coeff h * hf

/-- The computed anchor coefficients are factorial-scaled genuine alphabet coefficients. -/
theorem shortAnchorNumerator_eq (k H : ℕ) {h : ℕ} (hh : h ≤ H) :
    (shortAnchorNumerator H (shortCoefficientTable k H) h : ℚ) =
      (H.factorial : ℚ) * (lossRow k H).coeff h :=
  shortAnchorNumerator_eq_of_le k H H le_rfl hh

private theorem norm_nonconstant_lossRow (k H : ℕ) :
    coefficientNorm (4 / 5 : ℚ) (lossRow k H - C ((lossRow k H).coeff 0)) =
      ∑ h ∈ Ico 1 (H + 1), |(lossRow k H).coeff h| * (4 / 5 : ℚ) ^ h := by
  have hs : (lossRow k H).support ⊆ range (H + 1) := by
    intro h hh
    exact mem_range.mpr (Nat.lt_succ_of_le
      ((le_natDegree_of_mem_supp h hh).trans (natDegree_lossRow_le k H)))
  have he := coefficientNorm_eq_abs_constant_add (4 / 5 : ℚ) (lossRow k H)
  rw [coefficientNorm_eq_sum hs,
    ← sum_range_add_sum_Ico (fun h => |(lossRow k H).coeff h| * (4 / 5 : ℚ) ^ h)
      (by lia : 1 ≤ H + 1)] at he
  simp only [sum_range_one, pow_zero, mul_one] at he
  exact (add_left_cancel he).symm

/-- A finite table computes every earlier rational coefficient margin. -/
theorem shortMarginNumerator_eq_of_le (k H n : ℕ) (hn : n ≤ H) :
    (shortMarginNumerator n (shortCoefficientTable k H) : ℚ) =
      (n.factorial : ℚ) * 5 ^ n * ((lossRow k n).coeff 0 -
        coefficientNorm (4 / 5 : ℚ) (lossRow k n - C ((lossRow k n).coeff 0))) := by
  rw [shortMarginNumerator, Int.cast_sub, Int.cast_mul, Int.cast_pow, Int.cast_ofNat,
    shortAnchorNumerator_eq_of_le k H n hn (Nat.zero_le n),
    sum_abs_mul_pow_eq n (Ico 1 (n + 1)) (fun h hh => by have := mem_Ico.mp hh; lia)]
  have he : (∑ h ∈ Ico 1 (n + 1),
      |(shortAnchorNumerator n (shortCoefficientTable k H) h : ℚ)| * (4 / 5 : ℚ) ^ h) =
      (n.factorial : ℚ) * ∑ h ∈ Ico 1 (n + 1),
        |(lossRow k n).coeff h| * (4 / 5 : ℚ) ^ h := by
    rw [mul_sum]
    apply sum_congr rfl
    intro h hh
    rw [shortAnchorNumerator_eq_of_le k H n hn (by have := mem_Ico.mp hh; lia), abs_mul,
      abs_of_nonneg (Nat.cast_nonneg n.factorial)]
    ring
  rw [he, ← norm_nonconstant_lossRow]
  ring

/-- The integer anchor margin is its exact rational coefficient margin. -/
theorem shortMarginNumerator_eq (k H : ℕ) :
    (shortMarginNumerator H (shortCoefficientTable k H) : ℚ) =
      (H.factorial : ℚ) * 5 ^ H * ((lossRow k H).coeff 0 -
        coefficientNorm (4 / 5 : ℚ) (lossRow k H - C ((lossRow k H).coeff 0))) :=
  shortMarginNumerator_eq_of_le k H H le_rfl

/-- Prefix margins from the same table cover the ranks before its tail anchor. -/
theorem coefficientNorm_lt_of_shortPrefixCertificate {k H n : ℕ}
    (hn : 18 ≤ n) (hH : n ≤ H) (hc : shortPrefixCertificate k H = true) :
    coefficientNorm (4 / 5 : ℚ) (lossRow k n - C ((lossRow k n).coeff 0)) <
      (lossRow k n).coeff 0 := by
  dsimp only [shortPrefixCertificate] at hc
  have hh : 0 < shortMarginNumerator n (shortCoefficientTable k H) := by
    have he := List.all_eq_true.mp hc n (List.mem_range.mpr (by lia))
    simpa only [ite_eq_left hn, decide_eq_true_eq] using he
  have hpos : (0 : ℚ) < shortMarginNumerator n (shortCoefficientTable k H) := by
    exact_mod_cast hh
  rw [shortMarginNumerator_eq_of_le k H n hH] at hpos
  have hfac : (0 : ℚ) < (n.factorial : ℚ) * 5 ^ n := by positivity
  exact sub_pos.mp ((mul_pos_iff_of_pos_left hfac).mp hpos)

/-- The sparse integer kernel norm has denominator exactly `5^64`. -/
theorem shortKernelNormNumerator_eq (k : ℕ) {i : ℕ} (hi : i ≤ 64) :
    (shortKernelNormNumerator k i : ℚ) = (5 : ℚ) ^ 64 * shortKernelNorm k i := by
  have he := sum_shortKernelCell_reflect k i
    (fun h => |shortKernelCell k i h| * (4 : ℤ) ^ h * 5 ^ (64 - h))
    (fun h hz => by rw [hz]; simp)
  rw [shortKernelNormNumerator, ← he,
    sum_abs_mul_pow_eq 64 (range (i + 1)) (fun h hh => by have := mem_range.mp hh; lia)]
  rfl

/-- The integer geometric remainder has the same denominator. -/
theorem shortKernelTailNumerator_eq {k : ℕ} (hk : k ≤ 66) :
    (shortKernelTailNumerator k : ℚ) = (5 : ℚ) ^ 64 * shortKernelTail k := by
  have hc : (5 : ℚ) ^ 64 * (4 / 5) ^ 65 / (1 - 4 / 5) = 4 ^ 65 := by norm_num
  have hp {q : ℕ} (hq : q ≤ 65) : (4 : ℚ) ^ (65 - q) * 5 ^ q =
      (5 / 4 : ℚ) ^ q * ((5 : ℚ) ^ 64 * (4 / 5) ^ 65 / (1 - 4 / 5)) := by
    rw [hc, div_pow]
    have he : (4 : ℚ) ^ (65 - q) * 4 ^ q = 4 ^ 65 := by
      rw [← pow_add, Nat.sub_add_cancel hq]
    field_simp
    rw [← he]
  calc
    _ = ∑ j ∈ range (k - 1), ∑ d ∈ (j + 1).divisors,
        (5 / 4 : ℚ) ^ ((j + 1) / d) * ((5 : ℚ) ^ 64 * (4 / 5) ^ 65 / (1 - 4 / 5)) := by
      simp only [shortKernelTailNumerator, Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_ofNat]
      apply sum_congr rfl
      intro j hj
      apply sum_congr rfl
      intro d _
      exact hp ((Nat.div_le_self _ _).trans (by have := mem_range.mp hj; lia))
    _ = _ := by
      simp only [shortKernelTail, shortKernelScale, div_eq_mul_inv, sum_mul, mul_sum]
      apply sum_congr rfl
      intro j _
      apply sum_congr rfl
      intro d _
      ring

/-- Every integer tail numerator is the corresponding rational tail budget. -/
theorem shortTailNumerator_eq {k : ℕ} (hk : k ≤ 66) (l : ℕ) :
    (shortTailNumerator k l : ℚ) = (5 : ℚ) ^ 64 * shortTailBound k l := by
  rw [shortTailNumerator, Int.cast_add, Int.cast_sum, shortKernelTailNumerator_eq hk,
    shortTailBound, mul_add, mul_sum]
  congr 1
  exact sum_congr rfl (fun i hi => shortKernelNormNumerator_eq k
    (by have := mem_Ico.mp hi; lia))

/-- A successful integer check gives the exact rational anchor and tail inequalities. -/
theorem shortTailCertificate_sound {k H : ℕ} (hk : k ≤ 66)
    (hc : shortTailCertificate k H = true) :
    shortTailBound k 1 < (H + 1 : ℕ) ∧
      (∑ j ∈ range (H + 1), coefficientNorm (4 / 5 : ℚ) (differenceRow k j) *
        shortTailBound k (H + 1 - j)) <
      ((H + 1 : ℕ) - shortTailBound k 1) * ((lossRow k H).coeff 0 -
        coefficientNorm (4 / 5 : ℚ) (lossRow k H - C ((lossRow k H).coeff 0))) := by
  dsimp only [shortTailCertificate] at hc
  have hh := of_decide_eq_true hc
  have hB : (0 : ℚ) < 5 ^ 64 := by positivity
  have hA : (0 : ℚ) < (H.factorial : ℚ) * 5 ^ H := by positivity
  have h1 : (shortTailNumerator k 1 : ℚ) < ((H + 1 : ℕ) : ℚ) * 5 ^ 64 := by
    exact_mod_cast hh.1
  rw [shortTailNumerator_eq hk] at h1
  have h2 : ((∑ j ∈ range (H + 1), ((H.factorial / j.factorial : ℕ) : ℤ) *
      arrayNormNumerator H ((shortCoefficientTable k H).getD j #[]) *
        shortTailNumerator k (H + 1 - j) : ℤ) : ℚ) <
      (((H + 1 : ℕ) : ℚ) * 5 ^ 64 - (shortTailNumerator k 1 : ℚ)) *
        (shortMarginNumerator H (shortCoefficientTable k H) : ℚ) := by
    exact_mod_cast hh.2
  have hb : ((∑ j ∈ range (H + 1), ((H.factorial / j.factorial : ℕ) : ℤ) *
      arrayNormNumerator H ((shortCoefficientTable k H).getD j #[]) *
        shortTailNumerator k (H + 1 - j) : ℤ) : ℚ) =
      (H.factorial : ℚ) * 5 ^ H * 5 ^ 64 *
        ∑ j ∈ range (H + 1), coefficientNorm (4 / 5 : ℚ) (differenceRow k j) *
          shortTailBound k (H + 1 - j) := by
    simp only [Int.cast_sum, Int.cast_mul, Int.cast_natCast, mul_sum]
    apply sum_congr rfl
    intro j hj
    have hjH := Nat.le_of_lt_succ (mem_range.mp hj)
    rw [arrayNormNumerator_shortCoefficientTable hjH, shortTailNumerator_eq hk]
    have hf : ((H.factorial / j.factorial : ℕ) : ℚ) * j.factorial = H.factorial := by
      exact_mod_cast Nat.div_mul_cancel (Nat.factorial_dvd_factorial hjH)
    linear_combination (5 : ℚ) ^ H * 5 ^ 64 *
      coefficientNorm (4 / 5 : ℚ) (differenceRow k j) * shortTailBound k (H + 1 - j) * hf
  rw [hb, shortTailNumerator_eq hk, shortMarginNumerator_eq] at h2
  constructor
  · apply (mul_lt_mul_iff_right₀ hB).mp
    simpa only [mul_comm] using h1
  · apply (mul_lt_mul_iff_right₀ (mul_pos hA hB)).mp
    convert h2 using 1; ring

end RealRooted.LongCycleDescents.Structural
