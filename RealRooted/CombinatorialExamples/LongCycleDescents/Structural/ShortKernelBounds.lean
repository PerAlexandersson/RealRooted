/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import RealRooted.CombinatorialExamples.LongCycleDescents.Structural.ShortCoefficients
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Tactic

/-!
# Geometric tails of the excluded-length kernel

Adapted from Bowen Zuo, cycle-minimum-descent-real-roots v1.0.0 (Apache-2.0)
-/

@[expose] public section

noncomputable section

open Polynomial Finset
open scoped ArithmeticFunction.Moebius

namespace RealRooted.LongCycleDescents.Structural

/-- Coefficientwise geometric majorant for the finitely many excluded lengths. -/
def shortKernelScale (k : ℕ) : ℚ :=
  ∑ j ∈ range (k - 1), ∑ d ∈ (j + 1).divisors, (5 / 4 : ℚ) ^ ((j + 1) / d)

/-- The geometric budget for short-kernel norms at indices at least 65. -/
def shortKernelTail (k : ℕ) : ℚ := shortKernelScale k * (4 / 5 : ℚ) ^ 65 / (1 - 4 / 5)

/-- A bound for every short-kernel norm tail starting below index 65. -/
def shortTailBound (k l : ℕ) : ℚ :=
  (∑ i ∈ Ico l 65, shortKernelNorm k i) + shortKernelTail k

private theorem abs_moebius_rat_le (d : ℕ) : |(μ d : ℚ)| ≤ 1 := by
  rcases ArithmeticFunction.moebius_eq_or d with h | h | h <;> rw [h] <;> norm_num

/-- Every short-kernel norm has an elementary geometric envelope. -/
theorem shortKernelNorm_le {i : ℕ} (hi : 0 < i) (k : ℕ) :
    shortKernelNorm k i ≤ shortKernelScale k * (4 / 5 : ℚ) ^ i := by
  rw [shortKernelNorm_eq, shortKernel_eq_sum hi]
  apply (coefficientNorm_sum_le (by norm_num) _ _).trans
  rw [shortKernelScale, sum_mul]
  apply sum_le_sum
  intro j _
  by_cases hj : j + 1 ∣ i
  · rw [ite_eq_left hj, sum_mul]
    apply (coefficientNorm_sum_le (by norm_num) _ _).trans
    apply sum_le_sum
    intro d hd
    have hq : (j + 1) / d ≤ i :=
      (Nat.div_le_self _ _).trans (Nat.le_of_dvd hi hj)
    rw [C_mul_X_pow_eq_monomial, coefficientNorm_monomial]
    have hp : (4 / 5 : ℚ) ^ (i - (j + 1) / d) =
        (5 / 4 : ℚ) ^ ((j + 1) / d) * (4 / 5 : ℚ) ^ i := by
      rw [show (5 / 4 : ℚ) = (4 / 5 : ℚ)⁻¹ by norm_num, inv_pow,
        mul_comm ((4 / 5 : ℚ) ^ ((j + 1) / d))⁻¹, ← div_eq_mul_inv,
        eq_div_iff (pow_ne_zero _ (by norm_num)), ← pow_add, Nat.sub_add_cancel hq]
    exact (mul_le_mul_of_nonneg_right (abs_moebius_rat_le d) (by positivity)).trans_eq
      (by rw [one_mul, hp])
  · rw [ite_eq_right hj, coefficientNorm_zero]
    positivity

/-- The short-kernel scale is nonnegative. -/
theorem shortKernelScale_nonneg (k : ℕ) : 0 ≤ shortKernelScale k := by
  exact sum_nonneg fun _ _ => sum_nonneg fun _ _ => by positivity

/-- Every finite geometric tail fits its infinite-series budget. -/
theorem sum_shortKernelNorm_geometric_le {l : ℕ} (hl : 0 < l) (k B : ℕ) :
    (∑ i ∈ Ico l B, shortKernelNorm k i) ≤
      shortKernelScale k * (4 / 5 : ℚ) ^ l / (1 - 4 / 5) := by
  calc
    _ ≤ ∑ i ∈ Ico l B, shortKernelScale k * (4 / 5 : ℚ) ^ i :=
      sum_le_sum (fun i hi => shortKernelNorm_le (hl.trans_le (mem_Ico.mp hi).1) k)
    _ = shortKernelScale k * ∑ i ∈ Ico l B, (4 / 5 : ℚ) ^ i := (mul_sum ..).symm
    _ ≤ _ := by
      simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left
        (geom_sum_Ico_le_of_lt_one (m := l) (n := B)
          (by norm_num : (0 : ℚ) ≤ 4 / 5) (by norm_num : (4 / 5 : ℚ) < 1))
        (shortKernelScale_nonneg k)

/-- The exact first 64 norms plus the geometric remainder bound every tail
starting in the certificate's valid range. -/
theorem sum_shortKernelNorm_le {l : ℕ} (h65 : l ≤ 65) (k B : ℕ) :
    ∑ i ∈ Ico l B, shortKernelNorm k i ≤ shortTailBound k l := by
  have hn i : 0 ≤ shortKernelNorm k i := by
    rw [shortKernelNorm_eq]
    exact coefficientNorm_nonneg (by norm_num) _
  have ht : 0 ≤ shortKernelTail k := by
    unfold shortKernelTail
    exact div_nonneg (mul_nonneg (shortKernelScale_nonneg k) (by positivity)) (by norm_num)
  by_cases hB : B ≤ 65
  · exact (sum_le_sum_of_subset_of_nonneg (Ico_subset_Ico_right hB) (fun i _ _ => hn i)).trans
      (le_add_of_nonneg_right ht)
  · have hh := sum_shortKernelNorm_geometric_le (by decide : 0 < 65) k B
    rw [← sum_Ico_consecutive (fun i => shortKernelNorm k i) h65 (by lia : 65 ≤ B)]
    exact add_le_add_right hh _

end RealRooted.LongCycleDescents.Structural
