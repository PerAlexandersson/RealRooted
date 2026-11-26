/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import RealRooted.CombinatorialExamples.LongCycleDescents.Structural.AlphabetReflection
public import RealRooted.CombinatorialExamples.LongCycleDescents.Structural.DivisorMajorant
public import RealRooted.IntervalDifferential.CoefficientNorm
import Mathlib.Tactic

/-!
# The alphabet kernel error norm

The nonconstant part of the actual reflected necklace kernel is bounded by the
rational divisor majorant. This bound holds uniformly for all cutoffs at least
thirteen, without a root-location assumption on an alphabet polynomial.

Adapted from Bowen Zuo, cycle-minimum-descent-real-roots v1.0.0 (Apache-2.0)
-/

public section

noncomputable section

open Polynomial Finset
open scoped ArithmeticFunction.Moebius

namespace RealRooted.LongCycleDescents.Structural

private theorem lossKernel_sub_constant (k i : ℕ) :
    lossKernel k i - C ((lossKernel k i).coeff 0) =
      ∑ j ∈ range i, if k ≤ j + 1 ∧ j + 1 ∣ i then
        ∑ d ∈ (j + 1).divisors, if i - (j + 1) / d = 0 then 0 else
          C (μ d : ℚ) * X ^ (i - (j + 1) / d) else 0 := by
  simp only [lossKernel, finsetSum_coeff, apply_ite (fun p : ℚ[X] => p.coeff 0),
    coeff_zero, coeff_C_mul_X_pow, map_sum, apply_ite (C : ℚ → ℚ[X]), map_zero]
  rw [← sum_sub_distrib]
  apply sum_congr rfl
  intro j _
  split_ifs with hj
  · rw [← sum_sub_distrib]
    apply sum_congr rfl
    intro d _
    by_cases hd : i - (j + 1) / d = 0
    · simp [hd]
    · simp [hd, Ne.symm hd]
  · simp

private theorem sum_divisors_succ (j : ℕ) (f : ℕ → ℚ) :
    (∑ d ∈ (j + 1).divisors, f d) =
      ∑ d ∈ range (j + 1), if d + 1 ∣ j + 1 then f (d + 1) else 0 := by
  rw [Nat.divisors, sum_filter, sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel, add_comm 1]

private theorem abs_moebius_rat_le (d : ℕ) : |(μ d : ℚ)| ≤ 1 := by
  rcases ArithmeticFunction.moebius_eq_or d with h | h | h <;> rw [h] <;> norm_num

/-- The actual reflected kernel error satisfies the uniform divisor majorant. -/
theorem coefficientNorm_lossKernel_sub_constant_le {k : ℕ} (hk : 13 ≤ k) (i : ℕ) :
    coefficientNorm (4 / 5 : ℚ) (lossKernel k i - C ((lossKernel k i).coeff 0)) ≤
      divisorMajorant i := by
  rw [lossKernel_sub_constant]
  apply (coefficientNorm_sum_le (by norm_num) _ _).trans
  unfold divisorMajorant
  apply sum_le_sum
  intro j hj
  by_cases hc : k ≤ j + 1 ∧ j + 1 ∣ i
  · rw [ite_eq_left hc, ite_eq_left (show 13 ≤ j + 1 ∧ j + 1 ∣ i by lia)]
    apply (coefficientNorm_sum_le (by norm_num) _ _).trans
    rw [sum_divisors_succ]
    apply sum_le_sum
    intro d hd
    by_cases hdj : d + 1 ∣ j + 1
    · simp only [hdj, true_and, ite_true]
      by_cases hz : i - (j + 1) / (d + 1) = 0
      · rw [ite_eq_left hz, coefficientNorm_zero]
        split_ifs <;> positivity
      · rw [ite_eq_right hz, ite_eq_left (show
          (j + 1) / (d + 1) < i by lia), C_mul_X_pow_eq_monomial,
          coefficientNorm_monomial]
        exact (mul_le_mul_of_nonneg_right (abs_moebius_rat_le (d + 1))
          (by positivity)).trans_eq (one_mul _)
    · simp [hdj]
  · rw [ite_eq_right hc, coefficientNorm_zero]
    split_ifs
    · apply sum_nonneg
      intro d _
      split_ifs <;> positivity
    · exact le_rfl

/-- The error kernel has a uniform rational peak, at every degree. -/
theorem coefficientNorm_lossKernel_sub_constant_lt {k : ℕ} (hk : 13 ≤ k) (i : ℕ) :
    coefficientNorm (4 / 5 : ℚ) (lossKernel k i - C ((lossKernel k i).coeff 0)) <
      17 / 50 :=
  (coefficientNorm_lossKernel_sub_constant_le hk i).trans_lt (divisorMajorant_lt i)

/-- All partial logarithmic masses of the actual error kernel satisfy the same
rational bound. -/
theorem sum_coefficientNorm_lossKernel_div_lt {k : ℕ} (hk : 13 ≤ k) (N : ℕ) :
    (∑ i ∈ range N, coefficientNorm (4 / 5 : ℚ)
      (lossKernel k i - C ((lossKernel k i).coeff 0)) / (i : ℚ)) < 3 / 20 := by
  apply lt_of_le_of_lt (sum_le_sum ?_) (sum_divisorMajorant_div_lt N)
  intro i _
  exact div_le_div_of_nonneg_right (coefficientNorm_lossKernel_sub_constant_le hk i)
    (Nat.cast_nonneg i)

end RealRooted.LongCycleDescents.Structural
