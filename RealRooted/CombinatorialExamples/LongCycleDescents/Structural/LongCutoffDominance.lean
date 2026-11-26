/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import RealRooted.CombinatorialExamples.LongCycleDescents.Structural.KernelNorm
import RealRooted.CombinatorialExamples.LongCycleDescents.Structural.AlphabetMass
import RealRooted.IntervalDifferential.EulerNorm
import RealRooted.IntervalDifferential.ConvolutionBounds
import Mathlib.Tactic

/-!
# Coefficient dominance at long cutoffs

The Euler product rule separates the constant kernel from its error. Finite
convolution bounds then give strict dominance for every cutoff at least thirteen.

Adapted from Bowen Zuo, cycle-minimum-descent-real-roots v1.0.0 (Apache-2.0)
-/

public section

noncomputable section

open Polynomial Finset

namespace RealRooted.LongCycleDescents.Structural

open IntervalDifferential

private def errorKernel (k i : ℕ) : ℚ[X] :=
  lossKernel k i - C ((lossKernel k i).coeff 0)

private def massKernel (k i : ℕ) : ℚ[X] := C ((lossKernel k i).coeff 0)

private theorem errorKernel_zero (k : ℕ) : errorKernel k 0 = 0 := by
  simp [errorKernel, lossKernel]

private theorem massKernel_zero (k : ℕ) : massKernel k 0 = 0 := by
  simp [massKernel, lossKernel]

private theorem eulerCoeff_massKernel (k : ℕ) (n : ℕ) :
    PowerSeries.eulerCoeff (massKernel k) n = C ((lossRow k n).coeff 0) := by
  have he := PowerSeries.eulerCoeff_unique (massKernel k)
    (fun n => C ((lossRow k n).coeff 0)) (by simp) (by
      intro n hn
      have hh := congrArg (fun p : ℚ[X] => p.coeff 0) (lossRow_equation k hn)
      simp only [← C_eq_natCast, finsetSum_coeff, mul_coeff_zero, coeff_C_zero] at hh
      have hc := congrArg (C : ℚ → ℚ[X]) hh
      simpa only [massKernel, map_sum, map_mul, smul_eq_C_mul] using hc)
  exact (congrFun he n).symm

private theorem lossRow_eq_mass_error_convolution (k n : ℕ) :
    lossRow k n = ∑ i ∈ range (n + 1),
      C ((lossRow k i).coeff 0) * PowerSeries.eulerCoeff (errorKernel k) (n - i) := by
  have he : lossKernel k = massKernel k + errorKernel k := by
    funext i
    simp [massKernel, errorKernel]
  conv_lhs => rw [lossRow_eq_eulerCoeff, he, PowerSeries.eulerCoeff_add _ _
    (massKernel_zero k) (errorKernel_zero k)]
  simp_rw [eulerCoeff_massKernel]

private theorem error_row_bounds {k : ℕ} (hk : 13 ≤ k) (N : ℕ) :
    (∑ i ∈ range N, coefficientNorm (4 / 5 : ℚ)
      (PowerSeries.eulerCoeff (errorKernel k) i)) ≤ 20 / 17 ∧
    (N : ℚ) * coefficientNorm (4 / 5 : ℚ)
      (PowerSeries.eulerCoeff (errorKernel k) N) ≤ 2 / 5 := by
  let u i := coefficientNorm (4 / 5 : ℚ) (errorKernel k i)
  let b i := coefficientNorm (4 / 5 : ℚ) (PowerSeries.eulerCoeff (errorKernel k) i)
  have hu i : 0 ≤ u i := coefficientNorm_nonneg (by norm_num) _
  have hb i : 0 ≤ b i := coefficientNorm_nonneg (by norm_num) _
  have h0 : b 0 = 1 := by
    dsimp [b]
    rw [PowerSeries.eulerCoeff_zero, ← C_1, coefficientNorm_C]
    norm_num
  have hm M : (∑ i ∈ range M, u i / (i : ℚ)) ≤ 3 / 20 :=
    (sum_coefficientNorm_lossKernel_div_lt hk M).le
  have hU i : u i ≤ 17 / 50 := (coefficientNorm_lossKernel_sub_constant_lt hk i).le
  have h1 := sum_euler_bound u b hu hb h0
    (fun n hn => coefficientNorm_eulerCoeff_equation (by norm_num) (errorKernel k) hn)
    (by norm_num : (3 / 20 : ℚ) < 1) hm N
  have h2 := index_mul_euler_bound u b hu hb h0
    (fun n hn => coefficientNorm_eulerCoeff_equation (by norm_num) (errorKernel k) hn)
    (by norm_num : (3 / 20 : ℚ) < 1) hm hU N
  norm_num only at h1 h2
  exact ⟨h1, h2⟩

/-- The actual alphabet has strict coefficient dominance at radius `4/5` for
every cutoff at least thirteen, at every allowed size. -/
theorem coefficientNorm_lossRow_sub_constant_lt {n k : ℕ} (hk : 13 ≤ k) (hkn : k ≤ n) :
    coefficientNorm (4 / 5 : ℚ) (lossRow k n - C ((lossRow k n).coeff 0)) <
      (lossRow k n).coeff 0 := by
  have hk3 : 3 ≤ k := by lia
  let p i := (lossRow k i).coeff 0
  let b i := coefficientNorm (4 / 5 : ℚ) (PowerSeries.eulerCoeff (errorKernel k) i)
  have hb i : 0 ≤ b i := coefficientNorm_nonneg (by norm_num) _
  have hp0 : p 0 = 1 := by
    dsimp [p]
    rw [lossRow_zero]
    simp only [coeff_one]
    norm_num
  have hb0 : b 0 = 1 := by
    dsimp [b]
    rw [PowerSeries.eulerCoeff_zero, ← C_1, coefficientNorm_C]
    norm_num
  have hr i (hi : i ∈ Ico 1 n) : p i ≤ 2 * p n := by
    have hu := coeff_lossRow_zero_le hk3 (show 0 < i by have := mem_Ico.mp hi; lia)
    have hl := one_div_two_mul_le_coeff_lossRow_zero hk3 hkn
    have he : 1 / (k : ℚ) = 2 * (1 / (2 * (k : ℚ))) := by
      have : (k : ℚ) ≠ 0 := by positivity
      field_simp
    rw [he] at hu
    nlinarith
  have hd := convolution_lt_of_factor_two p b hb hp0 hb0 (by lia : 0 < n)
    (coeff_lossRow_zero_pos hk3 hkn) (one_le_mul_coeff_lossRow_zero hk3 hkn)
    hr (error_row_bounds hk n).1 (error_row_bounds hk n).2
  apply lt_of_le_of_lt _ hd
  nth_rw 1 [lossRow_eq_mass_error_convolution]
  rw [sum_range_succ, Nat.sub_self,
    PowerSeries.eulerCoeff_zero, mul_one, add_sub_cancel_right]
  apply (coefficientNorm_sum_le (by norm_num) _ _).trans
  apply sum_le_sum
  intro i _
  rw [coefficientNorm_C_mul, abs_of_nonneg (lossRow_leading_signs hk3 i).1]

end RealRooted.LongCycleDescents.Structural
