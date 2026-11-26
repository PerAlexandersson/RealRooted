/-
Copyright (c) 2026 Bowen Zuo and Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bowen Zuo, Per Alexandersson
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.Field.GeomSum
public import Mathlib.Algebra.Order.Field.Rat
import RealRooted.CombinatorialExamples.LongCycleDescents.Structural.AlphabetLeading
public import RealRooted.CombinatorialExamples.LongCycleDescents.Structural.AlphabetRecurrence
public import RealRooted.IntervalDifferential.CoefficientNorm
import RealRooted.IntervalDifferential.ConvolutionBounds
import RealRooted.IntervalDifferential.EulerRecurrence
import Mathlib.Tactic

/-!
# Coefficient dominance at long cutoffs

A rational divisor majorant bounds the nonconstant reflected kernel for cutoffs
at least thirteen. Splitting the Euler kernel into constant and error parts and
applying finite convolution bounds gives strict dominance at radius `4/5`.

Adapted from Bowen Zuo, cycle-minimum-descent-real-roots v1.0.0 (Apache-2.0).
-/

@[expose] public noncomputable section

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
        exact (mul_le_mul_of_nonneg_right
          (show |(μ (d + 1) : ℚ)| ≤ 1 from by
            exact_mod_cast ArithmeticFunction.abs_moebius_le_one)
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
