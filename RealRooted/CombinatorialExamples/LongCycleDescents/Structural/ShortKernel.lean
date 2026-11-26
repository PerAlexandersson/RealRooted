/-
Copyright (c) 2026 Bowen Zuo and Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bowen Zuo, Per Alexandersson
-/
module

import Mathlib.Algebra.Order.Field.GeomSum
public import RealRooted.CombinatorialExamples.LongCycleDescents.Structural.AlphabetRecurrence
public import RealRooted.IntervalDifferential.CoefficientNorm
public import RealRooted.IntervalDifferential.EulerRecurrence
import Mathlib.Tactic

/-!
# Excluded-length kernels and exact coefficient tables

The scalar divisor formula computes the excluded kernel. An integer Euler table
computes its difference rows exactly. The first 64 norms plus a geometric
remainder bound every tail in the certificate range.

Adapted from Bowen Zuo, cycle-minimum-descent-real-roots v1.0.0 (Apache-2.0).
-/

@[expose] public noncomputable section

open Polynomial Finset
open scoped ArithmeticFunction.Moebius

namespace RealRooted.LongCycleDescents.Structural

/-- The unrestricted primitive-necklace identity. -/
theorem sum_length_mul_necklacePolynomial {i : ℕ} (hi : 0 < i) :
    ∑ j ∈ i.divisors, (j : ℚ[X]) * necklacePolynomial j = X ^ i := by
  let f (j : ℕ) := (j : ℚ[X]) * necklacePolynomial j
  let g j := (X : ℚ[X]) ^ j
  apply (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq (f := f) (g := g)).mpr ?_ i hi
  intro j hj
  dsimp [f, g]
  rw [Nat.sum_divisorsAntidiagonal (fun a b => (μ a : ℚ[X]) * X ^ b)]
  rw [← C_eq_natCast, necklacePolynomial, ← mul_assoc, ← C_mul,
    mul_inv_cancel₀ (by exact_mod_cast hj.ne' : (j : ℚ) ≠ 0), C_1, one_mul]
  apply sum_congr rfl
  intro d _
  rw [map_intCast]

/-- The full alphabet kernel is the corresponding pure power. -/
theorem alphabetKernel_one {i : ℕ} (hi : 0 < i) : alphabetKernel 1 i = X ^ i := by
  rw [alphabetKernel]
  have he : (∑ j ∈ range i, if 1 ≤ j + 1 ∧ j + 1 ∣ i then
      ((j + 1 : ℕ) : ℚ[X]) * necklacePolynomial (j + 1) else 0) =
      ∑ j ∈ i.divisors, (j : ℚ[X]) * necklacePolynomial j := by
    rw [Nat.divisors, sum_filter, sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel, add_comm 1, Nat.succ_le_succ (Nat.zero_le _), true_and]
  rw [he, sum_length_mul_necklacePolynomial hi]

/-- The full reflected kernel has every positive coefficient equal to one. -/
theorem lossKernel_one {i : ℕ} (hi : 0 < i) : lossKernel 1 i = 1 := by
  rw [← reflect_alphabetKernel, alphabetKernel_one hi, reflect_monomial]
  simp

/-- The reflected kernel of the excluded cycle lengths. -/
def shortKernel (k i : ℕ) : ℚ[X] :=
  if i = 0 then 0 else
    ∑ j ∈ range i, if j + 1 < k ∧ j + 1 ∣ i then
      ∑ d ∈ (j + 1).divisors, C (μ d : ℚ) * X ^ (i - (j + 1) / d) else 0

@[simp] theorem shortKernel_zero (k : ℕ) : shortKernel k 0 = 0 := by simp [shortKernel]

/-- Allowed and excluded lengths partition the full positive kernel. -/
theorem lossKernel_add_shortKernel {i : ℕ} (hi : 0 < i) (k : ℕ) :
    lossKernel k i + shortKernel k i = 1 := by
  rw [← lossKernel_one hi, lossKernel, shortKernel, ite_eq_right hi.ne', ← sum_add_distrib]
  apply sum_congr rfl
  intro j _
  by_cases hd : j + 1 ∣ i <;> by_cases hk : k ≤ j + 1 <;>
    simp [hd, hk, Nat.lt_of_not_ge, Nat.not_lt.mpr]

/-- The short kernel only needs the excluded lengths, independently of the rank. -/
theorem shortKernel_eq_sum {i : ℕ} (hi : 0 < i) (k : ℕ) :
    shortKernel k i = ∑ j ∈ range (k - 1), if j + 1 ∣ i then
      ∑ d ∈ (j + 1).divisors, C (μ d : ℚ) * X ^ (i - (j + 1) / d) else 0 := by
  rw [shortKernel, ite_eq_right hi.ne', ← sum_filter, ← sum_filter]
  have hs : (range i).filter (fun j => j + 1 < k ∧ j + 1 ∣ i) =
      (range (k - 1)).filter (fun j => j + 1 ∣ i) := by
    ext j
    simp only [mem_filter, mem_range]
    constructor
    · rintro ⟨_, hj, hd⟩
      exact ⟨by lia, hd⟩
    · rintro ⟨hj, hd⟩
      have ht := Nat.le_of_dvd hi hd
      exact ⟨by lia, by lia, hd⟩
  rw [hs]

/-- The short kernel is supported in degree at most its rank. -/
theorem natDegree_shortKernel_le (k i : ℕ) : (shortKernel k i).natDegree ≤ i := by
  unfold shortKernel
  split_ifs
  · simp
  · apply natDegree_sum_le_of_forall_le
    intro j _
    split_ifs
    · apply natDegree_sum_le_of_forall_le
      intro d _
      exact (natDegree_C_mul_le _ _).trans
        ((natDegree_X_pow_le _).trans (Nat.sub_le _ _))
    · simp

private def fullKernel (i : ℕ) : ℚ[X] := if i = 0 then 0 else 1

private theorem eulerCoeff_fullKernel (n : ℕ) : PowerSeries.eulerCoeff fullKernel n = 1 := by
  have he := PowerSeries.eulerCoeff_unique fullKernel (fun _ => (1 : ℚ[X])) rfl (by
    intro n hn
    have hs : (∑ i ∈ range n, fullKernel (n - i) * 1) = ∑ _i ∈ range n, (1 : ℚ[X]) := by
      exact sum_congr rfl (fun i hi => by
        simp [fullKernel, show n - i ≠ 0 by have := mem_range.mp hi; lia])
    rw [hs]
    simp [Algebra.smul_def])
  exact (congrFun he n).symm

/-- The successive-difference row of the reflected alphabets. -/
def differenceRow (k n : ℕ) : ℚ[X] := PowerSeries.eulerCoeff (-shortKernel k) n

/-- The genuine alphabet row is the prefix sum of the short-kernel coefficients. -/
theorem lossRow_eq_sum_differenceRow (k n : ℕ) :
    lossRow k n = ∑ i ∈ range (n + 1), differenceRow k i := by
  have hk : lossKernel k = fullKernel + (-shortKernel k) := by
    funext i
    by_cases hi : i = 0
    · simp [hi, lossKernel, fullKernel]
    · have he := lossKernel_add_shortKernel (Nat.pos_of_ne_zero hi) k
      simp only [Pi.add_apply, Pi.neg_apply, fullKernel, ite_eq_right hi]
      linear_combination he
  conv_lhs => rw [lossRow_eq_eulerCoeff, hk, PowerSeries.eulerCoeff_add _ _
    (by simp [fullKernel]) (by simp)]
  simp only [eulerCoeff_fullKernel, one_mul]
  simpa [differenceRow] using sum_range_reflect (differenceRow k) (n + 1)

end RealRooted.LongCycleDescents.Structural

open Polynomial Finset
open scoped ArithmeticFunction.Moebius

namespace RealRooted.LongCycleDescents.Structural

open IntervalDifferential

/-- An executable scalar coefficient of the excluded-length kernel. -/
def shortKernelCell (k i h : ℕ) : ℤ :=
  if i = 0 then 0 else ∑ j ∈ range (k - 1), if j + 1 ∣ i then
    ∑ d ∈ (j + 1).divisors, if h = i - (j + 1) / d then μ d else 0 else 0

/-- The scalar formula computes the genuine excluded-kernel coefficient. -/
theorem shortKernelCell_eq (k i h : ℕ) :
    (shortKernelCell k i h : ℚ) = (shortKernel k i).coeff h := by
  by_cases hi : i = 0
  · simp [hi, shortKernelCell]
  · rw [shortKernel_eq_sum (Nat.pos_of_ne_zero hi)]
    simp only [shortKernelCell, ite_eq_right hi, finsetSum_coeff,
      apply_ite (fun p : ℚ[X] => p.coeff h), coeff_zero, coeff_C_mul_X_pow,
      Int.cast_ite, Int.cast_sum, Int.cast_zero]

/-- A short-kernel coefficient can only occur at the excluded degree losses. -/
theorem shortKernelCell_eq_zero {k i h : ℕ} (hh : i ≤ h ∨ h + (k - 1) < i) :
    shortKernelCell k i h = 0 := by
  unfold shortKernelCell
  split_ifs
  · rfl
  · apply sum_eq_zero
    intro j hj
    split_ifs with hdj
    · apply sum_eq_zero
      intro d hd
      apply ite_eq_right
      intro he
      have hjk := mem_range.mp hj
      have hdiv := Nat.dvd_of_mem_divisors hd
      have hjpos : 0 < j + 1 := Nat.succ_pos _
      have hdpos := Nat.pos_of_dvd_of_pos hdiv hjpos
      have hqpos := Nat.div_pos (Nat.le_of_dvd hjpos hdiv) hdpos
      have hqle := Nat.div_le_self (j + 1) d
      have hji := Nat.le_of_dvd (Nat.pos_of_ne_zero (by assumption)) hdj
      rcases hh with hh | hh <;> lia
    · rfl

/-- Reindex any function supported on the short-kernel coefficients by its loss. -/
theorem sum_shortKernelCell_reflect {R : Type*} [AddCommMonoid R] (k i : ℕ)
    (f : ℕ → R) (hf : ∀ h, shortKernelCell k i h = 0 → f h = 0) :
    (∑ h ∈ range (i + 1), f h) = ∑ q ∈ Icc 1 (min i (k - 1)), f (i - q) := by
  rw [← sum_range_reflect f (i + 1)]
  simp only [Nat.add_sub_cancel]
  symm
  apply sum_subset (by intro q hq; have := mem_Icc.mp hq; exact mem_range.mpr (by lia))
  intro q hq hqn
  apply hf
  have hqi := mem_range.mp hq
  apply shortKernelCell_eq_zero
  by_cases hq0 : q = 0
  · exact Or.inl (by simp [hq0])
  · exact Or.inr (by
      have ht : ¬ (1 ≤ q ∧ q ≤ min i (k - 1)) := fun h => hqn (mem_Icc.mpr h)
      simp only [le_min_iff] at ht
      lia)

/-- The only exponents that can occur in a short-kernel row. -/
def shortKernelSupport (k i : ℕ) : Finset ℕ := Ico (i - (k - 1)) i

/-- The short-kernel support omits only zero coefficients. -/
theorem shortKernelCell_eq_zero_of_not_mem {k i h : ℕ}
    (hh : h ∉ shortKernelSupport k i) : shortKernelCell k i h = 0 := by
  apply shortKernelCell_eq_zero
  simp only [shortKernelSupport, mem_Ico, not_and_or, not_le, not_lt] at hh
  rcases hh with hh | hh
  · exact Or.inr (by lia)
  · exact Or.inl hh

/-- Recompute all short-kernel difference rows through the fixed certificate rank. -/
def shortCoefficientTable (k H : ℕ) : Array (Array ℤ) :=
  eulerCoefficientTable H (shortKernelSupport k) (fun i h => -shortKernelCell k i h) (H + 1)

/-- Every coefficient used by the finite tail certificate is exact. -/
theorem shortCoefficientTable_correct (k H : ℕ) {n h : ℕ} (hn : n ≤ H) (hh : h ≤ H) :
    ((((shortCoefficientTable k H).getD n #[]).getD h 0 : ℤ) : ℚ) =
      (n.factorial : ℚ) * (differenceRow k n).coeff h := by
  apply eulerCoefficientTable_correct H (shortKernelSupport k) _ (-shortKernel k) _
    (fun i => by simpa using natDegree_shortKernel_le k i)
    (fun i h hh => by rw [shortKernelCell_eq_zero_of_not_mem hh, neg_zero]) (by lia) hh
  intro i h
  simp only [Int.cast_neg, shortKernelCell_eq, Pi.neg_apply, coeff_neg]

/-- A difference row has degree at most its rank. -/
theorem natDegree_differenceRow_le (k n : ℕ) : (differenceRow k n).natDegree ≤ n := by
  exact natDegree_eulerCoeff_le (-shortKernel k)
    (fun i => by simpa using natDegree_shortKernel_le k i) n

/-- Integer numerator of a weighted coefficient norm at radius `4/5`. -/
def arrayNormNumerator (H : ℕ) (row : Array ℤ) : ℤ :=
  ∑ h ∈ range (H + 1), |row.getD h 0| * 4 ^ h * 5 ^ (H - h)

/-- Clear the radius denominator in any finite sum of absolute coefficients. -/
theorem sum_abs_mul_pow_eq (H : ℕ) (s : Finset ℕ) (hs : ∀ h ∈ s, h ≤ H)
    (f : ℕ → ℤ) :
    ((∑ h ∈ s, |f h| * (4 : ℤ) ^ h * 5 ^ (H - h) : ℤ) : ℚ) =
      (5 : ℚ) ^ H * ∑ h ∈ s, |(f h : ℚ)| * (4 / 5 : ℚ) ^ h := by
  simp only [Int.cast_sum, Int.cast_mul, Int.cast_abs, Int.cast_pow, Int.cast_ofNat, mul_sum]
  apply sum_congr rfl
  intro h hh
  have hp : (5 : ℚ) ^ (H - h) * 5 ^ h = 5 ^ H := by
    rw [← pow_add, Nat.sub_add_cancel (hs h hh)]
  rw [div_pow]
  field_simp
  rw [← hp]
  ring

/-- The array numerator is exactly `5^H` times its weighted coefficient sum. -/
theorem arrayNormNumerator_eq (H : ℕ) (row : Array ℤ) :
    (arrayNormNumerator H row : ℚ) = (5 : ℚ) ^ H *
      ∑ h ∈ range (H + 1), |(row.getD h 0 : ℚ)| * (4 / 5 : ℚ) ^ h :=
  sum_abs_mul_pow_eq H _ (fun _ hh => Nat.le_of_lt_succ (mem_range.mp hh)) _

/-- The normalized integer array norm is the actual difference-row norm. -/
theorem arrayNormNumerator_shortCoefficientTable {k H n : ℕ} (hn : n ≤ H) :
    (arrayNormNumerator H ((shortCoefficientTable k H).getD n #[]) : ℚ) =
      (n.factorial : ℚ) * 5 ^ H * coefficientNorm (4 / 5 : ℚ) (differenceRow k n) := by
  classical
  rw [arrayNormNumerator_eq, coefficientNorm_eq_sum (s := range (H + 1)) (by
    intro h hh
    have he := le_natDegree_of_mem_supp h hh
    exact mem_range.mpr (by have := natDegree_differenceRow_le k n; lia))]
  simp only [mul_sum]
  apply sum_congr rfl
  intro h hh
  rw [shortCoefficientTable_correct k H hn (Nat.le_of_lt_succ (mem_range.mp hh)), abs_mul,
    abs_of_nonneg (Nat.cast_nonneg n.factorial)]
  ring

/-- Exact weighted norm of the excluded kernel. This definition is used in
proofs; the certificate clears its denominators. -/
def shortKernelNorm (k i : ℕ) : ℚ :=
  ∑ h ∈ range (i + 1), |(shortKernelCell k i h : ℚ)| * (4 / 5 : ℚ) ^ h

/-- The executable scalar formula agrees with the actual polynomial norm. -/
theorem shortKernelNorm_eq (k i : ℕ) :
    shortKernelNorm k i = coefficientNorm (4 / 5 : ℚ) (shortKernel k i) := by
  classical
  rw [coefficientNorm_eq_sum (s := range (i + 1)) (by
    intro h hh
    have he := le_natDegree_of_mem_supp h hh
    exact mem_range.mpr (by have := natDegree_shortKernel_le k i; lia))]
  simp [shortKernelNorm, shortKernelCell_eq]

end RealRooted.LongCycleDescents.Structural

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
    exact (mul_le_mul_of_nonneg_right
      (show |(μ d : ℚ)| ≤ 1 from by exact_mod_cast ArithmeticFunction.abs_moebius_le_one)
      (by positivity)).trans_eq
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
