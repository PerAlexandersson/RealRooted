/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import RealRooted.CombinatorialExamples.LongCycleDescents.Structural.ShortKernel
public import RealRooted.IntervalDifferential.EulerCoefficientTable
public import RealRooted.IntervalDifferential.CoefficientNorm
import RealRooted.IntervalDifferential.EulerNorm
import Mathlib.Tactic

/-!
# Executable short-kernel coefficients

The scalar divisor formula computes the coefficients of the actual excluded
kernel. The generic Euler table then computes its difference rows exactly.

Adapted from Bowen Zuo, cycle-minimum-descent-real-roots v1.0.0 (Apache-2.0)
-/

@[expose] public section

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
