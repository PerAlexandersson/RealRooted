/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import RealRooted.CombinatorialExamples.LongCycleDescents.Structural.AlphabetReflection
import Mathlib.Tactic

/-!
# The complementary short-cycle kernel

Möbius inversion gives the unrestricted necklace identity. It identifies the
complement of the allowed kernel with the finitely many excluded lengths.

Adapted from Bowen Zuo, cycle-minimum-descent-real-roots v1.0.0 (Apache-2.0)
-/

@[expose] public section

noncomputable section

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
