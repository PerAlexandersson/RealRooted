/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Elementary majorant estimates for partial sums of power series

Adapted from Aristotle's centered-disk proof, `RequestProject/Majorants.lean` (2026-10-23).
-/

@[expose] public section

open PowerSeries

namespace RealRooted.CenteredEulerian

/-- Coefficientwise absolute value. -/
noncomputable def absPS (P : ℝ⟦X⟧) : ℝ⟦X⟧ := mk (fun n => |coeff n P|)

lemma coeff_absPS (P : ℝ⟦X⟧) (n : ℕ) : coeff n (absPS P) = |coeff n P| := by
  rw [absPS, coeff_mk]

/-- Nonnegative coefficients. -/
def NonnegPS (P : ℝ⟦X⟧) : Prop := ∀ n, 0 ≤ coeff n P

lemma nonnegPS_absPS (P : ℝ⟦X⟧) : NonnegPS (absPS P) := fun n => by
  rw [coeff_absPS]; exact abs_nonneg _

lemma NonnegPS.mul {P Q : ℝ⟦X⟧} (hP : NonnegPS P) (hQ : NonnegPS Q) : NonnegPS (P * Q) :=
  fun n => by
    rw [coeff_mul]
    exact Finset.sum_nonneg (fun p _ => mul_nonneg (hP _) (hQ _))

lemma NonnegPS.pow {P : ℝ⟦X⟧} (hP : NonnegPS P) (j : ℕ) : NonnegPS (P ^ j) := by
  induction j with
  | zero => intro n; rw [pow_zero, coeff_one]; split_ifs <;> norm_num
  | succ j ih => rw [pow_succ]; exact ih.mul hP

lemma abs_coeff_mul_le (P Q : ℝ⟦X⟧) (n : ℕ) :
    |coeff n (P * Q)| ≤ coeff n (absPS P * absPS Q) := by
  rw [coeff_mul, coeff_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
  apply Finset.sum_congr rfl; intro p _
  rw [abs_mul, coeff_absPS, coeff_absPS]

/-- Coefficientwise domination. -/
def DomPS (P P' : ℝ⟦X⟧) : Prop := ∀ n, |coeff n P| ≤ coeff n P'

lemma DomPS.mul {P P' Q Q' : ℝ⟦X⟧} (hP : DomPS P P') (hQ : DomPS Q Q') :
    DomPS (P * Q) (P' * Q') := fun n => by
  rw [coeff_mul, coeff_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun p _ => ?_))
  rw [abs_mul]
  exact mul_le_mul (hP _) (hQ _) (abs_nonneg _) ((abs_nonneg _).trans (hP _))

lemma DomPS.pow {P P' : ℝ⟦X⟧} (hP : DomPS P P') (j : ℕ) : DomPS (P ^ j) (P' ^ j) := by
  induction j with
  | zero => intro n; rw [pow_zero, pow_zero, coeff_one]; split_ifs <;> norm_num
  | succ j ih => rw [pow_succ, pow_succ]; exact ih.mul hP

lemma DomPS.nonneg {P P' : ℝ⟦X⟧} (h : DomPS P P') : NonnegPS P' :=
  fun n => (abs_nonneg _).trans (h n)

/-- Partial sums of a product are dominated by products of partial sums. -/
lemma sum_coeff_mul_le {P Q : ℝ⟦X⟧} (hP : NonnegPS P) (hQ : NonnegPS Q)
    {x : ℝ} (hx : 0 ≤ x)
    (K : ℕ) :
    ∑ k ∈ Finset.range K, coeff k (P * Q) * x ^ k ≤
      (∑ k ∈ Finset.range K, coeff k P * x ^ k) *
        (∑ k ∈ Finset.range K, coeff k Q * x ^ k) := by
  have hL : ∑ k ∈ Finset.range K, coeff k (P * Q) * x ^ k =
      ∑ k ∈ Finset.range K, ∑ i ∈ Finset.range (k + 1),
        coeff i P * x ^ i * (coeff (k - i) Q * x ^ (k - i)) := by
    apply Finset.sum_congr rfl; intro k _
    rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_mul]
    apply Finset.sum_congr rfl; intro i hi
    simp only [Finset.mem_range] at hi
    rw [show x ^ k = x ^ i * x ^ (k - i) by rw [← pow_add]; congr 1; lia]
    ring
  rw [hL, Finset.sum_mul_sum]
  have hcomm : ∑ k ∈ Finset.range K, ∑ i ∈ Finset.range (k + 1),
      coeff i P * x ^ i * (coeff (k - i) Q * x ^ (k - i)) =
      ∑ i ∈ Finset.range K, ∑ k ∈ Finset.Ico i K,
        coeff i P * x ^ i * (coeff (k - i) Q * x ^ (k - i)) := by
    simp only [Finset.range_eq_Ico]
    rw [Finset.sum_Ico_Ico_comm]
  rw [hcomm]
  apply Finset.sum_le_sum
  intro i hi
  rw [Finset.sum_Ico_eq_sum_range]
  simp only [add_tsub_cancel_left]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro j hj
    simp only [Finset.mem_range] at hj ⊢
    lia
  · intro j _ _
    exact mul_nonneg (mul_nonneg (hP _) (pow_nonneg hx _)) (mul_nonneg (hQ _) (pow_nonneg hx _))

lemma sum_coeff_pow_le {P : ℝ⟦X⟧} (hP : NonnegPS P) {x : ℝ} (hx : 0 ≤ x) (K j : ℕ) :
    ∑ k ∈ Finset.range K, coeff k (P ^ j) * x ^ k ≤
      (∑ k ∈ Finset.range K, coeff k P * x ^ k) ^ j := by
  induction j with
  | zero =>
    rw [pow_zero, pow_zero]
    rcases K with _ | K
    · simp
    · rw [Finset.sum_range_succ']
      simp only [coeff_one, pow_zero, mul_one, ite_true]
      rw [Finset.sum_eq_zero (fun k _ => by rw [ite_eq_right (by lia), zero_mul])]
      norm_num
  | succ j ih =>
    rw [pow_succ, pow_succ]
    refine (sum_coeff_mul_le (hP.pow j) hP hx K).trans ?_
    apply mul_le_mul_of_nonneg_right ih
    exact Finset.sum_nonneg (fun k _ => mul_nonneg (hP _) (pow_nonneg hx _))

end RealRooted.CenteredEulerian
