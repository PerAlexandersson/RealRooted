/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-!
# Newton coefficients of derivatives of ordered products

We use an algebraic Newton expansion, which permits repeated nodes. The coefficients of the
polynomial obtained by deleting one linear factor are tail products of differences of nodes.
For ordered nonnegative parameters this gives nonnegative derivative coefficients and the
inequality needed for exponential coefficient rows.

Source: unpublished argument in RealRooted issue #2415,
https://github.com/PerAlexandersson/RealRooted/issues/2415.
-/

@[expose] public section

open Finset

namespace Polynomial

/-- Tail-product coefficients for deleting the factor indexed by `i` in a Newton product. -/
noncomputable def newtonOmitCoeff (r : ℕ → ℝ) (n j i : ℕ) : ℝ :=
  ∏ k ∈ Ico (j + 1) n, (r k - r i)

/-- Newton coefficients of the derivative of `∏ k < n, (X + C (r k))`. -/
noncomputable def newtonDerivativeCoeff (r : ℕ → ℝ) (n j : ℕ) : ℝ :=
  ∑ i ∈ range n, newtonOmitCoeff r n j i

private lemma newtonOmitCoeff_succ {r : ℕ → ℝ} {n j : ℕ} (hj : j < n) (i : ℕ) :
    newtonOmitCoeff r (n + 1) j i = newtonOmitCoeff r n j i * (r n - r i) := by
  simp [newtonOmitCoeff, prod_Ico_succ_top (by lia : j + 1 ≤ n)]

private lemma newton_sum_mul (r : ℕ → ℝ) (n i : ℕ) :
    (X + C (r i)) *
        (∑ j ∈ range n, C (newtonOmitCoeff r n j i) *
          ∏ k ∈ range j, (X + C (r k))) =
      (∏ k ∈ range n, (X + C (r k))) - C (∏ k ∈ range n, (r k - r i)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ]
    have hsum :
        (∑ j ∈ range n, C (newtonOmitCoeff r (n + 1) j i) *
          ∏ k ∈ range j, (X + C (r k))) =
        C (r n - r i) *
          (∑ j ∈ range n, C (newtonOmitCoeff r n j i) *
            ∏ k ∈ range j, (X + C (r k))) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro j hj
      rw [newtonOmitCoeff_succ (mem_range.mp hj), map_mul]
      ring
    rw [hsum]
    have htop : newtonOmitCoeff r (n + 1) n i = 1 := by
      simp [newtonOmitCoeff]
    rw [htop, map_one, one_mul]
    rw [mul_add]
    rw [show (X + C (r i)) * (C (r n - r i) *
        (∑ j ∈ range n, C (newtonOmitCoeff r n j i) *
          ∏ k ∈ range j, (X + C (r k)))) =
        C (r n - r i) * ((X + C (r i)) *
          (∑ j ∈ range n, C (newtonOmitCoeff r n j i) *
            ∏ k ∈ range j, (X + C (r k)))) by ring, ih]
    simp only [prod_range_succ, map_mul, map_sub]
    ring

/-- The Newton expansion of a product with one factor omitted, valid also at repeated nodes. -/
theorem prod_erase_eq_sum_newtonOmitCoeff (r : ℕ → ℝ) {n i : ℕ} (hi : i < n) :
    (∏ k ∈ (range n).erase i, (X + C (r k))) =
      ∑ j ∈ range n, C (newtonOmitCoeff r n j i) *
        ∏ k ∈ range j, (X + C (r k)) := by
  apply mul_left_cancel₀ (X_add_C_ne_zero (r i))
  rw [mul_prod_erase (range n) (fun k => (X : ℝ[X]) + C (r k)) (mem_range.mpr hi), newton_sum_mul]
  have hz : (∏ k ∈ range n, (r k - r i)) = 0 :=
    prod_eq_zero (mem_range.mpr hi) (sub_self (r i))
  simp [hz]

/-- The derivative of a monic product in its partial-product Newton basis. -/
theorem derivative_prod_eq_sum_newtonDerivativeCoeff (r : ℕ → ℝ) (n : ℕ) :
    (∏ k ∈ range n, (X + C (r k))).derivative =
      ∑ j ∈ range n, C (newtonDerivativeCoeff r n j) *
        ∏ k ∈ range j, (X + C (r k)) := by
  rw [derivative_prod_finset]
  simp only [derivative_add, derivative_X, derivative_C, add_zero, mul_one]
  have hsum :
      (∑ i ∈ range n, ∏ k ∈ (range n).erase i, (X + C (r k))) =
        ∑ i ∈ range n, ∑ j ∈ range n, C (newtonOmitCoeff r n j i) *
          ∏ k ∈ range j, (X + C (r k)) := by
    apply sum_congr rfl
    intro i hi
    exact prod_erase_eq_sum_newtonOmitCoeff r (mem_range.mp hi)
  rw [hsum, sum_comm]
  apply sum_congr rfl
  intro j hj
  simp [newtonDerivativeCoeff, map_sum, sum_mul]

/-- Omitting a factor to the right of the coefficient index gives a zero coefficient. -/
theorem newtonOmitCoeff_eq_zero {r : ℕ → ℝ} {n j i : ℕ}
    (hji : j < i) (hin : i < n) : newtonOmitCoeff r n j i = 0 := by
  exact prod_eq_zero (mem_Ico.mpr ⟨by lia, hin⟩) (sub_self (r i))

/-- Ordered parameters make all omitted-factor Newton coefficients nonnegative. -/
theorem newtonOmitCoeff_nonneg {r : ℕ → ℝ} (hr : Monotone r)
    {n j i : ℕ} (hi : i < n) : 0 ≤ newtonOmitCoeff r n j i := by
  by_cases hji : j < i
  · rw [newtonOmitCoeff_eq_zero hji hi]
  · apply prod_nonneg
    intro k hk
    exact sub_nonneg.mpr (hr (by have := (mem_Ico.mp hk).1; lia))

/-- The derivative Newton coefficients of an ordered product are nonnegative. -/
theorem newtonDerivativeCoeff_nonneg {r : ℕ → ℝ} (hr : Monotone r) (n j : ℕ) :
    0 ≤ newtonDerivativeCoeff r n j := by
  exact sum_nonneg fun i hi => newtonOmitCoeff_nonneg hr (mem_range.mp hi)

/-- Adjacent derivative Newton coefficients satisfy the weighted monotonicity inequality. -/
theorem newtonDerivativeCoeff_le_mul_succ {r : ℕ → ℝ} (hr : Monotone r)
    (hpos : ∀ i, 0 ≤ r i) {n j : ℕ} (hj : j + 1 < n) :
    newtonDerivativeCoeff r n j ≤ r (j + 1) * newtonDerivativeCoeff r n (j + 1) := by
  unfold newtonDerivativeCoeff
  rw [mul_sum]
  apply sum_le_sum
  intro i hi
  have htail : newtonOmitCoeff r n j i =
      (r (j + 1) - r i) * newtonOmitCoeff r n (j + 1) i := by
    exact Finset.prod_eq_prod_Ico_succ_bot (by lia : j + 1 < n)
      (fun k => r k - r i)
  rw [htail]
  exact mul_le_mul_of_nonneg_right (sub_le_self _ (hpos i))
    (newtonOmitCoeff_nonneg hr (mem_range.mp hi))

/-- The top derivative Newton coefficient is the number of factors. -/
theorem newtonDerivativeCoeff_top (r : ℕ → ℝ) (n : ℕ) :
    newtonDerivativeCoeff r (n + 1) n = n + 1 := by
  simp [newtonDerivativeCoeff, newtonOmitCoeff]

/-- Two zero nodes make the first derivative Newton coefficient twice the remaining product. -/
theorem newtonDerivativeCoeff_one {r : ℕ → ℝ} (hr₀ : r 0 = 0) (hr₁ : r 1 = 0)
    (n : ℕ) :
    newtonDerivativeCoeff r (n + 2) 1 = 2 * ∏ k ∈ Ico 2 (n + 2), r k := by
  unfold newtonDerivativeCoeff
  have hsub : range 2 ⊆ range (n + 2) := range_mono (by lia)
  rw [← sum_subset hsub]
  · simp [sum_range_succ, newtonOmitCoeff, hr₀, hr₁]
    ring
  · intro i hi hnot
    apply newtonOmitCoeff_eq_zero
    · have : ¬ i < 2 := by simpa using hnot
      lia
    · exact mem_range.mp hi

/-- Two zero nodes force the constant derivative Newton coefficient to vanish. -/
theorem newtonDerivativeCoeff_zero {r : ℕ → ℝ} (hr₀ : r 0 = 0) (hr₁ : r 1 = 0)
    (n : ℕ) : newtonDerivativeCoeff r (n + 2) 0 = 0 := by
  apply sum_eq_zero
  intro i hi
  by_cases hi₀ : i = 0
  · subst i
    unfold newtonOmitCoeff
    apply prod_eq_zero (i := 1)
    · exact mem_Ico.mpr ⟨by lia, by lia⟩
    · simp [hr₀, hr₁]
  · exact newtonOmitCoeff_eq_zero (by lia) (mem_range.mp hi)

end Polynomial
