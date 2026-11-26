/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic

/-!
# Tail bounds for a nonnegative Euler convolution

A finite prefix and kernel-tail budgets control every subsequent partial sum.
-/

public section

open Finset

namespace RealRooted.IntervalDifferential

private theorem shifted_tail (t : ℕ → ℚ) {N M j : ℕ} (hj : j < M) :
    (∑ n ∈ Ico N M, if j < n then t (n - j) else 0) =
      ∑ i ∈ Ico (max N (j + 1) - j) (M - j), t i := by
  rw [← sum_filter]
  have hs : (Ico N M).filter (fun n => j < n) = Ico (max N (j + 1)) M := by
    ext n
    simp only [mem_filter, mem_Ico, max_le_iff]
    lia
  rw [hs]
  have he := sum_Ico_add_right_sub_eq (f := t) (max N (j + 1) - j) (M - j) j
  have hl : j ≤ max N (j + 1) := (Nat.le_succ j).trans (le_max_right _ _)
  simpa only [Nat.sub_add_cancel hl, Nat.sub_add_cancel hj.le] using he

/-- Summing an Euler convolution above a cutoff bounds the tail by a finite
prefix, with the full kernel mass subtracted from the cutoff. -/
theorem sum_euler_tail_bound (t e S : ℕ → ℚ)
    (he : ∀ i, 0 ≤ e i)
    (hrec : ∀ (n : ℕ), n ≠ 0 → (n : ℚ) * e n ≤ ∑ j ∈ range n, t (n - j) * e j)
    {N M : ℕ} (hN : 0 < N) (hNM : N ≤ M)
    (hS : ∀ l, 0 < l → l ≤ N → ∀ B, ∑ i ∈ Ico l B, t i ≤ S l) :
    ((N : ℚ) - S 1) * (∑ n ∈ Ico N M, e n) ≤
      ∑ j ∈ range N, e j * S (N - j) := by
  have hfirst : (N : ℚ) * (∑ n ∈ Ico N M, e n) ≤
      ∑ n ∈ Ico N M, ∑ j ∈ range n, t (n - j) * e j := by
    rw [mul_sum]
    apply sum_le_sum
    intro n hn
    have hnn := mem_Ico.mp hn
    exact (mul_le_mul_of_nonneg_right (by exact_mod_cast hnn.1) (he n)).trans
      (hrec n (by lia))
  have hpad n (hn : n ∈ Ico N M) :
      (∑ j ∈ range n, t (n - j) * e j) =
        ∑ j ∈ range M, if j < n then t (n - j) * e j else 0 := by
    rw [← sum_filter]
    congr 1
    ext j
    have hnn := mem_Ico.mp hn
    simp only [mem_filter, mem_range]
    lia
  have hrect : (∑ n ∈ Ico N M, ∑ j ∈ range n, t (n - j) * e j) =
      ∑ j ∈ range M, e j * (∑ n ∈ Ico N M, if j < n then t (n - j) else 0) := by
    calc
      _ = ∑ n ∈ Ico N M, ∑ j ∈ range M, if j < n then t (n - j) * e j else 0 :=
        sum_congr rfl hpad
      _ = ∑ j ∈ range M, ∑ n ∈ Ico N M, if j < n then t (n - j) * e j else 0 := sum_comm
      _ = _ := by
        apply sum_congr rfl
        intro j _
        rw [mul_sum]
        exact sum_congr rfl (fun n _ => by split_ifs <;> ring)
  rw [hrect] at hfirst
  have hbound : (∑ j ∈ range M, e j * (∑ n ∈ Ico N M, if j < n then t (n - j) else 0)) ≤
      ∑ j ∈ range M, e j * S (if j < N then N - j else 1) := by
    apply sum_le_sum
    intro j hj
    rw [shifted_tail t (mem_range.mp hj)]
    have hl : max N (j + 1) - j = if j < N then N - j else 1 := by
      split_ifs <;> lia
    rw [hl]
    apply mul_le_mul_of_nonneg_left _ (he j)
    apply hS <;> split_ifs <;> lia
  have hsplit : (∑ j ∈ range M, e j * S (if j < N then N - j else 1)) =
      (∑ j ∈ range N, e j * S (N - j)) + S 1 * ∑ j ∈ Ico N M, e j := by
    rw [← sum_range_add_sum_Ico _ hNM, mul_sum]
    congr 1
    · exact sum_congr rfl (fun j hj => by rw [ite_eq_left (mem_range.mp hj)])
    · exact sum_congr rfl (fun j hj => by
        rw [ite_eq_right (by have := mem_Ico.mp hj; lia)]
        ring)
  rw [hsplit] at hbound
  nlinarith

end RealRooted.IntervalDifferential
