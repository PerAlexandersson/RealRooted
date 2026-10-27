/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs

/-!
# Inequalities for finite sums in an ordered ring

This file proves a cubic power-sum inequality for finite sums (RealRooted issue #1920).
The proof was found by Aristotle (Harmonic).

It also bounds finite alternating sums `∑ i ∈ range N, (-1) ^ i * T i` of a nonnegative antitone
sequence `T` between `T 0 - T 1` and `T 0` (the Leibniz bounds). These were upstreamed from
real-rooted-oeis-proofs (`ProofsOeis/AlternatingSum.lean`).
-/

public section

namespace Finset

/-- The square of a finite sum of cubes is bounded by the cube of the sum of squares. -/
theorem sq_sum_pow_three_le_pow_three_sum_sq {ι : Type*} (s : Finset ι) (y : ι → ℝ) :
    (∑ i ∈ s, y i ^ 3) ^ 2 ≤ (∑ i ∈ s, y i ^ 2) ^ 3 := by
  set S := ∑ i ∈ s, y i ^ 2 with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg (fun i _ => sq_nonneg (y i))
  have hyi : ∀ i ∈ s, |y i| ≤ Real.sqrt S := by
    intro i hi
    rw [← Real.sqrt_sq_eq_abs]
    apply Real.sqrt_le_sqrt
    exact Finset.single_le_sum (f := fun j => y j ^ 2) (fun j _ => sq_nonneg (y j)) hi
  have h1 : |∑ i ∈ s, y i ^ 3| ≤ Real.sqrt S * S := by
    calc
      |∑ i ∈ s, y i ^ 3| ≤ ∑ i ∈ s, |y i ^ 3| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ s, Real.sqrt S * y i ^ 2 := by
        apply Finset.sum_le_sum
        intro i hi
        rw [abs_pow, pow_succ']
        have : |y i| ^ 2 = y i ^ 2 := sq_abs _
        rw [this]
        exact mul_le_mul_of_nonneg_right (hyi i hi) (sq_nonneg _)
      _ = Real.sqrt S * S := by rw [← Finset.mul_sum]
  have h2 : (∑ i ∈ s, y i ^ 3) ^ 2 ≤ (Real.sqrt S * S) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  calc
    (∑ i ∈ s, y i ^ 3) ^ 2 ≤ (Real.sqrt S * S) ^ 2 := h2
    _ = S ^ 3 := by rw [mul_pow, Real.sq_sqrt hS0]; ring

section AlternatingSum

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

/-- A finite alternating sum of a nonnegative antitone sequence is nonnegative. -/
theorem sum_range_neg_one_pow_mul_nonneg_of_antitone (N : ℕ) {T : ℕ → R} (hT : Antitone T)
    (h0 : ∀ i, 0 ≤ T i) : 0 ≤ ∑ i ∈ range N, (-1 : R) ^ i * T i := by
  induction N using Nat.strong_induction_on generalizing T with
  | _ N ih =>
    match N with
    | 0 => simp
    | 1 => simpa using h0 0
    | n + 2 =>
      have hsplit : ∑ i ∈ range (n + 2), (-1 : R) ^ i * T i
          = (∑ i ∈ range n, (-1 : R) ^ i * T (i + 2)) + (T 0 - T 1) := by
        rw [sum_range_succ', sum_range_succ']
        simp only [pow_zero, one_mul, pow_succ]
        ring_nf
      rw [hsplit]
      have := ih n (by lia) (T := fun i => T (i + 2)) (fun i j hij => hT (by lia))
        (fun i => h0 (i + 2))
      have := hT (Nat.zero_le 1)
      linarith

/-- A finite alternating sum of a nonnegative antitone sequence is at most its first term. -/
theorem sum_range_neg_one_pow_mul_le_of_antitone {N : ℕ} (hN : N ≠ 0) {T : ℕ → R}
    (hT : Antitone T) (h0 : ∀ i, 0 ≤ T i) : ∑ i ∈ range N, (-1 : R) ^ i * T i ≤ T 0 := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by lia⟩
  have hsplit : ∑ i ∈ range (n + 1), (-1 : R) ^ i * T i
      = T 0 - ∑ i ∈ range n, (-1 : R) ^ i * T (i + 1) := by
    rw [sum_range_succ', pow_zero, one_mul, sub_eq_add_neg, add_comm, ← sum_neg_distrib]
    congr 1
    refine sum_congr rfl fun i _ => ?_
    ring
  rw [hsplit]
  have := sum_range_neg_one_pow_mul_nonneg_of_antitone n (T := fun i => T (i + 1))
    (fun i j hij => hT (by lia)) (fun i => h0 (i + 1))
  linarith

/-- A finite alternating sum with at least two terms of a nonnegative antitone sequence is at
least its first two terms. -/
theorem sub_le_sum_range_neg_one_pow_mul_of_antitone {N : ℕ} (hN : 2 ≤ N) {T : ℕ → R}
    (hT : Antitone T) (h0 : ∀ i, 0 ≤ T i) :
    T 0 - T 1 ≤ ∑ i ∈ range N, (-1 : R) ^ i * T i := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 2 := ⟨N - 2, by lia⟩
  have hsplit : ∑ i ∈ range (n + 2), (-1 : R) ^ i * T i
      = (∑ i ∈ range n, (-1 : R) ^ i * T (i + 2)) + (T 0 - T 1) := by
    rw [sum_range_succ', sum_range_succ']
    simp only [pow_zero, one_mul, pow_succ]
    ring_nf
  rw [hsplit]
  have := sum_range_neg_one_pow_mul_nonneg_of_antitone n (T := fun i => T (i + 2))
    (fun i j hij => hT (by lia)) (fun i => h0 (i + 2))
  linarith

end AlternatingSum

end Finset
