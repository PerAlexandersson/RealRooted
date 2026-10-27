/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.Ring
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs

/-!
# Inequalities for finite sums in an ordered ring

This file proves a cubic power-sum inequality for finite sums (RealRooted issue #1920).
The proof was found by Aristotle (Harmonic).
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

end Finset

