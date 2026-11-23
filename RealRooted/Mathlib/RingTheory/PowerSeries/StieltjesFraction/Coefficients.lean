/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import RealRooted.Mathlib.RingTheory.PowerSeries.StieltjesFraction.Tail
public import Mathlib.Basic.Real.Basic

/-!
# Coefficients of formal Stieltjes fractions

The tail identity yields the Stieltjes--Rogers convolution recurrence. In
particular, nonnegative numerator data give nonnegative formal coefficients.
This is not yet the stronger Stieltjes moment representation theorem.
-/

public section

open scoped BigOperators

namespace PowerSeries

variable {R : Type*} [CommRing R]

/-- The multiplicative tail recurrence with its degree shift explicit. -/
theorem stieltjesTail_eq_one_add (a : ℕ → R) (s : ℕ) :
    stieltjesTail a s =
      1 + X * (C (a s) * (stieltjesTail a s * stieltjesTail a (s + 1))) := by
  calc
    stieltjesTail a s =
        1 + C (a s) * X * stieltjesTail a (s + 1) * stieltjesTail a s := by
      simpa only [← stieltjesTail_eq_step a s] using
        stieltjesStep_eq_one_add (a s) (stieltjesTail a (s + 1))
    _ = _ := by ring

/-- The Stieltjes--Rogers convolution recurrence for the formal coefficients. -/
theorem coeff_stieltjesTail_succ (a : ℕ → R) (s n : ℕ) :
    coeff (n + 1) (stieltjesTail a s) = a s *
      ∑ ij ∈ Finset.antidiagonal n,
        coeff ij.1 (stieltjesTail a s) * coeff ij.2 (stieltjesTail a (s + 1)) := by
  have h := congrArg (coeff (n + 1)) (stieltjesTail_eq_one_add a s)
  have hn : n + 1 ≠ 0 := by lia
  rw [map_add, coeff_one, ite_eq_right hn, zero_add, coeff_succ_X_mul,
    coeff_C_mul, coeff_mul] at h
  exact h

/-- The first nonconstant coefficient recovers the first numerator. -/
@[simp] theorem coeff_one_stieltjesTail (a : ℕ → R) (s : ℕ) :
    coeff 1 (stieltjesTail a s) = a s := by
  simpa using coeff_stieltjesTail_succ a s 0

/-- Nonnegative Stieltjes numerator data give nonnegative formal coefficients. -/
theorem coeff_stieltjesTail_nonneg {a : ℕ → ℝ} (ha : ∀ i, 0 ≤ a i) (n s : ℕ) :
    0 ≤ coeff n (stieltjesTail a s) := by
  induction n using Nat.strong_induction_on generalizing s with
  | ind n ih =>
      cases n with
      | zero => simp
      | succ n =>
          rw [coeff_stieltjesTail_succ]
          apply mul_nonneg (ha s)
          apply Finset.sum_nonneg
          intro ij hij
          have hij' := Finset.mem_antidiagonal.mp hij
          exact mul_nonneg (ih ij.1 (by lia) s) (ih ij.2 (by lia) (s + 1))

end PowerSeries
