/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.Algebra.Polynomial.Coeff

import Mathlib.Tactic.Linarith

/-!
# Coefficients of descending degree-box sums

This Mathlib-shaped shim packages coefficient extraction for polynomial sums
whose exponents descend through a finite degree box.
-/

public section

open BigOperators

namespace Polynomial

/-- The coefficient of a degree-box sum with descending exponents. -/
theorem coeff_sum_range_C_mul_X_pow_sub {R : Type*} [Semiring R] (a : ℕ → R)
    (n j : ℕ) :
    (∑ k ∈ Finset.range (n + 1), C (a k) * X ^ (n - k)).coeff j =
      if j ≤ n then a (n - j) else 0 := by
  by_cases hj : j ≤ n
  · rw [finsetSum_coeff]
    rw [Finset.sum_eq_single_of_mem (n - j)
        (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr (Nat.sub_le n j)))]
    · rw [coeff_C_mul, coeff_X_pow, Nat.sub_sub_self hj, if_pos rfl, mul_one,
        if_pos hj]
    · intro k hk hkne
      have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      rw [coeff_C_mul, coeff_X_pow, if_neg (fun h => hkne (by lia)), mul_zero]
  · rw [finsetSum_coeff, if_neg hj]
    apply Finset.sum_eq_zero
    intro k hk
    rw [coeff_C_mul, coeff_X_pow, if_neg (fun _ => by lia), mul_zero]

end Polynomial
