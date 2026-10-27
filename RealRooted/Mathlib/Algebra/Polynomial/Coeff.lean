/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

import Mathlib.Algebra.Polynomial.Coeff

import Mathlib.Tactic.Linarith
public import Mathlib.Algebra.Polynomial.Basic

/-!
# Coefficients of descending degree-box sums

This Mathlib-shaped shim packages coefficient extraction for polynomial sums
whose exponents descend through a finite degree box, and the coefficients of
`(1 - X) * p`.
-/

public section

open BigOperators

namespace Polynomial

/-- The coefficient of a monomial sum indexed by a finite set. -/
theorem coeff_sum_finset_monomial {R : Type*} [Semiring R]
    (s : Finset ℕ) (a : ℕ → R) (k : ℕ) :
    (∑ i ∈ s, monomial i (a i)).coeff k =
      if k ∈ s then a k else 0 := by
  simp only [finsetSum_coeff, coeff_monomial]
  rw [Finset.sum_ite_eq' s k]

/-- The coefficient of a finite initial-segment monomial sum. -/
theorem coeff_sum_range_monomial {R : Type*} [Semiring R] (a : ℕ → R)
    (n k : ℕ) :
    (∑ i ∈ Finset.range n, monomial i (a i)).coeff k =
      if k < n then a k else 0 := by
  simpa using coeff_sum_finset_monomial (Finset.range n) a k

/-- The coefficient of a degree-box sum with descending exponents. -/
theorem coeff_sum_range_C_mul_X_pow_sub {R : Type*} [Semiring R] (a : ℕ → R)
    (n j : ℕ) :
    (∑ k ∈ Finset.range (n + 1), C (a k) * X ^ (n - k)).coeff j =
      if j ≤ n then a (n - j) else 0 := by
  by_cases hj : j ≤ n
  · rw [finsetSum_coeff]
    rw [Finset.sum_eq_single_of_mem (n - j)
        (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr (Nat.sub_le n j)))]
    · rw [coeff_C_mul, coeff_X_pow, Nat.sub_sub_self hj, ite_eq_left rfl, mul_one,
        ite_eq_left hj]
    · intro k hk hkne
      have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      rw [coeff_C_mul, coeff_X_pow, ite_eq_right (fun h => hkne (by lia)), mul_zero]
  · rw [finsetSum_coeff, ite_eq_right hj]
    apply Finset.sum_eq_zero
    intro k hk
    rw [coeff_C_mul, coeff_X_pow, ite_eq_right (fun _ => by lia), mul_zero]

theorem coeff_one_sub_X_mul_zero {R : Type*} [Ring R] (p : R[X]) :
    ((1 - X) * p).coeff 0 = p.coeff 0 := by
  simp [sub_mul]

theorem coeff_one_sub_X_mul_succ {R : Type*} [Ring R] (p : R[X]) (k : ℕ) :
    ((1 - X) * p).coeff (k + 1) = p.coeff (k + 1) - p.coeff k := by
  rw [sub_mul, one_mul, coeff_sub, coeff_X_mul]

/-- The coefficient of `(1 - X) ^ n` is the signed binomial coefficient. -/
theorem coeff_one_sub_X_pow {R : Type*} [CommRing R] (n k : ℕ) :
    ((1 - X : R[X]) ^ n).coeff k = (-1 : R) ^ k * (n.choose k : R) := by
  rw [show (1 - X : R[X]) = -(X + C (-1 : R)) by
    ext m
    simp [sub_eq_add_neg]]
  rw [neg_pow]
  rw [show ((-1 : R[X]) ^ n) = C ((-1 : R) ^ n) by simp]
  rw [coeff_C_mul]
  rw [Polynomial.coeff_X_add_C_pow]
  by_cases hk : k ≤ n
  · have hsign : (-1 : R) ^ n * (-1 : R) ^ (n - k) = (-1 : R) ^ k := by
      nth_rw 1 [← Nat.add_sub_of_le hk]
      rw [pow_add, mul_assoc, ← pow_add]
      simp
    grind
  · have hchoose : n.choose k = 0 := Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hk)
    simp [hchoose]

end Polynomial
