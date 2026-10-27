/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.Algebra.Order.Antidiag.Pi
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Tactic.LinearCombination

/-!
# Iterated derivatives of products of powers of linear factors

The multinomial Leibniz rule for `∏ i ∈ s, (X + C (a i)) ^ n i`:
its `k`-th derivative is `k! ∑_{|α| = k} ∏ i, (n i).choose (α i) * (X + C (a i)) ^ (n i - α i)`,
the sum running over `s.piAntidiag k`.  When every `n i ≥ m ≥ k`, the common factor
`∏ i, (X + C (a i)) ^ (n i - m)` can be pulled out; this is the cluster derivative identity of
RealRooted issue #1917.  The proofs were found by Aristotle (Harmonic).
-/

public section

open Finset

namespace Polynomial

variable {R ι : Type*} [CommRing R] [DecidableEq ι]

/-- The multinomial Leibniz rule for a product of powers of linear factors. -/
theorem iterate_derivative_prod_X_add_C_pow (a : ι → R) (n : ι → ℕ) (s : Finset ι) (k : ℕ) :
    derivative^[k] (∏ i ∈ s, (X + C (a i)) ^ n i) =
      (k.factorial : R[X]) *
        ∑ α ∈ s.piAntidiag k,
          ∏ i ∈ s, ((n i).choose (α i) : R[X]) * (X + C (a i)) ^ (n i - α i) := by
  induction s using Finset.cons_induction generalizing k with
  | empty =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · rw [piAntidiag_empty_of_ne_zero hk.ne']
      obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
      simp [Function.iterate_succ_apply, iterate_map_zero]
  | cons i s hi ih =>
    rw [prod_cons, mul_comm, iterate_derivative_mul, piAntidiag_cons, sum_disjiUnion,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, mul_sum]
    refine sum_congr rfl fun p hp => ?_
    have hpk : p ≤ k := Nat.lt_succ_iff.mp (mem_range.mp hp)
    rw [ih, iterate_derivative_X_add_pow, sum_map]
    have key : ∀ x ∈ piAntidiag s (k - p),
        ∏ j ∈ cons i s hi,
            ((n j).choose ((addRightEmbedding fun t ↦ if t = i then p else 0) x j) : R[X]) *
              (X + C (a j)) ^ (n j - (addRightEmbedding fun t ↦ if t = i then p else 0) x j) =
          ((n i).choose p : R[X]) * (X + C (a i)) ^ (n i - p) *
            ∏ j ∈ s, ((n j).choose (x j) : R[X]) * (X + C (a j)) ^ (n j - x j) := by
      intro x hx
      have hxi : x i = 0 := by
        by_contra h
        exact hi ((mem_piAntidiag.mp hx).2 i h)
      rw [prod_cons]
      simp only [addRightEmbedding_apply, Pi.add_apply, hxi, zero_add]
      congr 1
      refine prod_congr rfl fun j hj => ?_
      have : j ≠ i := fun h => hi (h ▸ hj)
      simp [this]
    rw [sum_congr rfl key, ← mul_sum]
    have hfac : (k.choose p : R[X]) * ((k - p).factorial : R[X]) * (n i).descFactorial p =
        (k.factorial : R[X]) * (n i).choose p := by
      rw [Nat.descFactorial_eq_factorial_mul_choose, ← Nat.choose_mul_factorial_mul_factorial hpk]
      push_cast
      ring
    rw [nsmul_eq_mul, nsmul_eq_mul]
    linear_combination (∑ x ∈ piAntidiag s (k - p),
        ∏ j ∈ s, ((n j).choose (x j) : R[X]) * (X + C (a j)) ^ (n j - x j)) *
        (X + C (a i)) ^ (n i - p) * hfac

/-- The multinomial Leibniz rule with the common factor `∏ i, (X + C (a i)) ^ (n i - m)` pulled
out, for `k ≤ m ≤ n i`. -/
theorem iterate_derivative_prod_X_add_C_pow_of_le [Fintype ι] (a : ι → R) (n : ι → ℕ)
    {m k : ℕ} (hn : ∀ i, m ≤ n i) (hk : k ≤ m) :
    derivative^[k] (∏ i, (X + C (a i)) ^ n i) =
      (∏ i, (X + C (a i)) ^ (n i - m)) *
        ((k.factorial : R[X]) *
          ∑ α ∈ univ.piAntidiag k,
            ∏ i, ((n i).choose (α i) : R[X]) * (X + C (a i)) ^ (m - α i)) := by
  rw [iterate_derivative_prod_X_add_C_pow a n univ k, mul_left_comm]
  congr 1
  rw [mul_sum]
  refine sum_congr rfl fun α hα => ?_
  have hle : ∀ i, α i ≤ k := fun i => by
    rw [← (mem_piAntidiag.mp hα).1]
    exact single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ i)
  rw [← prod_mul_distrib]
  refine prod_congr rfl fun i _ => ?_
  rw [show n i - α i = (n i - m) + (m - α i) by have := hle i; have := hn i; lia, pow_add]
  ring

end Polynomial
