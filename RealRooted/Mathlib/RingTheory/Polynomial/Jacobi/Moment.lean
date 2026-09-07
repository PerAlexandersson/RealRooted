/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import RealRooted.Mathlib.Algebra.Polynomial.Moment
public import RealRooted.Mathlib.RingTheory.Polynomial.Jacobi.DifferentialOperator

import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Moment pairings for the shifted Jacobi operator

This file isolates the algebra behind formal self-adjointness of the shifted
Jacobi differential operator.  It applies over any commutative ring and to any
moment sequence satisfying the corresponding first-order recurrence.
-/

@[expose] public section

noncomputable section

namespace Polynomial

variable {R : Type*} [CommRing R]

private theorem jacobiDifferentialOperator_momentPairing_monomial_symm
    {b c : R} {μ : ℕ → R}
    (hμ : ∀ k : ℕ, ((k : R) + b) * μ k = ((k : R) + c) * μ (k + 1))
    (a d : R) (i j : ℕ) :
    momentPairing μ (jacobiDifferentialOperator b c (monomial i a))
        (monomial j d) =
      momentPairing μ (monomial i a)
        (jacobiDifferentialOperator b c (monomial j d)) := by
  rw [jacobiDifferentialOperator_monomial,
    jacobiDifferentialOperator_monomial]
  cases i with
  | zero =>
      cases j with
      | zero => simp
      | succ j =>
          simp only [momentPairing_sub_right,
            momentPairing_monomial, Nat.zero_sub, Nat.cast_zero,
            Nat.succ_sub_one, zero_mul, mul_zero, zero_add, sub_self,
            momentPairing_zero_left]
          have hrec := hμ j
          push_cast at hrec ⊢
          linear_combination -a * d * ((j : R) + 1) * hrec
  | succ i =>
      cases j with
      | zero =>
          simp only [momentPairing_sub_left,
            momentPairing_monomial, Nat.zero_sub, Nat.cast_zero,
            Nat.succ_sub_one, zero_mul, mul_zero, zero_add, add_zero,
            sub_self, momentPairing_zero_right]
          have hrec := hμ i
          push_cast at hrec ⊢
          linear_combination a * d * ((i : R) + 1) * hrec
      | succ j =>
          simp only [momentPairing_sub_left, momentPairing_sub_right,
            momentPairing_monomial, Nat.succ_sub_one, Nat.add_comm,
            Nat.add_left_comm]
          have hrec := hμ (i + j + 1)
          simp only [Nat.cast_add, Nat.cast_one] at hrec
          push_cast at hrec ⊢
          linear_combination a * d * ((i : R) - (j : R)) * hrec

/-- A Jacobi-type moment recurrence makes the shifted Jacobi differential
operator self-adjoint for the induced moment pairing. -/
theorem jacobiDifferentialOperator_momentPairing_symm
    {b c : R} {μ : ℕ → R}
    (hμ : ∀ k : ℕ, ((k : R) + b) * μ k = ((k : R) + c) * μ (k + 1))
    (p q : R[X]) :
    momentPairing μ (jacobiDifferentialOperator b c p) q =
      momentPairing μ p (jacobiDifferentialOperator b c q) := by
  induction p using Polynomial.induction_on' with
  | add p s hp hs => simp [hp, hs]
  | monomial i a =>
      induction q using Polynomial.induction_on' with
      | add q s hq hs => simp [hq, hs]
      | monomial j d =>
          exact jacobiDifferentialOperator_momentPairing_monomial_symm
            hμ a d i j

end Polynomial
