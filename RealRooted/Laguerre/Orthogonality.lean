/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import RealRooted.Mathlib.RingTheory.Polynomial.Laguerre.Differential

import Mathlib.Tactic.Algebra.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity

/-!
# Algebraic orthogonality for generalized Laguerre polynomials

The signed Gamma moments in this file represent integration of `p(-x)`
against `x ^ α * exp (-x)` on the positive half-line.  This sign convention
matches the sign-reversed normalization whose roots are nonpositive.
-/

@[expose] public section

open Polynomial

noncomputable section

namespace RealRooted

/-- The signed Gamma moment associated with the sign-reversed Laguerre
normalization. -/
def generalizedLaguerreMoment (α : ℝ) (k : ℕ) : ℝ :=
  (-1 : ℝ) ^ k * Real.Gamma (α + k + 1)

/-- The generalized Laguerre moment functional on real polynomials. -/
def generalizedLaguerreFunctional (α : ℝ) (p : ℝ[X]) : ℝ :=
  p.sum fun k c => c * generalizedLaguerreMoment α k

/-- The symmetric generalized Laguerre moment pairing.

This is an unbundled bilinear pairing, not an `InnerProduct` instance. -/
def generalizedLaguerreInner (α : ℝ) (p q : ℝ[X]) : ℝ :=
  generalizedLaguerreFunctional α (p * q)

@[simp] theorem generalizedLaguerreFunctional_zero (α : ℝ) :
    generalizedLaguerreFunctional α 0 = 0 := by
  simp [generalizedLaguerreFunctional]

@[simp] theorem generalizedLaguerreFunctional_add (α : ℝ) (p q : ℝ[X]) :
    generalizedLaguerreFunctional α (p + q) =
      generalizedLaguerreFunctional α p + generalizedLaguerreFunctional α q := by
  simp only [generalizedLaguerreFunctional]
  apply Polynomial.sum_add_index <;> simp [add_mul]

@[simp] theorem generalizedLaguerreFunctional_sum {ι : Type*} (α : ℝ)
    (s : Finset ι) (p : ι → ℝ[X]) :
    generalizedLaguerreFunctional α (∑ i ∈ s, p i) =
      ∑ i ∈ s, generalizedLaguerreFunctional α (p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi hs => simp [hi, hs]

@[simp] theorem generalizedLaguerreFunctional_C_mul (α c : ℝ) (p : ℝ[X]) :
    generalizedLaguerreFunctional α (C c * p) =
      c * generalizedLaguerreFunctional α p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [mul_add, hp, hq, mul_add]
  | monomial n a =>
      simp [generalizedLaguerreFunctional, C_mul_monomial, mul_assoc]

@[simp] theorem generalizedLaguerreFunctional_monomial (α c : ℝ) (k : ℕ) :
    generalizedLaguerreFunctional α (monomial k c) =
      c * generalizedLaguerreMoment α k := by
  simp [generalizedLaguerreFunctional]

@[simp] theorem generalizedLaguerreFunctional_X_pow (α : ℝ) (k : ℕ) :
    generalizedLaguerreFunctional α (X ^ k) =
      generalizedLaguerreMoment α k := by
  rw [X_pow_eq_monomial, generalizedLaguerreFunctional_monomial]
  simp

theorem generalizedLaguerreInner_comm (α : ℝ) (p q : ℝ[X]) :
    generalizedLaguerreInner α p q = generalizedLaguerreInner α q p := by
  simp [generalizedLaguerreInner, mul_comm]

@[simp] theorem generalizedLaguerreInner_zero_left (α : ℝ) (p : ℝ[X]) :
    generalizedLaguerreInner α 0 p = 0 := by
  simp [generalizedLaguerreInner]

@[simp] theorem generalizedLaguerreInner_zero_right (α : ℝ) (p : ℝ[X]) :
    generalizedLaguerreInner α p 0 = 0 := by
  simp [generalizedLaguerreInner]

@[simp] theorem generalizedLaguerreInner_add_left
    (α : ℝ) (p q s : ℝ[X]) :
    generalizedLaguerreInner α (p + q) s =
      generalizedLaguerreInner α p s + generalizedLaguerreInner α q s := by
  simp [generalizedLaguerreInner, add_mul]

@[simp] theorem generalizedLaguerreInner_add_right
    (α : ℝ) (p q s : ℝ[X]) :
    generalizedLaguerreInner α p (q + s) =
      generalizedLaguerreInner α p q + generalizedLaguerreInner α p s := by
  rw [generalizedLaguerreInner_comm]
  simp only [generalizedLaguerreInner_add_left]
  rw [generalizedLaguerreInner_comm α q p,
    generalizedLaguerreInner_comm α s p]

@[simp] theorem generalizedLaguerreInner_sum_right {ι : Type*}
    (α : ℝ) (p : ℝ[X]) (s : Finset ι) (q : ι → ℝ[X]) :
    generalizedLaguerreInner α p (∑ i ∈ s, q i) =
      ∑ i ∈ s, generalizedLaguerreInner α p (q i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi hs => simp [hi, hs]

@[simp] theorem generalizedLaguerreInner_C_mul_left
    (α c : ℝ) (p q : ℝ[X]) :
    generalizedLaguerreInner α (C c * p) q =
      c * generalizedLaguerreInner α p q := by
  simp [generalizedLaguerreInner, mul_assoc]

@[simp] theorem generalizedLaguerreInner_C_mul_right
    (α c : ℝ) (p q : ℝ[X]) :
    generalizedLaguerreInner α p (C c * q) =
      c * generalizedLaguerreInner α p q := by
  rw [generalizedLaguerreInner_comm]
  simp only [generalizedLaguerreInner_C_mul_left]
  rw [generalizedLaguerreInner_comm]

@[simp] theorem generalizedLaguerreInner_monomial
    (α a b : ℝ) (i j : ℕ) :
    generalizedLaguerreInner α (monomial i a) (monomial j b) =
      a * b * generalizedLaguerreMoment α (i + j) := by
  simp [generalizedLaguerreInner, monomial_mul_monomial, mul_assoc]

/-- Consecutive signed Gamma moments satisfy the integration-by-parts
recurrence. -/
theorem generalizedLaguerreMoment_succ {α : ℝ} (hα : -1 < α) (k : ℕ) :
    generalizedLaguerreMoment α (k + 1) =
      -(α + k + 1) * generalizedLaguerreMoment α k := by
  have hk : 0 ≤ (k : ℝ) := by positivity
  have hpos : 0 < α + (k : ℝ) + 1 := by linarith
  have harg : α + ((k + 1 : ℕ) : ℝ) + 1 =
      (α + (k : ℝ) + 1) + 1 := by push_cast; ring
  rw [generalizedLaguerreMoment, generalizedLaguerreMoment, pow_succ,
    harg, Real.Gamma_add_one hpos.ne']
  ring

private theorem generalizedLaguerreOperator_inner_monomial_symm
    {α : ℝ} (hα : -1 < α) (a b : ℝ) (i j : ℕ) :
    generalizedLaguerreInner α
        (laguerreDifferentialOperator α (monomial i a)) (monomial j b) =
      generalizedLaguerreInner α (monomial i a)
        (laguerreDifferentialOperator α (monomial j b)) := by
  rw [laguerreDifferentialOperator_monomial,
    laguerreDifferentialOperator_monomial]
  cases i with
  | zero =>
      cases j with
      | zero => simp
      | succ j =>
          simp only [generalizedLaguerreInner_add_left,
            generalizedLaguerreInner_add_right,
            generalizedLaguerreInner_monomial, Nat.zero_sub,
            Nat.cast_zero, Nat.succ_sub_one, zero_add]
          have hrec := generalizedLaguerreMoment_succ hα j
          push_cast at hrec ⊢
          linear_combination -a * b * ((j : ℝ) + 1) * hrec
  | succ i =>
      cases j with
      | zero =>
          simp only [generalizedLaguerreInner_add_left,
            generalizedLaguerreInner_add_right,
            generalizedLaguerreInner_monomial, Nat.zero_sub,
            Nat.cast_zero, Nat.succ_sub_one, zero_add, add_zero]
          have hrec := generalizedLaguerreMoment_succ hα i
          push_cast at hrec ⊢
          linear_combination a * b * ((i : ℝ) + 1) * hrec
      | succ j =>
          simp only [generalizedLaguerreInner_add_left,
            generalizedLaguerreInner_add_right,
            generalizedLaguerreInner_monomial, Nat.succ_sub_one,
            Nat.cast_add, Nat.cast_one, Nat.add_comm, Nat.add_left_comm]
          have hrec := generalizedLaguerreMoment_succ hα (i + j + 1)
          simp only [Nat.cast_add, Nat.cast_one] at hrec
          push_cast at hrec ⊢
          linear_combination a * b * ((i : ℝ) - (j : ℝ)) * hrec

/-- The generalized Laguerre differential operator is self-adjoint for its
signed Gamma moment pairing. -/
theorem generalizedLaguerreOperator_inner_symm
    {α : ℝ} (hα : -1 < α) (p q : ℝ[X]) :
    generalizedLaguerreInner α (laguerreDifferentialOperator α p) q =
      generalizedLaguerreInner α p (laguerreDifferentialOperator α q) := by
  induction p using Polynomial.induction_on' with
  | add p s hp hs => simp [hp, hs, laguerreDifferentialOperator_add]
  | monomial i a =>
      induction q using Polynomial.induction_on' with
      | add q s hq hs => simp [hq, hs, laguerreDifferentialOperator_add]
      | monomial j b =>
          exact generalizedLaguerreOperator_inner_monomial_symm
            hα a b i j

/-- A generalized Laguerre polynomial is orthogonal to every lower
monomial. -/
theorem generalizedLaguerreInner_X_pow_eq_zero
    {α : ℝ} (hα : -1 < α) {n j : ℕ} (hj : j < n) :
    generalizedLaguerreInner α (generalizedLaguerre n α) (X ^ j) = 0 := by
  induction j with
  | zero =>
      have hs := generalizedLaguerreOperator_inner_symm hα
        (generalizedLaguerre n α) (X ^ 0)
      rw [generalizedLaguerre_ode,
        laguerreDifferentialOperator_X_pow] at hs
      simp only [generalizedLaguerreInner_C_mul_left, Nat.cast_zero,
        zero_mul, map_zero, generalizedLaguerreInner_zero_right,
        add_zero, pow_zero] at hs
      exact (mul_eq_zero.mp hs).resolve_left (by exact_mod_cast (show n ≠ 0 by lia))
  | succ j ih =>
      have hih := ih (by lia : j < n)
      have hs := generalizedLaguerreOperator_inner_symm hα
        (generalizedLaguerre n α) (X ^ (j + 1))
      rw [generalizedLaguerre_ode,
        laguerreDifferentialOperator_X_pow] at hs
      simp only [generalizedLaguerreInner_C_mul_left,
        generalizedLaguerreInner_add_right,
        generalizedLaguerreInner_C_mul_right, Nat.succ_sub_one] at hs
      rw [hih, mul_zero, zero_add] at hs
      have hproduct :
          ((n : ℝ) - (j + 1 : ℝ)) *
            generalizedLaguerreInner α
              (generalizedLaguerre n α) (X ^ (j + 1)) = 0 := by
        push_cast at hs ⊢
        linear_combination hs
      exact (mul_eq_zero.mp hproduct).resolve_left (by
        have hj_real : (j + 1 : ℝ) < n := by exact_mod_cast hj
        exact sub_ne_zero.mpr (ne_of_gt hj_real))

/-- A generalized Laguerre polynomial is orthogonal to every polynomial of
strictly smaller degree. -/
theorem generalizedLaguerreInner_eq_zero
    {α : ℝ} (hα : -1 < α) {n : ℕ} (q : ℝ[X])
    (hq : q.natDegree < n) :
    generalizedLaguerreInner α (generalizedLaguerre n α) q = 0 := by
  classical
  rw [q.as_sum_range_C_mul_X_pow' hq,
    generalizedLaguerreInner_sum_right]
  apply Finset.sum_eq_zero
  intro i hi
  rw [generalizedLaguerreInner_C_mul_right,
    generalizedLaguerreInner_X_pow_eq_zero hα
      (Finset.mem_range.mp hi), mul_zero]

/-- Distinct generalized Laguerre polynomials are pairwise orthogonal. -/
theorem generalizedLaguerre_pairwise_orthogonal
    {α : ℝ} (hα : -1 < α) {m n : ℕ} (hmn : m ≠ n) :
    generalizedLaguerreInner α
      (generalizedLaguerre m α) (generalizedLaguerre n α) = 0 := by
  rcases lt_or_gt_of_ne hmn with hmn | hnm
  · rw [generalizedLaguerreInner_comm]
    exact generalizedLaguerreInner_eq_zero hα _ (by simpa using hmn)
  · exact generalizedLaguerreInner_eq_zero hα _ (by simpa using hnm)

end RealRooted
