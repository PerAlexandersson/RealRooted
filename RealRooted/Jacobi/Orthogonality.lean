/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import RealRooted.Mathlib.RingTheory.Polynomial.Jacobi
public import RealRooted.Mathlib.RingTheory.Polynomial.Jacobi.Moment

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Finite orthogonality for shifted Jacobi polynomials

The beta moments in this file represent integration against
`x ^ α * (1 - x) ^ β` on the unit interval.  The finite orthogonality proof is
kept separate from the analytic identification with that integral.
-/

@[expose] public section

open Polynomial

noncomputable section

namespace RealRooted

/-- The `k`th moment of the shifted Jacobi beta weight. -/
def shiftedJacobiMoment (α β : ℝ) (k : ℕ) : ℝ :=
  Real.Gamma (α + k + 1) * Real.Gamma (β + 1) /
    Real.Gamma (α + β + k + 2)

/-- The shifted Jacobi moment functional on real polynomials. -/
def shiftedJacobiFunctional (α β : ℝ) (p : ℝ[X]) : ℝ :=
  Polynomial.momentFunctional (shiftedJacobiMoment α β) p

/-- The symmetric shifted Jacobi moment pairing.

This is an unbundled bilinear pairing, not an `InnerProduct` instance. -/
def shiftedJacobiInner (α β : ℝ) (p q : ℝ[X]) : ℝ :=
  Polynomial.momentPairing (shiftedJacobiMoment α β) p q

@[simp] theorem shiftedJacobiFunctional_zero (α β : ℝ) :
    shiftedJacobiFunctional α β 0 = 0 := by
  simp [shiftedJacobiFunctional]

@[simp] theorem shiftedJacobiFunctional_add (α β : ℝ) (p q : ℝ[X]) :
    shiftedJacobiFunctional α β (p + q) =
      shiftedJacobiFunctional α β p + shiftedJacobiFunctional α β q := by
  simp [shiftedJacobiFunctional]

@[simp] theorem shiftedJacobiFunctional_sum {ι : Type*} (α β : ℝ)
    (s : Finset ι) (p : ι → ℝ[X]) :
    shiftedJacobiFunctional α β (∑ i ∈ s, p i) =
      ∑ i ∈ s, shiftedJacobiFunctional α β (p i) := by
  simp [shiftedJacobiFunctional]

@[simp] theorem shiftedJacobiFunctional_C_mul
    (α β c : ℝ) (p : ℝ[X]) :
    shiftedJacobiFunctional α β (C c * p) =
      c * shiftedJacobiFunctional α β p := by
  simp [shiftedJacobiFunctional]

@[simp] theorem shiftedJacobiFunctional_monomial
    (α β c : ℝ) (k : ℕ) :
    shiftedJacobiFunctional α β (monomial k c) =
      c * shiftedJacobiMoment α β k := by
  simp [shiftedJacobiFunctional]

@[simp] theorem shiftedJacobiFunctional_X_pow (α β : ℝ) (k : ℕ) :
    shiftedJacobiFunctional α β (X ^ k) = shiftedJacobiMoment α β k := by
  simp [shiftedJacobiFunctional]

theorem shiftedJacobiInner_comm (α β : ℝ) (p q : ℝ[X]) :
    shiftedJacobiInner α β p q = shiftedJacobiInner α β q p := by
  exact Polynomial.momentPairing_comm _ _ _

@[simp] theorem shiftedJacobiInner_zero_left (α β : ℝ) (p : ℝ[X]) :
    shiftedJacobiInner α β 0 p = 0 := by
  simp [shiftedJacobiInner]

@[simp] theorem shiftedJacobiInner_zero_right (α β : ℝ) (p : ℝ[X]) :
    shiftedJacobiInner α β p 0 = 0 := by
  simp [shiftedJacobiInner]

@[simp] theorem shiftedJacobiInner_add_left
    (α β : ℝ) (p q s : ℝ[X]) :
    shiftedJacobiInner α β (p + q) s =
      shiftedJacobiInner α β p s + shiftedJacobiInner α β q s := by
  simp [shiftedJacobiInner]

@[simp] theorem shiftedJacobiInner_add_right
    (α β : ℝ) (p q s : ℝ[X]) :
    shiftedJacobiInner α β p (q + s) =
      shiftedJacobiInner α β p q + shiftedJacobiInner α β p s := by
  simp [shiftedJacobiInner]

@[simp] theorem shiftedJacobiInner_neg_right
    (α β : ℝ) (p q : ℝ[X]) :
    shiftedJacobiInner α β p (-q) = -shiftedJacobiInner α β p q := by
  simp [shiftedJacobiInner]

@[simp] theorem shiftedJacobiInner_sub_right
    (α β : ℝ) (p q s : ℝ[X]) :
    shiftedJacobiInner α β p (q - s) =
      shiftedJacobiInner α β p q - shiftedJacobiInner α β p s := by
  simp [shiftedJacobiInner]

@[simp] theorem shiftedJacobiInner_sum_right {ι : Type*}
    (α β : ℝ) (p : ℝ[X]) (s : Finset ι) (q : ι → ℝ[X]) :
    shiftedJacobiInner α β p (∑ i ∈ s, q i) =
      ∑ i ∈ s, shiftedJacobiInner α β p (q i) := by
  simp [shiftedJacobiInner]

@[simp] theorem shiftedJacobiInner_C_mul_left
    (α β c : ℝ) (p q : ℝ[X]) :
    shiftedJacobiInner α β (C c * p) q =
      c * shiftedJacobiInner α β p q := by
  simp [shiftedJacobiInner]

@[simp] theorem shiftedJacobiInner_C_mul_right
    (α β c : ℝ) (p q : ℝ[X]) :
    shiftedJacobiInner α β p (C c * q) =
      c * shiftedJacobiInner α β p q := by
  simp [shiftedJacobiInner]

@[simp] theorem shiftedJacobiInner_monomial
    (α β a d : ℝ) (i j : ℕ) :
    shiftedJacobiInner α β (monomial i a) (monomial j d) =
      a * d * shiftedJacobiMoment α β (i + j) := by
  simp [shiftedJacobiInner]

/-- Consecutive shifted Jacobi moments satisfy the beta recurrence. -/
theorem shiftedJacobiMoment_succ
    {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) (k : ℕ) :
    (α + k + 1) * shiftedJacobiMoment α β k =
      (α + β + k + 2) * shiftedJacobiMoment α β (k + 1) := by
  have hk : 0 ≤ (k : ℝ) := by positivity
  have hnum : 0 < α + (k : ℝ) + 1 := by linarith
  have hden : 0 < α + β + (k : ℝ) + 2 := by linarith
  have hnum' : α + ((k + 1 : ℕ) : ℝ) + 1 =
      (α + (k : ℝ) + 1) + 1 := by push_cast; ring
  have hden' : α + β + ((k + 1 : ℕ) : ℝ) + 2 =
      (α + β + (k : ℝ) + 2) + 1 := by push_cast; ring
  rw [shiftedJacobiMoment, shiftedJacobiMoment, hnum', hden',
    Real.Gamma_add_one hnum.ne', Real.Gamma_add_one hden.ne']
  field_simp [(Real.Gamma_pos_of_pos hden).ne', hden.ne']

/-- At beta parameter zero, the Gamma moments reduce to reciprocal linear
moments. -/
theorem shiftedJacobiMoment_beta_zero
    {α : ℝ} (hα : -1 < α) (k : ℕ) :
    shiftedJacobiMoment α 0 k = (α + k + 1)⁻¹ := by
  have hk : 0 ≤ (k : ℝ) := by positivity
  have harg : 0 < α + (k : ℝ) + 1 := by linarith
  rw [shiftedJacobiMoment,
    show α + 0 + (k : ℝ) + 2 = (α + (k : ℝ) + 1) + 1 by ring,
    Real.Gamma_add_one harg.ne']
  norm_num
  field_simp [(Real.Gamma_pos_of_pos harg).ne', harg.ne']

/-- At beta parameter one, the Gamma moments reduce to reciprocal quadratic
moments. -/
theorem shiftedJacobiMoment_beta_one
    {α : ℝ} (hα : -1 < α) (k : ℕ) :
    shiftedJacobiMoment α 1 k =
      (((α + k + 1) * (α + k + 2))⁻¹ : ℝ) := by
  have hk : 0 ≤ (k : ℝ) := by positivity
  have harg : 0 < α + (k : ℝ) + 1 := by linarith
  have harg' : 0 < α + (k : ℝ) + 2 := by linarith
  rw [shiftedJacobiMoment,
    show α + 1 + (k : ℝ) + 2 = (α + (k : ℝ) + 2) + 1 by ring,
    Real.Gamma_add_one harg'.ne',
    show α + (k : ℝ) + 2 = (α + (k : ℝ) + 1) + 1 by ring,
    Real.Gamma_add_one harg.ne']
  norm_num
  field_simp [(Real.Gamma_pos_of_pos harg).ne', harg.ne', harg'.ne']

/-- The shifted Jacobi differential operator is self-adjoint for the beta
moment pairing. -/
theorem shiftedJacobiInner_operator_symm
    {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) (p q : ℝ[X]) :
    shiftedJacobiInner α β
        (jacobiDifferentialOperator (α + 1) (α + β + 2) p) q =
      shiftedJacobiInner α β p
        (jacobiDifferentialOperator (α + 1) (α + β + 2) q) := by
  apply Polynomial.jacobiDifferentialOperator_momentPairing_symm
  intro k
  convert shiftedJacobiMoment_succ hα hβ k using 1 <;> ring

/-- A shifted Jacobi polynomial is orthogonal to every lower monomial. -/
theorem shiftedJacobiInner_X_pow_eq_zero
    {α β : ℝ} (hα : -1 < α) (hβ : -1 < β)
    {n j : ℕ} (hj : j < n) :
    shiftedJacobiInner α β (shiftedJacobi n α β) (X ^ j) = 0 := by
  induction j with
  | zero =>
      have hs := shiftedJacobiInner_operator_symm hα hβ
        (shiftedJacobi n α β) (X ^ 0)
      rw [jacobiDifferentialOperator_shiftedJacobi,
        jacobiDifferentialOperator_X_pow] at hs
      simp only [shiftedJacobiInner_C_mul_left, Nat.cast_zero, zero_mul,
        zero_add, sub_self, map_zero, shiftedJacobiInner_zero_right,
        pow_zero] at hs
      have hn : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by lia)
      have hn1 : 1 ≤ (n : ℝ) := by
        exact_mod_cast (show 1 ≤ n by lia)
      have hfactor : 0 < (n : ℝ) + α + β + 1 := by linarith
      exact (mul_eq_zero.mp hs).resolve_left
        (neg_ne_zero.mpr (mul_ne_zero hn.ne' hfactor.ne'))
  | succ j ih =>
      have hih := ih (by lia : j < n)
      have hs := shiftedJacobiInner_operator_symm hα hβ
        (shiftedJacobi n α β) (X ^ (j + 1))
      rw [jacobiDifferentialOperator_shiftedJacobi,
        jacobiDifferentialOperator_X_pow] at hs
      simp only [shiftedJacobiInner_C_mul_left,
        shiftedJacobiInner_sub_right,
        shiftedJacobiInner_C_mul_right, Nat.succ_sub_one] at hs
      rw [hih, mul_zero, zero_sub] at hs
      have hjn : (j + 1 : ℝ) < n := by exact_mod_cast hj
      have hsum : 0 < (n : ℝ) + (j + 1 : ℝ) + α + β + 1 := by
        have hj0 : 0 ≤ (j + 1 : ℝ) := by positivity
        linarith
      have hdiff : 0 < (n : ℝ) * (n + α + β + 1) -
          (j + 1 : ℝ) * (j + 1 + α + β + 1) := by
        nlinarith [mul_pos (sub_pos.mpr hjn) hsum]
      have hproduct : ((j + 1 : ℝ) * (j + 1 + α + β + 1) -
          (n : ℝ) * (n + α + β + 1)) *
          shiftedJacobiInner α β
            (shiftedJacobi n α β) (X ^ (j + 1)) = 0 := by
        push_cast at hs ⊢
        linear_combination hs
      exact (mul_eq_zero.mp hproduct).resolve_left (by linarith)

/-- A shifted Jacobi polynomial is orthogonal to every polynomial of strictly
smaller degree. -/
theorem shiftedJacobiInner_eq_zero
    {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) {n : ℕ}
    (q : ℝ[X]) (hq : q.natDegree < n) :
    shiftedJacobiInner α β (shiftedJacobi n α β) q = 0 := by
  classical
  rw [q.as_sum_range_C_mul_X_pow' hq, shiftedJacobiInner_sum_right]
  apply Finset.sum_eq_zero
  intro i hi
  rw [shiftedJacobiInner_C_mul_right,
    shiftedJacobiInner_X_pow_eq_zero hα hβ (Finset.mem_range.mp hi),
    mul_zero]

/-- Distinct shifted Jacobi polynomials are pairwise orthogonal. -/
theorem shiftedJacobi_pairwise_orthogonal
    {α β : ℝ} (hα : -1 < α) (hβ : -1 < β)
    {m n : ℕ} (hmn : m ≠ n) :
    shiftedJacobiInner α β
      (shiftedJacobi m α β) (shiftedJacobi n α β) = 0 := by
  rcases lt_or_gt_of_ne hmn with hmn | hnm
  · rw [shiftedJacobiInner_comm]
    apply shiftedJacobiInner_eq_zero hα hβ
    rw [natDegree_shiftedJacobi m hα hβ]
    exact hmn
  · apply shiftedJacobiInner_eq_zero hα hβ
    rw [natDegree_shiftedJacobi n hα hβ]
    exact hnm

end RealRooted
