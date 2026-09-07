/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import RealRooted.Jacobi.Orthogonality
public import RealRooted.Mathlib.Analysis.SpecialFunctions.Gamma.Beta

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Integral form of shifted Jacobi orthogonality

This file identifies the shifted Jacobi moment pairing with integration
against the classical beta weight on the unit interval.
-/

@[expose] public section

open Polynomial

noncomputable section

namespace RealRooted

/-- The classical shifted Jacobi weight on the unit interval. -/
def shiftedJacobiWeight (α β x : ℝ) : ℝ :=
  x ^ α * (1 - x) ^ β

/-- A polynomial multiplied by the shifted Jacobi weight. -/
def shiftedJacobiIntegrand (α β : ℝ) (p : ℝ[X]) (x : ℝ) : ℝ :=
  p.eval x * shiftedJacobiWeight α β x

/-- The shifted Jacobi weight is interval integrable in the classical
parameter range. -/
theorem intervalIntegrable_shiftedJacobiWeight
    {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) :
    IntervalIntegrable (shiftedJacobiWeight α β)
      MeasureTheory.volume 0 1 := by
  change IntervalIntegrable (fun x : ℝ => x ^ α * (1 - x) ^ β)
    MeasureTheory.volume 0 1
  exact intervalIntegral.intervalIntegrable_rpow_mul_one_sub_rpow hα hβ

/-- A polynomial times the shifted Jacobi weight is interval integrable. -/
theorem intervalIntegrable_shiftedJacobiIntegrand
    {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) (p : ℝ[X]) :
    IntervalIntegrable (shiftedJacobiIntegrand α β p)
      MeasureTheory.volume 0 1 := by
  have hweight := intervalIntegrable_shiftedJacobiWeight hα hβ
  change IntervalIntegrable
    (fun x : ℝ => p.eval x * shiftedJacobiWeight α β x)
    MeasureTheory.volume 0 1
  exact hweight.continuousOn_mul p.continuousOn

/-- Each shifted Jacobi moment is the corresponding beta integral. -/
theorem shiftedJacobiMoment_eq_integral
    {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) (k : ℕ) :
    shiftedJacobiMoment α β k =
      ∫ x : ℝ in 0..1, x ^ (α + k) * (1 - x) ^ β := by
  have hk : 0 ≤ (k : ℝ) := by positivity
  have hαk : -1 < α + (k : ℝ) := by linarith
  rw [intervalIntegral.integral_rpow_mul_one_sub_rpow_zero_one hαk hβ,
    shiftedJacobiMoment]
  ring_nf

/-- The shifted Jacobi moment functional is integration against the beta
weight on the unit interval. -/
theorem shiftedJacobiFunctional_eq_integral
    {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) (p : ℝ[X]) :
    shiftedJacobiFunctional α β p =
      ∫ x : ℝ in 0..1, shiftedJacobiIntegrand α β p x := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [shiftedJacobiFunctional_add, hp, hq]
      rw [← intervalIntegral.integral_add
        (intervalIntegrable_shiftedJacobiIntegrand hα hβ p)
        (intervalIntegrable_shiftedJacobiIntegrand hα hβ q)]
      apply intervalIntegral.integral_congr
      intro x hx
      simp only [shiftedJacobiIntegrand, eval_add]
      ring
  | monomial n c =>
      rw [shiftedJacobiFunctional_monomial,
        shiftedJacobiMoment_eq_integral hα hβ n,
        ← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr_uIoo
      intro x hx
      have hxpos : 0 < x := by simpa using hx.1
      simp only [shiftedJacobiIntegrand, shiftedJacobiWeight, eval_monomial]
      rw [Real.rpow_add hxpos, Real.rpow_natCast]
      ring

/-- The shifted Jacobi moment pairing is the classical beta-weighted
integral. -/
theorem shiftedJacobiInner_eq_integral
    {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) (p q : ℝ[X]) :
    shiftedJacobiInner α β p q =
      ∫ x : ℝ in 0..1,
        p.eval x * q.eval x * shiftedJacobiWeight α β x := by
  change shiftedJacobiFunctional α β (p * q) = _
  rw [shiftedJacobiFunctional_eq_integral hα hβ]
  apply intervalIntegral.integral_congr
  intro x hx
  simp [shiftedJacobiIntegrand]

/-- A shifted Jacobi polynomial is beta-weight orthogonal to every polynomial
of strictly smaller degree. -/
theorem shiftedJacobi_integral_orthogonal
    {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) {n : ℕ}
    (q : ℝ[X]) (hq : q.natDegree < n) :
    (∫ x : ℝ in 0..1,
      (shiftedJacobi n α β).eval x * q.eval x *
        shiftedJacobiWeight α β x) = 0 := by
  rw [← shiftedJacobiInner_eq_integral hα hβ]
  exact shiftedJacobiInner_eq_zero hα hβ q hq

/-- Distinct shifted Jacobi polynomials satisfy the classical beta-weighted
integral orthogonality relation. -/
theorem shiftedJacobi_pairwise_integral_orthogonal
    {α β : ℝ} (hα : -1 < α) (hβ : -1 < β)
    {m n : ℕ} (hmn : m ≠ n) :
    (∫ x : ℝ in 0..1,
      (shiftedJacobi m α β).eval x * (shiftedJacobi n α β).eval x *
        shiftedJacobiWeight α β x) = 0 := by
  rw [← shiftedJacobiInner_eq_integral hα hβ]
  exact shiftedJacobi_pairwise_orthogonal hα hβ hmn

end RealRooted
