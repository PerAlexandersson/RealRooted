/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import RealRooted.Mathlib.Algebra.Polynomial.TaylorEvaluation
public import Mathlib.Algebra.Polynomial.HasseDeriv
import Mathlib.Tactic.TypeStar

/-!
# Expectations of polynomial translations
-/

public section

open Polynomial

namespace MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω] {mu : Measure Ω} {Y : Ω → ℝ}

/-- Integrable natural powers suffice for every translated polynomial test. -/
theorem integrable_polynomial_eval_add
    (hmom : ∀ k : ℕ, Integrable (fun w => Y w ^ k) mu)
    (p : ℝ[X]) (x : ℝ) : Integrable (fun w => p.eval (x + Y w)) mu := by
  simp_rw [p.eval_add_eq_sum_hasseDeriv]
  exact integrable_finsetSum _ (fun k _ => (hmom k).const_mul _)

/-- Averaging polynomial translations is the finite Hasse differential operator
whose coefficients are the actual power moments of the translation variable. -/
theorem integral_polynomial_eval_add_eq_sum_hasseDeriv
    (hmom : ∀ k : ℕ, Integrable (fun w => Y w ^ k) mu)
    (p : ℝ[X]) (x : ℝ) :
    (∫ w, p.eval (x + Y w) ∂mu) = ∑ k ∈ Finset.range (p.natDegree + 1),
      (hasseDeriv k p).eval x * ∫ w, Y w ^ k ∂mu := by
  simp_rw [p.eval_add_eq_sum_hasseDeriv]
  rw [integral_finsetSum _ (fun k _ => (hmom k).const_mul _)]
  simp only [integral_const_mul]

/-- The same expectation in ordinary iterated derivatives. -/
theorem integral_polynomial_eval_add_eq_sum_derivative
    (hmom : ∀ k : ℕ, Integrable (fun w => Y w ^ k) mu)
    (p : ℝ[X]) (x : ℝ) :
    (∫ w, p.eval (x + Y w) ∂mu) = ∑ k ∈ Finset.range (p.natDegree + 1),
      (∫ w, Y w ^ k ∂mu) / k.factorial * (derivative^[k] p).eval x := by
  rw [integral_polynomial_eval_add_eq_sum_hasseDeriv hmom]
  apply Finset.sum_congr rfl
  intro k _
  rw [eval_hasseDeriv_eq_div_factorial]
  ring

end MeasureTheory
