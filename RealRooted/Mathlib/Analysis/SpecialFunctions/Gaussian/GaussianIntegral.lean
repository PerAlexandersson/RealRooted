/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Algebra.Polynomial.Inductions

import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# Polynomial factors in Gaussian integrals

This file adds a reusable integrability lemma for a polynomial times a
decaying Gaussian.
-/

@[expose] public section

open MeasureTheory

noncomputable section

namespace Polynomial

/-- A real polynomial times `exp (-b x²)` is integrable when `b` is
positive. -/
theorem integrable_eval_mul_exp_neg_mul_sq (p : ℝ[X]) {b : ℝ} (hb : 0 < b) :
    Integrable (fun x : ℝ => p.eval x * Real.exp (-b * x ^ 2)) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      have hfun :
          (fun x : ℝ => (p + q).eval x * Real.exp (-b * x ^ 2)) =
            (fun x : ℝ => p.eval x * Real.exp (-b * x ^ 2)) +
              fun x : ℝ => q.eval x * Real.exp (-b * x ^ 2) := by
        funext x
        simp only [Pi.add_apply, eval_add, add_mul]
      rw [hfun]
      exact hp.add hq
  | monomial n a =>
      have hn : (0 : ℝ) ≤ n := by positivity
      have h := integrable_rpow_mul_exp_neg_mul_sq
        hb (s := (n : ℝ)) (by linarith)
      simpa only [eval_monomial, Real.rpow_natCast, mul_assoc,
        mul_comm, mul_left_comm] using h.const_mul a

end Polynomial
