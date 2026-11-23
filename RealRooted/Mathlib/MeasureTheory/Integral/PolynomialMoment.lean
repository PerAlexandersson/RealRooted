/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import RealRooted.Mathlib.Algebra.Polynomial.Moment
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import TauCeti.MeasureTheory.Function.PolynomialMemLp

/-!
# Integration of polynomial moment functionals
-/

public section

open MeasureTheory Polynomial

namespace MeasureTheory

/-- All natural moments make every polynomial times a natural power integrable. -/
theorem integrable_pow_mul_polynomial_eval {mu : Measure ℝ}
    (hmom : ∀ k : ℕ, Integrable (fun x : ℝ => x ^ k) mu) (r : ℕ) (p : ℝ[X]) :
    Integrable (fun x : ℝ => x ^ r * p.eval x) mu := by
  apply (TauCeti.integrable_eval_of_forall_integrable_pow hmom (X ^ r * p)).congr
  filter_upwards [] with x
  simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]

end MeasureTheory

namespace Polynomial

/-- The functional of shifted integral moments integrates the polynomial against
the corresponding power weight. -/
theorem momentFunctional_integral_pow_add {mu : Measure ℝ}
    (hmom : ∀ k : ℕ, Integrable (fun x : ℝ => x ^ k) mu) (r : ℕ) (p : ℝ[X]) :
    momentFunctional (fun k => ∫ x : ℝ, x ^ (k + r) ∂mu) p =
      ∫ x : ℝ, x ^ r * p.eval x ∂mu := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [momentFunctional_add, hp, hq]
      simp only [Polynomial.eval_add, mul_add]
      rw [integral_add (integrable_pow_mul_polynomial_eval hmom r p)
        (integrable_pow_mul_polynomial_eval hmom r q)]
  | monomial n a =>
      rw [momentFunctional_monomial]
      simp only [Polynomial.eval_monomial]
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with x
      rw [pow_add]
      ring

end Polynomial
