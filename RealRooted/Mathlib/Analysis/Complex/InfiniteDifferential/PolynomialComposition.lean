/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import RealRooted.Mathlib.Analysis.Complex.InfiniteDifferential.Basic
public import RealRooted.Mathlib.Analysis.Calculus.IteratedDeriv.Polynomial
import RealRooted.Mathlib.Analysis.Complex.InfiniteDifferential.SymbolAlgebra
import RealRooted.Mathlib.Analysis.Calculus.IteratedDeriv.PolynomialAlgebra
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-!
# Polynomial factors of infinite differential symbols

A finite polynomial factor composes with a convergent infinite differential
operator. Polynomial multiplication does not change the reciprocal-order
condition, even when the original symbol has a negative order bound.
-/

public section

open Polynomial

namespace Complex

/-- Multiplying a symbol by a fixed polynomial retains the same nonnegative
upper growth bound. -/
private theorem orderLE_polynomial_mul {φ : ℂ → ℂ} {ρ : ℝ}
    (hφ : TauCeti.OrderLE φ ρ) (P : ℂ[X]) :
    TauCeti.OrderLE (fun z => P.eval z * φ z) (max ρ 0) :=
  (P.orderLE_eval.mono (le_max_right _ _)).mul (hφ.mono (le_max_left _ _))

/-- A monomial factor applies the corresponding iterated derivative to the output. -/
theorem infiniteDifferentialApply_pow_mul {φ f : ℂ → ℂ} {ρ σ p q : ℝ}
    (hφ : Differentiable ℂ φ) (hoφ : TauCeti.OrderLE φ ρ) (hp : 0 < p) (hρ : ρ < p)
    (hf : Differentiable ℂ f) (hof : TauCeti.OrderLE f σ) (hq : 0 < q) (hσ : σ < q)
    (hsum : 1 < p⁻¹ + q⁻¹) (n : ℕ) :
    infiniteDifferentialApply (fun z => z ^ n * φ z) f =
      iteratedDeriv n (infiniteDifferentialApply φ f) := by
  induction n with
  | zero => simp only [pow_zero, one_mul, iteratedDeriv_zero]
  | succ n ih =>
      have ho : TauCeti.OrderLE (fun z => z ^ n * φ z) (max ρ 0) := by
        simpa only [eval_pow, eval_X] using orderLE_polynomial_mul hoφ (X ^ n)
      have heq : (fun z : ℂ => z ^ (n + 1) * φ z) =
          (fun z => z * (z ^ n * φ z)) := by
        ext z
        rw [pow_succ]
        ring
      rw [heq, infiniteDifferentialApply_id_mul_eq_deriv (by fun_prop) ho hp
        (max_lt hρ hp) hf hof hq hσ hsum, ih, iteratedDeriv_succ]

/-- A polynomial factor of an entire infinite symbol acts by the finite
polynomial differential operator on the infinite image. Both zero symbols and
zero outputs are included. -/
theorem infiniteDifferentialApply_polynomial_mul (P : ℂ[X])
    {φ f : ℂ → ℂ} {ρ σ p q : ℝ}
    (hφ : Differentiable ℂ φ) (hoφ : TauCeti.OrderLE φ ρ) (hp : 0 < p) (hρ : ρ < p)
    (hf : Differentiable ℂ f) (hof : TauCeti.OrderLE f σ) (hq : 0 < q) (hσ : σ < q)
    (hsum : 1 < p⁻¹ + q⁻¹) :
    infiniteDifferentialApply (fun z => P.eval z * φ z) f =
      P.differentialApply (infiniteDifferentialApply φ f) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
      have heq : (fun z => (P + Q).eval z * φ z) =
          (fun z => P.eval z * φ z + Q.eval z * φ z) := by
        ext z
        simp only [eval_add, add_mul]
      rw [heq, infiniteDifferentialApply_add_symbol (by fun_prop)
        (orderLE_polynomial_mul hoφ P) (by fun_prop) (orderLE_polynomial_mul hoφ Q)
        hp (max_lt hρ hp) hf hof hq hσ hsum, hP, hQ, differentialApply_add]
  | monomial n c =>
      have heq : (fun z => (monomial n c).eval z * φ z) =
          (fun z => c * (z ^ n * φ z)) := by
        ext z
        simp only [eval_monomial, mul_assoc]
      rw [heq, infiniteDifferentialApply_const_mul_symbol,
        infiniteDifferentialApply_pow_mul hφ hoφ hp hρ hf hof hq hσ hsum,
        differentialApply_monomial]

end Complex
