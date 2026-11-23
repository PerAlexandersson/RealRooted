/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import RealRooted.Mathlib.Analysis.Complex.InfiniteDifferential.Basic
public import RealRooted.Mathlib.Analysis.Calculus.IteratedDeriv.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import RealRooted.Mathlib.Analysis.Complex.InfiniteDifferential.GaussianPolynomialBound
import RealRooted.Mathlib.Analysis.Complex.InfiniteDifferential.GaussianSymbolAlgebra
import RealRooted.Mathlib.Analysis.Complex.InfiniteDifferential.SymbolAlgebra
import RealRooted.Mathlib.Analysis.Calculus.IteratedDeriv.PolynomialAlgebra

/-!
# Finite polynomial factors of Gaussian differential symbols

The strict Gaussian margin absorbs every fixed polynomial factor. The
result concerns the actual convergent differential sums, including zero output.
-/

public section

open Polynomial

namespace Complex

/-- The strict product bound permits a larger symbol coefficient. -/
private theorem exists_left_gaussian_margin {a b : ℝ} (hb : 0 < b)
    (hab : 4 * a * b < 1) : ∃ d, a < d ∧ 4 * d * b < 1 := by
  have haU : a < 1 / (4 * b) :=
    (lt_div_iff₀ (by positivity)).mpr (by nlinarith)
  obtain ⟨d, had, hdU⟩ := exists_between haU
  refine ⟨d, had, ?_⟩
  have h := (lt_div_iff₀ (by positivity : 0 < 4 * b)).mp hdU
  nlinarith

/-- A monomial factor differentiates the actual image in the sharp
Gaussian convergence range. -/
theorem infiniteDifferentialApply_pow_mul_of_gaussian {φ f : ℂ → ℂ}
    (hφ : Differentiable ℂ φ) (hf : Differentiable ℂ f)
    {Mφ Mf a b : ℝ} (hMφ : 0 ≤ Mφ) (hMf : 0 ≤ Mf) (ha : 0 < a) (hb : 0 < b)
    (hab : 4 * a * b < 1)
    (hφbound : ∀ w, ‖φ w‖ ≤ Mφ * Real.exp (a * ‖w‖ ^ 2))
    (hfbound : ∀ w, ‖f w‖ ≤ Mf * Real.exp (b * ‖w‖ ^ 2)) (n : ℕ) :
    infiniteDifferentialApply (fun z ↦ z ^ n * φ z) f =
      iteratedDeriv n (infiniteDifferentialApply φ f) := by
  induction n with
  | zero => simp only [pow_zero, one_mul, iteratedDeriv_zero]
  | succ n ih =>
      obtain ⟨d, had, hdb⟩ := exists_left_gaussian_margin hb hab
      obtain ⟨M, hM, hbound⟩ := exists_norm_polynomial_mul_le_exp_sq
        (X ^ n) hMφ had hφbound
      simp only [eval_pow, eval_X] at hbound
      have heq : (fun z : ℂ ↦ z ^ (n + 1) * φ z) =
          (fun z ↦ z * (z ^ n * φ z)) := by
        ext z
        rw [pow_succ]
        ring
      rw [heq, infiniteDifferentialApply_id_mul_eq_deriv_of_gaussian
        (by fun_prop) hf hM.le hMf (ha.trans had) hb hdb hbound hfbound,
        ih, iteratedDeriv_succ]

/-- Multiplying an entire symbol by a polynomial composes its Gaussian
differential image with the corresponding finite differential operator. -/
theorem infiniteDifferentialApply_polynomial_mul_of_gaussian (P : ℂ[X])
    {φ f : ℂ → ℂ} (hφ : Differentiable ℂ φ) (hf : Differentiable ℂ f)
    {Mφ Mf a b : ℝ} (hMφ : 0 ≤ Mφ) (hMf : 0 ≤ Mf) (ha : 0 < a) (hb : 0 < b)
    (hab : 4 * a * b < 1)
    (hφbound : ∀ w, ‖φ w‖ ≤ Mφ * Real.exp (a * ‖w‖ ^ 2))
    (hfbound : ∀ w, ‖f w‖ ≤ Mf * Real.exp (b * ‖w‖ ^ 2)) :
    infiniteDifferentialApply (fun z ↦ P.eval z * φ z) f =
      P.differentialApply (infiniteDifferentialApply φ f) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
      obtain ⟨d, had, hdb⟩ := exists_left_gaussian_margin hb hab
      obtain ⟨MP, hMP, hPbound⟩ := exists_norm_polynomial_mul_le_exp_sq P hMφ had hφbound
      obtain ⟨MQ, hMQ, hQbound⟩ := exists_norm_polynomial_mul_le_exp_sq Q hMφ had hφbound
      have heq : (fun z ↦ (P + Q).eval z * φ z) =
          (fun z ↦ P.eval z * φ z + Q.eval z * φ z) := by
        ext z
        simp only [eval_add, add_mul]
      rw [heq, infiniteDifferentialApply_add_symbol_of_gaussian
        (by fun_prop) (by fun_prop) hf hMP.le hMQ.le hMf (ha.trans had) hb hdb
          hPbound hQbound hfbound, hP, hQ, differentialApply_add]
  | monomial n c =>
      have heq : (fun z ↦ (monomial n c).eval z * φ z) =
          (fun z ↦ c * (z ^ n * φ z)) := by
        ext z
        simp only [eval_monomial, mul_assoc]
      rw [heq, infiniteDifferentialApply_const_mul_symbol,
        infiniteDifferentialApply_pow_mul_of_gaussian
          hφ hf hMφ hMf ha hb hab hφbound hfbound, differentialApply_monomial]

end Complex
