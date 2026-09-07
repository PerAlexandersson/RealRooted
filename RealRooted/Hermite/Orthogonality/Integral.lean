/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import RealRooted.Hermite.Orthogonality
public import RealRooted.Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

import Mathlib.RingTheory.Polynomial.Hermite.Gaussian
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Algebra.Polynomial.Eval.SMul
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Gaussian integral orthogonality for probabilists' Hermite polynomials

This file identifies the normalized algebraic Favard functional with
integration against the unnormalized standard Gaussian weight
`exp (-(x² / 2))`.  Consequently,

`∫ x, Hₘ(x) Hₙ(x) exp (-(x² / 2)) = δₘₙ √(2π) n!`.
-/

@[expose] public section

open MeasureTheory Polynomial

noncomputable section

namespace RealRooted

/-- The unnormalized standard Gaussian weight used by probabilists' Hermite
polynomials. -/
def hermiteGaussianWeight (x : ℝ) : ℝ :=
  Real.exp (-(x ^ 2 / 2))

/-- A polynomial multiplied by the probabilists' Hermite Gaussian weight. -/
def hermiteGaussianIntegrand (p : ℝ[X]) (x : ℝ) : ℝ :=
  p.eval x * hermiteGaussianWeight x

/-- Every real polynomial is integrable against the probabilists' Hermite
Gaussian weight. -/
theorem integrable_hermiteGaussianIntegrand (p : ℝ[X]) :
    Integrable (hermiteGaussianIntegrand p) := by
  have h := Polynomial.integrable_eval_mul_exp_neg_mul_sq
    p (b := (1 / 2 : ℝ)) (by norm_num)
  refine h.congr (Filter.Eventually.of_forall ?_)
  intro x
  simp only [hermiteGaussianIntegrand, hermiteGaussianWeight]
  congr 2
  ring

private theorem hasDerivAt_hermiteGaussianWeight (x : ℝ) :
    HasDerivAt hermiteGaussianWeight
      (-x * hermiteGaussianWeight x) x := by
  have hd : DifferentiableAt ℝ hermiteGaussianWeight x := by
    unfold hermiteGaussianWeight
    fun_prop
  apply hd.hasDerivAt.congr_deriv
  change deriv (fun y : ℝ => Real.exp (-(y ^ 2 / 2))) x =
    -x * Real.exp (-(x ^ 2 / 2))
  simpa [Function.iterate_one, Polynomial.hermite_one] using
    Polynomial.deriv_gaussian_eq_hermite_mul_gaussian 1 x

/-- A sign-adjusted Hermite polynomial times the Gaussian is a primitive of
the next Hermite polynomial times the Gaussian. -/
private theorem hasDerivAt_neg_hermite_mul_gaussian (n : ℕ) (x : ℝ) :
    HasDerivAt
      (fun y : ℝ =>
        -(aeval y (Polynomial.hermite n) * hermiteGaussianWeight y))
      (aeval x (Polynomial.hermite (n + 1)) * hermiteGaussianWeight x) x := by
  apply (((Polynomial.hermite n).hasDerivAt_aeval x).mul
    (hasDerivAt_hermiteGaussianWeight x)).neg.congr_deriv
  rw [Polynomial.hermite_succ, map_sub, map_mul, aeval_X]
  ring

/-- A sign-adjusted real Hermite polynomial times the Gaussian weight is a
primitive of the next Hermite polynomial times that weight. -/
theorem hasDerivAt_neg_eval_hermiteReal_mul_gaussian (n : ℕ) (x : ℝ) :
    HasDerivAt
      (fun y : ℝ =>
        -((hermiteReal n).eval y * hermiteGaussianWeight y))
      ((hermiteReal (n + 1)).eval x * hermiteGaussianWeight x) x := by
  simpa only [eval_hermiteReal] using
    hasDerivAt_neg_hermite_mul_gaussian n x

private theorem integrable_aeval_hermite_mul_gaussian (n : ℕ) :
    Integrable (fun x : ℝ =>
      aeval x (Polynomial.hermite n) * hermiteGaussianWeight x) := by
  refine (integrable_hermiteGaussianIntegrand (hermiteReal n)).congr
    (Filter.Eventually.of_forall ?_)
  intro x
  simp only [hermiteGaussianIntegrand, eval_hermiteReal]

/-- Positive-degree probabilists' Hermite polynomials have zero integral
against the unnormalized standard Gaussian weight. -/
theorem integral_hermiteReal_mul_gaussian_eq_zero {n : ℕ} (hn : n ≠ 0) :
    ∫ x : ℝ, hermiteGaussianIntegrand (hermiteReal n) x = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  have hzero := MeasureTheory.integral_eq_zero_of_hasDerivAt_of_integrable
    (fun x => hasDerivAt_neg_hermite_mul_gaussian k x)
    (integrable_aeval_hermite_mul_gaussian (k + 1))
    (integrable_aeval_hermite_mul_gaussian k).neg
  simpa only [hermiteGaussianIntegrand, eval_hermiteReal] using hzero

/-- Integration against the unnormalized standard Gaussian, bundled as a
linear functional on real polynomials. -/
def hermiteGaussianFunctional : ℝ[X] →ₗ[ℝ] ℝ where
  toFun p := ∫ x : ℝ, hermiteGaussianIntegrand p x
  map_add' p q := by
    calc
      (∫ x : ℝ, hermiteGaussianIntegrand (p + q) x) =
          ∫ x : ℝ,
            hermiteGaussianIntegrand p x + hermiteGaussianIntegrand q x := by
        apply integral_congr_ae
        filter_upwards with x
        simp [hermiteGaussianIntegrand, add_mul]
      _ = (∫ x : ℝ, hermiteGaussianIntegrand p x) +
          ∫ x : ℝ, hermiteGaussianIntegrand q x :=
        integral_add (integrable_hermiteGaussianIntegrand p)
          (integrable_hermiteGaussianIntegrand q)
  map_smul' c p := by
    change (∫ x : ℝ, hermiteGaussianIntegrand (c • p) x) =
      c * ∫ x : ℝ, hermiteGaussianIntegrand p x
    calc
      _ = ∫ x : ℝ, c * hermiteGaussianIntegrand p x := by
        apply integral_congr_ae
        filter_upwards with x
        simp [hermiteGaussianIntegrand, Polynomial.eval_smul,
          smul_eq_mul, mul_assoc]
      _ = c * ∫ x : ℝ, hermiteGaussianIntegrand p x :=
        integral_const_mul c _

@[simp] theorem hermiteGaussianFunctional_apply (p : ℝ[X]) :
    hermiteGaussianFunctional p =
      ∫ x : ℝ, hermiteGaussianIntegrand p x :=
  rfl

/-- The total mass of the unnormalized standard Gaussian is `√(2π)`. -/
@[simp] theorem hermiteGaussianFunctional_one :
    hermiteGaussianFunctional 1 = Real.sqrt (2 * Real.pi) := by
  rw [hermiteGaussianFunctional_apply]
  simp only [hermiteGaussianIntegrand, eval_one, one_mul,
    hermiteGaussianWeight]
  calc
    (∫ x : ℝ, Real.exp (-(x ^ 2 / 2))) =
        ∫ x : ℝ, Real.exp (-(1 / 2 : ℝ) * x ^ 2) := by
      apply integral_congr_ae
      filter_upwards with x
      congr 1
      ring
    _ = Real.sqrt (Real.pi / (1 / 2 : ℝ)) := integral_gaussian (1 / 2)
    _ = Real.sqrt (2 * Real.pi) := by
      congr 1
      ring

/-- Positive-degree real Hermite polynomials vanish under the Gaussian
functional. -/
@[simp] theorem hermiteGaussianFunctional_hermiteReal {n : ℕ} (hn : n ≠ 0) :
    hermiteGaussianFunctional (hermiteReal n) = 0 :=
  integral_hermiteReal_mul_gaussian_eq_zero hn

/-- The Gaussian functional is its total mass times the normalized Hermite
Favard functional. -/
theorem hermiteGaussianFunctional_eq_smul_favardFunctional :
    hermiteGaussianFunctional =
      Real.sqrt (2 * Real.pi) •
        hermiteReal_satisfiesFavardRecurrence.functional := by
  calc
    hermiteGaussianFunctional =
        hermiteGaussianFunctional 1 •
          hermiteReal_satisfiesFavardRecurrence.functional :=
      hermiteReal_satisfiesFavardRecurrence.linearMap_eq_smul_functional
        hermiteGaussianFunctional
        (fun _ hn => hermiteGaussianFunctional_hermiteReal hn)
    _ = Real.sqrt (2 * Real.pi) •
        hermiteReal_satisfiesFavardRecurrence.functional := by
      rw [hermiteGaussianFunctional_one]

/-- The symmetric bilinear pairing induced by the unnormalized Gaussian
functional. -/
def hermiteGaussianPairing : LinearMap.BilinForm ℝ ℝ[X] :=
  (LinearMap.mul ℝ ℝ[X]).compr₂ hermiteGaussianFunctional

@[simp] theorem hermiteGaussianPairing_apply (p q : ℝ[X]) :
    hermiteGaussianPairing p q =
      ∫ x : ℝ, hermiteGaussianIntegrand (p * q) x :=
  rfl

/-- The Gaussian pairing is `√(2π)` times the normalized Favard pairing. -/
theorem hermiteGaussianPairing_eq_smul_favardPairing :
    hermiteGaussianPairing =
      Real.sqrt (2 * Real.pi) •
        hermiteReal_satisfiesFavardRecurrence.pairing := by
  apply LinearMap.ext
  intro p
  apply LinearMap.ext
  intro q
  have hfunctional := LinearMap.congr_fun
    hermiteGaussianFunctional_eq_smul_favardFunctional (p * q)
  simpa [hermiteGaussianPairing, SatisfiesFavardRecurrence.pairing_apply,
    smul_eq_mul] using hfunctional

@[simp] theorem hermiteGaussianPairing_apply_eq_favardPairing
    (p q : ℝ[X]) :
    hermiteGaussianPairing p q =
      Real.sqrt (2 * Real.pi) *
        hermiteReal_satisfiesFavardRecurrence.pairing p q := by
  rw [hermiteGaussianPairing_eq_smul_favardPairing]
  rfl

/-- Classical Gaussian orthogonality for the real probabilists' Hermite
family. -/
theorem hermiteReal_integral_orthogonal (i j : ℕ) :
    (∫ x : ℝ,
      (hermiteReal i).eval x * (hermiteReal j).eval x *
        hermiteGaussianWeight x) =
      if i = j then
        Real.sqrt (2 * Real.pi) * (i.factorial : ℝ)
      else 0 := by
  rw [show
    (∫ x : ℝ,
      (hermiteReal i).eval x * (hermiteReal j).eval x *
        hermiteGaussianWeight x) =
      hermiteGaussianPairing (hermiteReal i) (hermiteReal j) by
    rw [hermiteGaussianPairing_apply]
    apply integral_congr_ae
    filter_upwards with x
    simp [hermiteGaussianIntegrand, mul_assoc]]
  rw [hermiteGaussianPairing_apply_eq_favardPairing,
    hermiteReal_favardPairing_apply]
  split_ifs <;> ring

/-- The squared Gaussian norm of the `n`th real probabilists' Hermite
polynomial is `√(2π) n!`. -/
theorem hermiteReal_integral_normSq (n : ℕ) :
    (∫ x : ℝ,
      ((hermiteReal n).eval x) ^ 2 * hermiteGaussianWeight x) =
      Real.sqrt (2 * Real.pi) * (n.factorial : ℝ) := by
  simpa [pow_two] using hermiteReal_integral_orthogonal n n

/-- The Gaussian integral of a nonzero polynomial square is positive. -/
theorem hermiteGaussian_integral_mul_self_pos {p : ℝ[X]} (hp : p ≠ 0) :
    0 < ∫ x : ℝ, (p.eval x) ^ 2 * hermiteGaussianWeight x := by
  rw [show
    (∫ x : ℝ, (p.eval x) ^ 2 * hermiteGaussianWeight x) =
      hermiteGaussianPairing p p by
    rw [hermiteGaussianPairing_apply]
    apply integral_congr_ae
    filter_upwards with x
    simp [hermiteGaussianIntegrand, pow_two]]
  rw [hermiteGaussianPairing_apply_eq_favardPairing]
  apply mul_pos
  · exact Real.sqrt_pos.2 (mul_pos (by norm_num) Real.pi_pos)
  · simpa [SatisfiesFavardRecurrence.pairing_apply] using
      hermiteReal_favardFunctional_mul_self_pos hp

end RealRooted
