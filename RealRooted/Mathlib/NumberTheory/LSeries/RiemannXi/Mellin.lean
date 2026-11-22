/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import RealRooted.Mathlib.NumberTheory.LSeries.RiemannXi.Moments
public import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import RealRooted.Mathlib.Analysis.MellinTransform.LogMoments
import TauCeti.NumberTheory.LSeries.MellinGrowth
import Mathlib.Analysis.Complex.Asymptotics
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Central derivatives of completed zeta as theta moments

Splitting the completed-zeta integral at one and using the functional equation
expresses its even central derivatives by positive logarithmic theta moments.
-/

@[expose] public section

open Complex Set MeasureTheory HurwitzZeta Filter Asymptotics

/-- The upper Mellin integral of the Riemann theta kernel. -/
noncomputable def riemannThetaMellin (s : ℂ) : ℂ :=
  ∫ t in Ioi (1 : ℝ), (riemannThetaKernel t : ℂ) * (t : ℂ) ^ (s - 1)

private theorem kernel_continuous :
    ContinuousOn (fun t => (riemannThetaKernel t : ℂ)) (Ici 1) :=
  continuous_ofReal.comp_continuousOn
    (continuousOn_riemannThetaKernel.mono (fun _ ht => zero_lt_one.trans_le ht))

private theorem kernel_isBigO (r : ℝ) :
    (fun t => (riemannThetaKernel t : ℂ)) =O[atTop] fun t => t ^ r :=
  isBigO_ofReal_left.mpr (isBigO_riemannThetaKernel_rpow r)

/-- The upper Mellin integral of the theta kernel is entire. -/
theorem differentiable_riemannThetaMellin : Differentiable ℂ riemannThetaMellin := by
  intro s
  change DifferentiableAt ℂ
    (fun z => ∫ t in Ioi (1 : ℝ), (riemannThetaKernel t : ℂ) * (t : ℂ) ^ (z - 1)) s
  have h := (hasDerivAt_integral_mul_log_pow_cpow kernel_continuous kernel_isBigO 0 s)
  simpa only [pow_zero, mul_one] using h.differentiableAt

/-- At exponent one quarter, all derivatives of the Mellin integral are real moments. -/
theorem iteratedDeriv_riemannThetaMellin_quarter (n : ℕ) :
    iteratedDeriv n riemannThetaMellin (1 / 4) = (riemannXiMoment n : ℂ) := by
  change iteratedDeriv n (fun z => ∫ t in Ioi (1 : ℝ),
    (riemannThetaKernel t : ℂ) * (t : ℂ) ^ (z - 1)) (1 / 4) = _
  rw [iteratedDeriv_integral_mul_cpow kernel_continuous kernel_isBigO,
    riemannXiMoment, ← integral_complex_ofReal]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  dsimp only
  have ht0 := (zero_lt_one.trans ht).le
  rw [show (1 / 4 : ℂ) - 1 = ((-3 / 4 : ℝ) : ℂ) by push_cast; ring,
    ← ofReal_cpow ht0]
  push_cast
  rfl

/-- The split Mellin representation of the entire part of completed zeta. -/
theorem completedRiemannZeta₀_eq_mellin (s : ℂ) :
    completedRiemannZeta₀ s =
      (riemannThetaMellin (s / 2) + riemannThetaMellin ((1 - s) / 2)) / 2 := by
  have hi (z : ℂ) : IntegrableOn
      (fun t : ℝ => (t : ℂ) ^ (z - 1) * (riemannThetaKernel t : ℂ)) (Ioi 1) := by
    simpa only [pow_zero, mul_one, mul_comm] using
      integrableOn_mul_log_pow_cpow kernel_continuous kernel_isBigO 0 z
  have h := (hurwitzEvenFEPair 0).Λ₀_eq_integral_add_smul_integral (s / 2)
    (by simpa [hurwitzEvenFEPair, riemannThetaKernel, Function.comp_def] using hi (s / 2))
    (by simpa [hurwitzEvenFEPair, riemannThetaKernel, Function.comp_def,
      evenKernel_eq_cosKernel_of_zero] using hi ((1 / 2 : ℂ) - s / 2))
  rw [completedRiemannZeta₀, completedHurwitzZetaEven₀, h]
  have he : (1 / 2 : ℂ) - s / 2 = (1 - s) / 2 := by ring
  simp only [hurwitzEvenFEPair, Function.comp_apply, ite_true, ofReal_div, ofReal_one,
    ofReal_ofNat, he, smul_eq_mul, one_mul, riemannThetaMellin, riemannThetaKernel,
    ofReal_sub, evenKernel_eq_cosKernel_of_zero, mul_comm]

private theorem deriv_affine_mellin (a b : ℂ) (n : ℕ) :
    iteratedDeriv n (fun z => riemannThetaMellin (b + a * z)) 0 =
      a ^ n * iteratedDeriv n riemannThetaMellin b := by
  have hd : ContDiff ℂ n (fun z => riemannThetaMellin (b + z)) :=
    (differentiable_riemannThetaMellin.comp (differentiable_id.const_add b)).contDiff
  have h := congrFun (iteratedDeriv_comp_const_mul hd a) 0
  simpa only [mul_zero, iteratedDeriv_comp_const_add, add_zero] using h

/-- Even central derivatives of the completed zeta function are theta moments. -/
theorem iteratedDeriv_completedRiemannZeta₀_even (n : ℕ) :
    iteratedDeriv (2 * n) completedRiemannZeta₀ (1 / 2) =
      (1 / 2 : ℂ) ^ (2 * n) * (riemannXiMoment (2 * n) : ℂ) := by
  have heq : (fun z => completedRiemannZeta₀ (1 / 2 + z)) = fun z =>
      (riemannThetaMellin (1 / 4 + (1 / 2) * z) +
        riemannThetaMellin (1 / 4 + (-1 / 2) * z)) / 2 := by
    funext z
    rw [completedRiemannZeta₀_eq_mellin]
    congr 2 <;> congr 1 <;> ring
  have h := congrArg (fun f : ℂ → ℂ => iteratedDeriv (2 * n) f 0) heq
  have hd (a : ℂ) : ContDiffAt ℂ (2 * n)
      (fun z => riemannThetaMellin (1 / 4 + a * z)) 0 :=
    (differentiable_riemannThetaMellin.comp (by fun_prop)).contDiff.contDiffAt
  simp only [iteratedDeriv_comp_const_add, add_zero] at h
  rw [iteratedDeriv_div_const,
    iteratedDeriv_fun_add (hd _) (hd _), deriv_affine_mellin,
    deriv_affine_mellin, iteratedDeriv_riemannThetaMellin_quarter] at h
  have hn : (-1 / 2 : ℂ) ^ (2 * n) = (1 / 2 : ℂ) ^ (2 * n) := by
    rw [neg_div, neg_pow, Even.neg_one_pow (even_two_mul n), one_mul]
  rw [hn] at h
  exact h.trans (by ring)
