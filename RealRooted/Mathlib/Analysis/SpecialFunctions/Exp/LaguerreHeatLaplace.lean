/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

import RealRooted.Mathlib.RingTheory.Polynomial.Laguerre.LaplaceKernel
public import RealRooted.Mathlib.RingTheory.Polynomial.Laguerre.Basic
import RealRooted.Mathlib.Analysis.SpecialFunctions.Exp.WeightedHeatLaplace
public import RealRooted.Mathlib.Analysis.SpecialFunctions.Exp.ExponentialSum
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
import RealRooted.Mathlib.Analysis.SpecialFunctions.Exp.ExponentialSumLaplace
import Mathlib.Tactic.Ring
import RealRooted.Mathlib.Analysis.SpecialFunctions.Exp.ExponentialSumBounds

/-!
# The Laguerre representation of weighted heat-trace moments

The two integrals in Zhang, arXiv:1506.07012v13, equations (2.16) and
(2.18)--(2.21), agree and have the same positive spectral sum. All integrals
are actually integrable. The Laplace endpoint zero is included when the
inverse spectral moment is summable.

The sign-reversed monic polynomial used here already contains the factor
`k!` in the classical formula. It is evaluated at `-x*t`.
-/

public section

open MeasureTheory Set

namespace Real

/-- The Laguerre-weighted heat integral equals the positive weighted
spectral sum, including at the Laplace endpoint zero. -/
theorem laplace_eval_generalizedLaguerre_exponentialMomentSum
    {ι : Type*} [Countable ι] {r : ι → ℝ} {a : ℝ}
    (hr : ∀ i, 0 < r i) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hs : Summable (fun i ↦ r i ^ (-a))) (k m : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    IntegrableOn (fun t : ℝ ↦ exp (-x * t) * t ^ m * exponentialMomentSum r 0 t *
        (Polynomial.generalizedLaguerre k (m : ℝ)).eval (-x * t)) (Ioi 0) ∧
      (∫ t : ℝ in Ioi 0, exp (-x * t) * t ^ m * exponentialMomentSum r 0 t *
        (Polynomial.generalizedLaguerre k (m : ℝ)).eval (-x * t)) =
          ∑' i, r i ^ k * ((k + m).factorial : ℝ) / (x + r i) ^ (k + m + 1) := by
  have hmoment (n : ℕ) := laplace_exponentialMomentSum_of_inverse_moment
    hr ha ha1 hs n hx
  obtain ⟨hint, heval⟩ :=
    Polynomial.integrableOn_and_integral_exp_mul_pow_mul_eval_generalizedLaguerre
      (exponentialMomentSum r 0) k m x (fun j _ ↦ (hmoment (m + j)).1)
  refine ⟨hint, heval.trans ?_⟩
  let c : ℕ → ℝ := fun j ↦ (k.choose j : ℝ) *
    (ascPochhammer ℝ (k - j)).eval ((m : ℝ) + j + 1) * (-x) ^ j
  let F : ℕ → ι → ℝ := fun j i ↦
    c j * (((m + j).factorial : ℝ) / (x + r i) ^ (m + j + 1))
  have hsum (j : ℕ) : Summable (F j) :=
    (summable_factorial_div_add_pow hr (m + j)
      (summable_inv_pow_of_inverse_moment hr ha ha1 hs (m + j)) hx).mul_left (c j)
  calc
    _ = ∑ j ∈ Finset.range (k + 1), ∑' i, F j i := by
      apply Finset.sum_congr rfl
      intro j _
      rw [(hmoment (m + j)).2]
      exact (tsum_mul_left : (∑' i, F j i) = _).symm
    _ = ∑' i, ∑ j ∈ Finset.range (k + 1), F j i :=
      (Summable.tsum_finsetSum (fun j _ ↦ hsum j)).symm
    _ = _ := by
      apply tsum_congr
      intro i
      calc
        _ = ∑ j ∈ Finset.range (k + 1),
            (k.choose j : ℝ) *
              (ascPochhammer ℝ (k - j)).eval ((m : ℝ) + j + 1) *
                (-x) ^ j * ((m + j).factorial : ℝ) / (x + r i) ^ (m + j + 1) := by
          apply Finset.sum_congr rfl
          intro j _
          dsimp only [F, c]
          ring
        _ = ((k + m).factorial : ℝ) * r i ^ k / (x + r i) ^ (k + m + 1) := by
          have h := Polynomial.sum_generalizedLaguerre_laplace_coefficients k m
            (add_pos_of_nonneg_of_pos hx (hr i)).ne' (-x)
          simpa only [show x + r i + -x = r i by ring] using h
        _ = _ := by ring

/-- The positive weighted heat integral and the Laguerre integral coincide.
This is Zhang's full two-index heat representation with the repository's
factorial polynomial normalization. -/
theorem weighted_heat_integral_eq_laguerre_heat_integral
    {ι : Type*} [Countable ι] {r : ι → ℝ} {a : ℝ}
    (hr : ∀ i, 0 < r i) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hs : Summable (fun i ↦ r i ^ (-a))) (k m : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    (∫ t : ℝ in Ioi 0, exp (-x * t) * t ^ (k + m) * exponentialMomentSum r k t) =
      ∫ t : ℝ in Ioi 0, exp (-x * t) * t ^ m * exponentialMomentSum r 0 t *
        (Polynomial.generalizedLaguerre k (m : ℝ)).eval (-x * t) :=
  (laplace_weighted_exponentialMomentSum_of_inverse_moment hr ha ha1 hs k m hx).2.trans
    (laplace_eval_generalizedLaguerre_exponentialMomentSum hr ha ha1 hs k m hx).2.symm

/-- Zhang's signed heat derivative is the nonnegative weighted spectral
moment. Positivity is a consequence, not a definition of the derivative. -/
theorem neg_mul_pow_mul_iteratedDeriv_exponentialMomentSum_zero
    {ι : Type*} {r : ι → ℝ} {a : ℝ}
    (hr : ∀ i, 0 < r i) (ha : 0 ≤ a)
    (hs : Summable (fun i ↦ r i ^ (-a))) (k : ℕ) {t : ℝ} (ht : 0 < t) :
    (-t) ^ k * iteratedDeriv k (exponentialMomentSum r 0) t =
      t ^ k * exponentialMomentSum r k t := by
  rw [iteratedDeriv_exponentialMomentSum_zero hr ha hs k ht]
  calc
    _ = ((-t) * (-1)) ^ k * exponentialMomentSum r k t := by rw [mul_pow]; ring
    _ = _ := by rw [neg_mul_neg, mul_one]

end Real
