/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import RealRooted.Mathlib.Analysis.SpecialFunctions.Exp.ExponentialSum
import RealRooted.Mathlib.Analysis.SpecialFunctions.Exp.WeightedMixtureLaplace
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
import RealRooted.Mathlib.Analysis.SpecialFunctions.Exp.ExponentialSumBounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Weighted heat-trace Laplace moments

For a positive spectrum `r`, Zhang's `Theta_k(t)` is `t^k` times
`exponentialMomentSum r k t`. Its `m`th Laplace moment is the positive
factorial sum in equations (2.15)--(2.16) of arXiv:1506.07012v13.
The inverse `(m+1)`st spectral moment suffices; the exponent need not
increase with `k`. The endpoint `x = 0` is included.
-/

public section

open MeasureTheory Set

namespace Real

/-- Polynomial weighting of the spectrum cancels against the additional
inverse moments required by the weighted Laplace integral. -/
theorem summable_pow_div_pow_add {ι : Type*} {r : ι → ℝ}
    (hr : ∀ i, r i ≠ 0) (k m : ℕ)
    (hs : Summable (fun i ↦ (r i ^ (m + 1))⁻¹)) :
    Summable (fun i ↦ r i ^ k / r i ^ (k + m + 1)) := by
  apply hs.congr
  intro i
  rw [show k + m + 1 = k + (m + 1) by lia, pow_add]
  field_simp [hr i]
  simp only [pow_add, pow_succ]
  ring

/-- Every weighted heat-trace Laplace moment is a positive resolvent sum. -/
theorem laplace_weighted_exponentialMomentSum
    {ι : Type*} [Countable ι] {r : ι → ℝ}
    (hr : ∀ i, 0 < r i) (k m : ℕ)
    (hs : Summable (fun i ↦ (r i ^ (m + 1))⁻¹)) {x : ℝ} (hx : 0 ≤ x) :
    IntegrableOn (fun t : ℝ ↦ exp (-x * t) * t ^ (k + m) *
        exponentialMomentSum r k t) (Ioi 0) ∧
      (∫ t : ℝ in Ioi 0, exp (-x * t) * t ^ (k + m) *
        exponentialMomentSum r k t) =
          ∑' i, r i ^ k * ((k + m).factorial : ℝ) / (x + r i) ^ (k + m + 1) := by
  simpa only [exponentialMomentSum] using
    integrableOn_and_integral_exp_mul_pow_mul_tsum hr (fun i ↦ pow_nonneg (hr i).le k)
      (k + m) (summable_pow_div_pow_add (fun i ↦ (hr i).ne') k m hs) hx

/-- An inverse spectral moment of exponent at most one gives all weighted
heat-trace Laplace identities, including at the endpoint zero. -/
theorem laplace_weighted_exponentialMomentSum_of_inverse_moment
    {ι : Type*} [Countable ι] {r : ι → ℝ} {a : ℝ}
    (hr : ∀ i, 0 < r i) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hs : Summable (fun i ↦ r i ^ (-a))) (k m : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    IntegrableOn (fun t : ℝ ↦ exp (-x * t) * t ^ (k + m) *
        exponentialMomentSum r k t) (Ioi 0) ∧
      (∫ t : ℝ in Ioi 0, exp (-x * t) * t ^ (k + m) *
        exponentialMomentSum r k t) =
          ∑' i, r i ^ k * ((k + m).factorial : ℝ) / (x + r i) ^ (k + m + 1) :=
  laplace_weighted_exponentialMomentSum hr k m
    (summable_inv_pow_of_inverse_moment hr ha ha1 hs m) hx

end Real
