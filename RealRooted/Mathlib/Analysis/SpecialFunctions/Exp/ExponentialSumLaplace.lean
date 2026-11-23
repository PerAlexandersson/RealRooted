/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import RealRooted.Mathlib.Analysis.SpecialFunctions.Exp.ExponentialSum
import RealRooted.Mathlib.Analysis.SpecialFunctions.Exp.ExponentialSumBounds
import RealRooted.Mathlib.Analysis.SpecialFunctions.Exp.WeightedMixtureLaplace

/-!
# Laplace transforms of positive spectral heat traces

For a positive spectrum, the `k`th Laplace moment is finite on the closed
nonnegative axis whenever the inverse `(k + 1)`st spectral moment is
summable. The exact integral and its bound are Zhang, arXiv:1506.07012v13,
Lemma 2, equations (2.5) and the integral equality in (2.6).

The hypotheses state summability explicitly. A heat trace can exist at
every positive time while its zeroth Laplace moment diverges.
-/

public section

open MeasureTheory Set

namespace Real

/-- Nonnegative shifts decrease reciprocal natural spectral moments. -/
theorem summable_factorial_div_add_pow {ι : Type*} {r : ι → ℝ}
    (hr : ∀ i, 0 < r i) (k : ℕ)
    (hs : Summable (fun i ↦ (r i ^ (k + 1))⁻¹)) {x : ℝ} (hx : 0 ≤ x) :
    Summable (fun i ↦ (k.factorial : ℝ) / (x + r i) ^ (k + 1)) := by
  simpa only [one_mul] using summable_mul_factorial_div_add_pow
    hr (fun _ ↦ zero_le_one) k (by simpa only [one_div] using hs) hx

/-- The Laplace transform of a positive heat trace equals the shifted
inverse spectral moment, with actual integrability also established. -/
theorem integrableOn_and_integral_exp_mul_pow_mul_exponentialMomentSum
    {ι : Type*} [Countable ι] {r : ι → ℝ}
    (hr : ∀ i, 0 < r i) (k : ℕ)
    (hs : Summable (fun i ↦ (r i ^ (k + 1))⁻¹)) {x : ℝ} (hx : 0 ≤ x) :
    IntegrableOn (fun t : ℝ ↦ exp (-x * t) * t ^ k * exponentialMomentSum r 0 t)
        (Ioi 0) ∧
      (∫ t : ℝ in Ioi 0, exp (-x * t) * t ^ k * exponentialMomentSum r 0 t) =
        ∑' i, (k.factorial : ℝ) / (x + r i) ^ (k + 1) := by
  simpa only [exponentialMomentSum, pow_zero, one_mul] using
    integrableOn_and_integral_exp_mul_pow_mul_tsum hr (fun _ ↦ zero_le_one) k
      (by simpa only [one_div] using hs) hx

/-- The Laplace moment is bounded by its value at the endpoint zero. -/
theorem integral_exp_mul_pow_mul_exponentialMomentSum_le
    {ι : Type*} [Countable ι] {r : ι → ℝ}
    (hr : ∀ i, 0 < r i) (k : ℕ)
    (hs : Summable (fun i ↦ (r i ^ (k + 1))⁻¹)) {x : ℝ} (hx : 0 ≤ x) :
    (∫ t : ℝ in Ioi 0, exp (-x * t) * t ^ k * exponentialMomentSum r 0 t) ≤
      ∑' i, (k.factorial : ℝ) / r i ^ (k + 1) := by
  rw [(integrableOn_and_integral_exp_mul_pow_mul_exponentialMomentSum hr k hs hx).2]
  apply Summable.tsum_le_tsum _ (summable_factorial_div_add_pow hr k hs hx)
    (by simpa only [zero_add] using summable_factorial_div_add_pow hr k hs (x := 0) le_rfl)
  intro i
  apply div_le_div_of_nonneg_left (Nat.cast_nonneg _) (pow_pos (hr i) _)
  exact pow_le_pow_left₀ (hr i).le (le_add_of_nonneg_left hx) _

/-- Zhang's inverse moment below one discharges all Laplace integrability
hypotheses. The stronger boundary exponent `a = 1` is allowed as well. -/
theorem laplace_exponentialMomentSum_of_inverse_moment
    {ι : Type*} [Countable ι] {r : ι → ℝ} {a : ℝ}
    (hr : ∀ i, 0 < r i) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hs : Summable (fun i ↦ r i ^ (-a))) (k : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    IntegrableOn (fun t : ℝ ↦ exp (-x * t) * t ^ k * exponentialMomentSum r 0 t)
        (Ioi 0) ∧
      (∫ t : ℝ in Ioi 0, exp (-x * t) * t ^ k * exponentialMomentSum r 0 t) =
        ∑' i, (k.factorial : ℝ) / (x + r i) ^ (k + 1) :=
  integrableOn_and_integral_exp_mul_pow_mul_exponentialMomentSum hr k
    (summable_inv_pow_of_inverse_moment hr ha ha1 hs k) hx

end Real
