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
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import TauCeti.MeasureTheory.Integral.Exp.Decay
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import RealRooted.Mathlib.Analysis.SpecialFunctions.Exp.ExponentialSumBounds

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
  have hsum := hs.mul_left (k.factorial : ℝ)
  apply Summable.of_nonneg_of_le
    (fun i ↦ div_nonneg (Nat.cast_nonneg _) (pow_nonneg (add_nonneg hx (hr i).le) _))
    ?_ hsum
  intro i
  rw [← div_eq_mul_inv]
  apply div_le_div_of_nonneg_left (Nat.cast_nonneg _) (pow_pos (hr i) _)
  exact pow_le_pow_left₀ (hr i).le (le_add_of_nonneg_left hx) _

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
  have hpos (i : ι) : 0 < x + r i := add_pos_of_nonneg_of_pos hx (hr i)
  have hint (i : ι) : IntegrableOn
      (fun t : ℝ ↦ t ^ k * exp (-((x + r i) * t))) (Ioi 0) :=
    TauCeti.integrableOn_pow_mul_exp_neg_mul_Ioi k (hpos i)
  have heval (i : ι) :
      (∫ t : ℝ in Ioi 0, t ^ k * exp (-((x + r i) * t))) =
        (k.factorial : ℝ) / (x + r i) ^ (k + 1) :=
    TauCeti.integral_pow_mul_exp_neg_mul_Ioi k (hpos i)
  have hnorm (i : ι) :
      (∫ t : ℝ in Ioi 0, ‖t ^ k * exp (-((x + r i) * t))‖) =
        (k.factorial : ℝ) / (x + r i) ^ (k + 1) := by
    rw [← heval i]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 0 < t)
    exact Real.norm_of_nonneg (mul_nonneg (pow_nonneg ht.le _) (exp_nonneg _))
  have hsx := summable_factorial_div_add_pow hr k hs hx
  have hnormsum : Summable
      (fun i ↦ ∫ t : ℝ in Ioi 0, ‖t ^ k * exp (-((x + r i) * t))‖) := by
    simpa only [hnorm] using hsx
  have hfun : (fun t : ℝ ↦ ∑' i, t ^ k * exp (-((x + r i) * t))) =
      (fun t : ℝ ↦ exp (-x * t) * t ^ k * exponentialMomentSum r 0 t) := by
    funext t
    calc (∑' i, t ^ k * exp (-((x + r i) * t)))
        = ∑' i, (exp (-x * t) * t ^ k) * exp (-r i * t) := by
          apply tsum_congr
          intro i
          simp only [add_mul, neg_add, exp_add, neg_mul]
          ring
      _ = _ := by
        rw [tsum_mul_left]
        simp only [exponentialMomentSum, pow_zero, one_mul]
  have heq :
      (∫ t : ℝ in Ioi 0, exp (-x * t) * t ^ k * exponentialMomentSum r 0 t) =
        ∑' i, (k.factorial : ℝ) / (x + r i) ^ (k + 1) := by
    rw [← hfun, ← integral_tsum_of_summable_integral_norm hint hnormsum]
    simp only [heval]
  refine ⟨?_, heq⟩
  cases isEmpty_or_nonempty ι with
  | inl h =>
      have := h
      simp only [exponentialMomentSum, tsum_empty, mul_zero]
      exact integrableOn_zero
  | inr h =>
      have := h
      apply Integrable.of_integral_ne_zero
      rw [heq]
      exact (hsx.tsum_pos
        (fun i ↦ div_nonneg (Nat.cast_nonneg _) (pow_nonneg (hpos i).le _))
        (Classical.arbitrary ι)
        (div_pos (by exact_mod_cast Nat.factorial_pos k) (pow_pos (hpos _) _))).ne'

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
