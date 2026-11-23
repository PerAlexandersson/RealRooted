/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
import RealRooted.Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Integrable derivatives of beta weights

For nonnegative exponents, `t^a (1-t)^b` is continuous on `[0, 1]` and has an
integrable derivative on the open interval. Its endpoint value at `1` plus
the integral of the absolute derivative is at most two. Exponent zero is
handled separately; no differentiability at either endpoint is assumed.
-/

public section

open MeasureTheory

namespace Real

private noncomputable def betaDerivLeft (a b t : ℝ) : ℝ :=
  a * (t ^ (a - 1) * (1 - t) ^ b)

private noncomputable def betaDerivRight (a b t : ℝ) : ℝ :=
  b * (t ^ a * (1 - t) ^ (b - 1))

private theorem betaDerivLeft_nonneg {a b t : ℝ} (ha : 0 ≤ a)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) : 0 ≤ betaDerivLeft a b t := by
  exact mul_nonneg ha (mul_nonneg (rpow_nonneg ht.1 _) (rpow_nonneg (sub_nonneg.mpr ht.2) _))

private theorem betaDerivRight_nonneg {a b t : ℝ} (hb : 0 ≤ b)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) : 0 ≤ betaDerivRight a b t := by
  exact mul_nonneg hb (mul_nonneg (rpow_nonneg ht.1 _) (rpow_nonneg (sub_nonneg.mpr ht.2) _))

private theorem intervalIntegrable_betaDerivLeft {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    IntervalIntegrable (betaDerivLeft a b) volume 0 1 := by
  by_cases ha0 : a = 0
  · unfold betaDerivLeft
    simp only [ha0, zero_mul]
    exact intervalIntegrable_const
  · have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    have ha1 : -1 < a - 1 := by linarith
    exact (intervalIntegral.intervalIntegrable_rpow_mul_one_sub_rpow
      ha1 (by linarith : -1 < b)).const_mul a

private theorem intervalIntegrable_betaDerivRight {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    IntervalIntegrable (betaDerivRight a b) volume 0 1 := by
  by_cases hb0 : b = 0
  · unfold betaDerivRight
    simp only [hb0, zero_mul]
    exact intervalIntegrable_const
  · have hbpos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
    have hb1 : -1 < b - 1 := by linarith
    exact (intervalIntegral.intervalIntegrable_rpow_mul_one_sub_rpow
      (by linarith : -1 < a) hb1).const_mul b

private theorem hasDerivAt_betaWeight {a b t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (fun x : ℝ ↦ x ^ a * (1 - x) ^ b)
      (betaDerivLeft a b t - betaDerivRight a b t) t := by
  have hleft : HasDerivAt (fun x : ℝ ↦ x ^ a) (a * t ^ (a - 1)) t :=
    hasDerivAt_rpow_const (Or.inl ht.1.ne')
  have hright : HasDerivAt (fun x : ℝ ↦ (1 - x) ^ b)
      (-(b * (1 - t) ^ (b - 1))) t := by
    have hnonzero : 1 - t ≠ 0 := (sub_pos.mpr ht.2).ne'
    simpa only [Function.comp_def, zero_sub, mul_neg, mul_one] using
      (hasDerivAt_rpow_const (p := b) (Or.inl hnonzero)).comp t
        ((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t))
  convert hleft.mul hright using 1
  dsimp [betaDerivLeft, betaDerivRight]
  ring

private theorem integral_betaDerivLeft_le_one {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (∫ t in (0 : ℝ)..1, betaDerivLeft a b t) ≤ 1 := by
  by_cases ha0 : a = 0
  · simp [betaDerivLeft, ha0]
  have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
  have hdom : IntervalIntegrable (fun t : ℝ ↦ a * t ^ (a - 1)) volume 0 1 := by
    have h := (intervalIntegral.intervalIntegrable_rpow_mul_one_sub_rpow
      (a := a - 1) (b := 0) (by linarith) (by norm_num)).const_mul a
    simpa only [rpow_zero, mul_one] using h
  have hint : (∫ t in (0 : ℝ)..1, a * t ^ (a - 1)) = 1 := by
    rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by linarith : -1 < a - 1)),
      sub_add_cancel, one_rpow, zero_rpow hapos.ne', sub_zero]
    field_simp [hapos.ne']
  calc
    _ ≤ ∫ t in (0 : ℝ)..1, a * t ^ (a - 1) := by
      apply intervalIntegral.integral_mono_on zero_le_one
        (intervalIntegrable_betaDerivLeft ha hb) hdom
      intro t ht
      have hpow : (1 - t) ^ b ≤ 1 :=
        rpow_le_one (sub_nonneg.mpr ht.2) (by linarith [ht.1]) hb
      calc
        betaDerivLeft a b t = (a * t ^ (a - 1)) * (1 - t) ^ b := by
          dsimp [betaDerivLeft]
          ring
        _ ≤ (a * t ^ (a - 1)) * 1 :=
          mul_le_mul_of_nonneg_left hpow (mul_nonneg ha (rpow_nonneg ht.1 _))
        _ = a * t ^ (a - 1) := mul_one _
    _ = 1 := hint

private theorem integral_betaDerivRight_le_one {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (∫ t in (0 : ℝ)..1, betaDerivRight a b t) ≤ 1 := by
  calc
    _ = ∫ t in (0 : ℝ)..1, betaDerivLeft b a (1 - t) := by
      apply intervalIntegral.integral_congr
      intro t _
      dsimp [betaDerivLeft, betaDerivRight]
      rw [show 1 - (1 - t) = t by ring]
      ring
    _ = ∫ t in (0 : ℝ)..1, betaDerivLeft b a t := by
      simpa only [sub_self, sub_zero] using
        intervalIntegral.integral_comp_sub_left (betaDerivLeft b a)
          (a := (0 : ℝ)) (b := 1) 1
    _ ≤ 1 := integral_betaDerivLeft_le_one hb ha

private theorem beta_endpoint_add_integral_abs_le_two {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |(1 : ℝ) ^ a * (1 - 1) ^ b| +
      (∫ t in (0 : ℝ)..1, |betaDerivLeft a b t - betaDerivRight a b t|) ≤ 2 := by
  have hA := intervalIntegrable_betaDerivLeft ha hb
  have hB := intervalIntegrable_betaDerivRight ha hb
  have hAI := integral_betaDerivLeft_le_one ha hb
  have hBI := integral_betaDerivRight_le_one ha hb
  by_cases hb0 : b = 0
  · have heq : (∫ t in (0 : ℝ)..1, |betaDerivLeft a b t - betaDerivRight a b t|) =
        ∫ t in (0 : ℝ)..1, betaDerivLeft a b t := by
      apply intervalIntegral.integral_congr_Ioo_of_le zero_le_one
      intro t ht
      change |betaDerivLeft a b t - betaDerivRight a b t| = betaDerivLeft a b t
      rw [show betaDerivRight a b t = 0 by simp [betaDerivRight, hb0], sub_zero,
        abs_of_nonneg (betaDerivLeft_nonneg ha ⟨ht.1.le, ht.2.le⟩)]
    rw [heq]
    simp only [hb0, one_rpow, rpow_zero, mul_one, abs_one]
    rw [hb0] at hAI
    linarith
  · have hnorm : (∫ t in (0 : ℝ)..1, |betaDerivLeft a b t - betaDerivRight a b t|) ≤
        (∫ t in (0 : ℝ)..1, betaDerivLeft a b t) +
          ∫ t in (0 : ℝ)..1, betaDerivRight a b t := by
      rw [← intervalIntegral.integral_add hA hB]
      apply intervalIntegral.integral_mono_on zero_le_one (hA.sub hB).abs (hA.add hB)
      intro t ht
      calc
        _ ≤ |betaDerivLeft a b t| + |betaDerivRight a b t| := abs_sub _ _
        _ = _ := by rw [abs_of_nonneg (betaDerivLeft_nonneg ha ht),
          abs_of_nonneg (betaDerivRight_nonneg hb ht)]
    simp only [one_rpow, sub_self, zero_rpow hb0, mul_zero, abs_zero, zero_add]
    linarith

/-- A beta weight with nonnegative exponents has an integrable interior derivative whose
absolute integral plus the right endpoint value is at most two. Zero exponents are included;
no endpoint differentiability or continuous-derivative assumption is imposed. -/
theorem exists_integrable_deriv_rpow_mul_one_sub_rpow {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ∃ g : ℝ → ℝ, IntervalIntegrable g volume 0 1 ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) 1,
        HasDerivAt (fun x : ℝ ↦ x ^ a * (1 - x) ^ b) (g t) t) ∧
      |(1 : ℝ) ^ a * (1 - 1) ^ b| + (∫ t in (0 : ℝ)..1, |g t|) ≤ 2 := by
  exact ⟨fun t ↦ betaDerivLeft a b t - betaDerivRight a b t,
    (intervalIntegrable_betaDerivLeft ha hb).sub (intervalIntegrable_betaDerivRight ha hb),
    fun _ ht ↦ hasDerivAt_betaWeight ht, beta_endpoint_add_integral_abs_le_two ha hb⟩

end Real
