/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic

import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Positive atomic measures for power sums

A summable nonnegative sequence supplies a finite positive measure with compact
support. Adding a mass at zero gives the measure occurring in logarithmic
derivative moment representations of Type-I entire functions.
-/

public section

open Filter Topology MeasureTheory

namespace MeasureTheory

/-- Positive powers of a summable real sequence remain summable. -/
private theorem summable_mul_self_pow {a : ℕ → ℝ} (ha : Summable a) (k : ℕ) :
    Summable (fun i => a i * a i ^ k) :=
  ha.norm.mul_tendsto_const (ha.tendsto_cofinite_zero.pow k)

/-- The discrete measure with mass `a i` at the nonnegative point `a i`
has finite moments whenever the sequence is summable. -/
theorem integrable_pow_sum_smul_dirac {a : ℕ → ℝ}
    (ha : ∀ i, 0 ≤ a i) (hs : Summable a) (k : ℕ) :
    Integrable (fun x : ℝ => x ^ k)
      (Measure.sum (fun i => ENNReal.ofReal (a i) • Measure.dirac (a i))) := by
  apply integrable_sum_dirac (fun _ => ENNReal.ofReal_ne_top)
  simpa only [ENNReal.toReal_ofReal (ha _), Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg (ha _) _)] using summable_mul_self_pow hs k

/-- The discrete measure weighted by a summable nonnegative sequence is finite. -/
theorem isFiniteMeasure_sum_smul_dirac {a : ℕ → ℝ}
    (ha : ∀ i, 0 ≤ a i) (hs : Summable a) :
    IsFiniteMeasure (Measure.sum (fun i => ENNReal.ofReal (a i) • Measure.dirac (a i))) := by
  exact (integrable_const_iff_isFiniteMeasure (by norm_num : (1 : ℝ) ≠ 0)).mp
    (by simpa only [pow_zero] using integrable_pow_sum_smul_dirac ha hs 0)

/-- The moments of the weighted atomic measure are the next power sums. -/
theorem integral_pow_sum_smul_dirac {a : ℕ → ℝ} (ha : ∀ i, 0 ≤ a i) (k : ℕ) :
    (∫ x : ℝ, x ^ k ∂Measure.sum
      (fun i => ENNReal.ofReal (a i) • Measure.dirac (a i))) =
      ∑' i, a i ^ (k + 1) := by
  rw [integral_sum_dirac (fun _ => ENNReal.ofReal_ne_top)]
  apply tsum_congr
  intro i
  simp only [ENNReal.toReal_ofReal (ha i), smul_eq_mul, pow_succ]
  ring

/-- All atoms lie in the compact interval from zero to the sum of their masses. -/
theorem sum_smul_dirac_compl_Icc_eq_zero {a : ℕ → ℝ}
    (ha : ∀ i, 0 ≤ a i) (hs : Summable a) :
    (Measure.sum (fun i => ENNReal.ofReal (a i) • Measure.dirac (a i)))
      (Set.Icc 0 (∑' i, a i))ᶜ = 0 := by
  rw [Measure.sum_apply _ measurableSet_Icc.compl]
  apply tsum_eq_zero_iff.mpr
  intro i
  have hi : a i ∈ Set.Icc 0 (∑' j, a j) :=
    ⟨ha i, hs.le_tsum i (fun j _ => ha j)⟩
  simp [Measure.dirac_apply', measurableSet_Icc, hi]


/-- Nonnegative summable atoms, with an optional mass at zero, give a compactly
supported positive measure with all moments equal to the corresponding power sums. -/
theorem exists_measure_power_sum_moments {a : ℕ → ℝ} {gamma : ℝ}
    (ha : ∀ i, 0 ≤ a i) (hs : Summable a) (hg : 0 ≤ gamma) :
    ∃ mu : Measure ℝ,
      mu = ENNReal.ofReal gamma • Measure.dirac 0 +
        Measure.sum (fun i => ENNReal.ofReal (a i) • Measure.dirac (a i)) ∧
      IsFiniteMeasure mu ∧ mu (Set.Icc 0 (∑' i, a i))ᶜ = 0 ∧
      ∀ k : ℕ, Integrable (fun x : ℝ => x ^ k) mu ∧
        (∫ x : ℝ, x ^ k ∂mu) = gamma * 0 ^ k + ∑' i, a i ^ (k + 1) := by
  let nu := Measure.sum (fun i => ENNReal.ofReal (a i) • Measure.dirac (a i))
  let mu : Measure ℝ := ENNReal.ofReal gamma • Measure.dirac 0 + nu
  have hfirst (k : ℕ) :
      Integrable (fun x : ℝ => x ^ k) (ENNReal.ofReal gamma • Measure.dirac 0) :=
    (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
  have hsecond (k : ℕ) : Integrable (fun x : ℝ => x ^ k) nu :=
    integrable_pow_sum_smul_dirac ha hs k
  have hint (k : ℕ) : Integrable (fun x : ℝ => x ^ k) mu :=
    (hfirst k).add_measure (hsecond k)
  have hfinite : IsFiniteMeasure mu :=
    (integrable_const_iff_isFiniteMeasure (by norm_num : (1 : ℝ) ≠ 0)).mp
      (by simpa only [pow_zero] using hint 0)
  refine ⟨mu, rfl, hfinite, ?_, fun k => ⟨hint k, ?_⟩⟩
  · have hzero : (0 : ℝ) ∈ Set.Icc 0 (∑' i, a i) := ⟨le_rfl, tsum_nonneg ha⟩
    dsimp only [mu, nu]
    rw [add_apply, sum_smul_dirac_compl_Icc_eq_zero ha hs, add_zero]
    simp [Measure.dirac_apply', measurableSet_Icc, hzero]
  · change (∫ x : ℝ, x ^ k ∂(ENNReal.ofReal gamma • Measure.dirac 0 + nu)) = _
    rw [integral_add_measure (hfirst k) (hsecond k), integral_smul_measure, integral_dirac,
      ENNReal.toReal_ofReal hg]
    rw [show (∫ x : ℝ, x ^ k ∂nu) = ∑' i, a i ^ (k + 1) from
      integral_pow_sum_smul_dirac ha k]
    rfl

end MeasureTheory
