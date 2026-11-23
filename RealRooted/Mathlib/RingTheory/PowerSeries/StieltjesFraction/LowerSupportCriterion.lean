/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import RealRooted.Mathlib.RingTheory.PowerSeries.StieltjesFraction.LowerSupportParameters
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import RealRooted.Mathlib.RingTheory.PowerSeries.StieltjesFraction.LowerSupportConstruction
import RealRooted.Mathlib.MeasureTheory.Measure.MomentTranslation
import RealRooted.Mathlib.RingTheory.PowerSeries.StieltjesFraction.MomentCriterion
import RealRooted.Mathlib.RingTheory.PowerSeries.BinomialTransform.Inverse

/-!
# The Stieltjes fraction criterion for a prescribed lower support bound

For `c ≥ 0`, a real moment sequence has a positive representing measure on
`[c, ∞)` exactly when its formal Stieltjes fraction has the lower-support
parameters of Sokal-Walrad, arXiv:2404.12131v1, Theorem 2(a)-(b).

The two parameter sequences encode `u k = g_(2k)` and `v k = g_(2k+1)`.
Their initial condition is `u 0 = 0`. Zero mass, shift zero, and terminating
fractions are included. The numerator tail is existential and need not obey
the standard convention after its first zero. No numerical continued-fraction
convergence or determinacy assumption is imposed.
-/

public section

open MeasureTheory

namespace PowerSeries

/-- The zeroth integrable moment already supplies finite mass. -/
private theorem nonnegative_moments_iff (m : ℕ → ℝ) :
    (∃ mu : Measure ℝ, (∀ᵐ x ∂mu, 0 ≤ x) ∧
      ∀ n : ℕ, Integrable (fun x : ℝ => x ^ n) mu ∧
        (∫ x : ℝ, x ^ n ∂mu) = m n) ↔
    ∃ (a : ℝ) (b : ℕ → ℝ), 0 ≤ a ∧ (∀ k, 0 ≤ b k) ∧
      mk m = C a * stieltjesTail b 0 := by
  rw [← exists_measure_moments_iff_stieltjesTail]
  constructor
  · rintro ⟨mu, hpos, hmom⟩
    have hfin : IsFiniteMeasure mu :=
      (integrable_const_iff_isFiniteMeasure (one_ne_zero : (1 : ℝ) ≠ 0)).mp
        (by simpa only [pow_zero] using (hmom 0).1)
    exact ⟨mu, hfin, hpos, hmom⟩
  · rintro ⟨mu, _, hpos, hmom⟩
    exact ⟨mu, hpos, hmom⟩

/-- A lower support bound is equivalent to a nonnegative Stieltjes fraction
after inverse binomial translation. -/
theorem exists_measure_moments_Ici_iff_binomial (m : ℕ → ℝ) (c : ℝ) :
    (∃ mu : Measure ℝ, (∀ᵐ x ∂mu, c ≤ x) ∧
      ∀ n : ℕ, Integrable (fun x : ℝ => x ^ n) mu ∧
        (∫ x : ℝ, x ^ n ∂mu) = m n) ↔
    ∃ (a : ℝ) (b : ℕ → ℝ), 0 ≤ a ∧ (∀ k, 0 ≤ b k) ∧
      binomialTransform (-c) (mk m) = C a * stieltjesTail b 0 := by
  rw [MeasureTheory.exists_measure_moments_Ici_iff, nonnegative_moments_iff,
    binomialTransform_mk]

/-- A positive measure with prescribed lower support exists exactly when the
formal fraction admits nonnegative lower-support parameters. -/
theorem exists_measure_moments_Ici_iff_parameters (m : ℕ → ℝ) {c : ℝ} (hc : 0 ≤ c) :
    (∃ mu : Measure ℝ, (∀ᵐ x ∂mu, c ≤ x) ∧
      ∀ n : ℕ, Integrable (fun x : ℝ => x ^ n) mu ∧
        (∫ x : ℝ, x ^ n ∂mu) = m n) ↔
    ∃ (a : ℝ) (u v : ℕ → ℝ), 0 ≤ a ∧ u 0 = 0 ∧
      (∀ k, 0 ≤ u k) ∧ (∀ k, 0 ≤ v k) ∧
      mk m = C a * stieltjesTail (shiftedStieltjesNumerators c u v) 0 := by
  rw [exists_measure_moments_Ici_iff_binomial]
  constructor
  · rintro ⟨a, b, ha, hb, hf⟩
    obtain ⟨u, v, hu0, hu, hv, htail⟩ :=
      exists_parameters_binomialTransform_stieltjesTail hc hb
    refine ⟨a, u, v, ha, hu0, hu, hv, ?_⟩
    have h := congrArg (binomialTransform c) hf
    rw [binomialTransform_binomialTransform, add_neg_cancel, binomialTransform_zero,
      binomialTransform_C_mul, htail] at h
    exact h
  · rintro ⟨a, u, v, ha, hu0, hu, hv, hf⟩
    refine ⟨a, stieltjesNumeratorsBeforeShift c u v, ha,
      stieltjesNumeratorsBeforeShift_nonneg hc hu hv, ?_⟩
    have h := congrArg (binomialTransform (-c)) hf
    rw [← binomialTransform_beforeShift hu hu0, ← binomialTransform_C_mul,
      binomialTransform_neg_cancel] at h
    exact h

end PowerSeries
