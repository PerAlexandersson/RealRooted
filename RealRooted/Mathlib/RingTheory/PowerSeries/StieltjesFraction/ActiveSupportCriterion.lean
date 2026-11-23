/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import RealRooted.Mathlib.RingTheory.PowerSeries.StieltjesFraction.LowerSupportParameters
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import RealRooted.Mathlib.RingTheory.PowerSeries.StieltjesFraction.LowerSupportCriterion
import RealRooted.Mathlib.RingTheory.PowerSeries.StieltjesFraction.ActivePrefix

/-!
# Lower support criteria on the active numerator prefix

For a fixed normalized Stieltjes fraction, agreement with the lower-support
parameters is required only until its first zero, including that zero. Later
numerators may be arbitrary. This avoids imposing a nonstandard existential
tail parametrization on the standard all-zero inactive tail.
-/

public section

open MeasureTheory

namespace PowerSeries

/-- The lower-support criterion for a fixed normalized fraction depends only
on the active prefix of its numerator sequence. -/
theorem exists_moments_Ici_iff_active_parameters (a : ℕ → ℝ) {c : ℝ} (hc : 0 ≤ c) :
    (∃ mu : Measure ℝ, (∀ᵐ x ∂mu, c ≤ x) ∧
      ∀ n : ℕ, Integrable (fun x : ℝ => x ^ n) mu ∧
        (∫ x : ℝ, x ^ n ∂mu) = coeff n (stieltjesTail a 0)) ↔
    ∃ u v : ℕ → ℝ, u 0 = 0 ∧ (∀ k, 0 ≤ u k) ∧ (∀ k, 0 ≤ v k) ∧
      ∀ n, (∀ k < n, a k ≠ 0) → a n = shiftedStieltjesNumerators c u v n := by
  have hmk : mk (fun n => coeff n (stieltjesTail a 0)) = stieltjesTail a 0 := by
    ext n
    simp
  rw [exists_measure_moments_Ici_iff_parameters _ hc, hmk]
  constructor
  · rintro ⟨mass, u, v, _, hu0, hu, hv, hf⟩
    have hmass : mass = 1 := by
      have h := congrArg constantCoeff hf
      simpa using h.symm
    have heq : stieltjesTail a 0 = stieltjesTail (shiftedStieltjesNumerators c u v) 0 := by
      simpa only [hmass, map_one, one_mul] using hf
    exact ⟨u, v, hu0, hu, hv, stieltjesTail_eq_iff_active_prefix.mp heq⟩
  · rintro ⟨u, v, hu0, hu, hv, hprefix⟩
    refine ⟨1, u, v, zero_le_one, hu0, hu, hv, ?_⟩
    simpa only [map_one, one_mul] using stieltjesTail_eq_of_active_prefix hprefix

/-- The odd-numerator lower bound applies to active coefficients of any
normalized representation, not to its arbitrary inactive zero tail. -/
theorem le_active_stieltjesNumerator {a : ℕ → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hmom : ∃ mu : Measure ℝ, (∀ᵐ x ∂mu, c ≤ x) ∧
      ∀ n : ℕ, Integrable (fun x : ℝ => x ^ n) mu ∧
        (∫ x : ℝ, x ^ n ∂mu) = coeff n (stieltjesTail a 0))
    (j : ℕ) (hactive : ∀ k < 2 * j, a k ≠ 0) : c ≤ a (2 * j) := by
  obtain ⟨u, v, _, hu, hv, hprefix⟩ :=
    (exists_moments_Ici_iff_active_parameters a hc).mp hmom
  rw [hprefix (2 * j) hactive]
  exact le_shiftedStieltjesNumerators_even hc hu hv j

end PowerSeries
