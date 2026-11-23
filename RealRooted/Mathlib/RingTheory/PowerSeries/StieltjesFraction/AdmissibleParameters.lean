/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import RealRooted.Mathlib.RingTheory.PowerSeries.StieltjesFraction.LowerSupportParameters

import RealRooted.Mathlib.RingTheory.PowerSeries.StieltjesFraction.ActiveSupportCriterion
import RealRooted.Mathlib.RingTheory.PowerSeries.StieltjesFraction.LowerParameters

/-!
# Admissible initial parameters on the active prefix

The fixed fraction is matched only through its first terminating numerator.
For a nonterminating fraction this is full coefficient equality. This is the
termination-aware interpretation of the parameter set in Sokal-Walrad,
arXiv:2404.12131v1, Remark 2. It is nonempty under the support hypothesis,
downward closed within the nonnegative half-line, and bounded for a positive shift.
-/

public section

namespace PowerSeries

/-- Initial parameters that reproduce the active numerator prefix. -/
@[expose] def admissibleStieltjesParameters (c : ℝ) (a : ℕ → ℝ) : Set ℝ :=
  {r | ∃ u v : ℕ → ℝ, u 0 = r ∧ (∀ k, 0 ≤ u k) ∧ (∀ k, 0 ≤ v k) ∧
    ∀ n, (∀ k < n, a k ≠ 0) → a n = shiftedStieltjesNumerators c u v n}

/-- Every admissible initial parameter is nonnegative. -/
theorem nonneg_of_mem_admissibleStieltjesParameters {c r : ℝ} {a : ℕ → ℝ}
    (hr : r ∈ admissibleStieltjesParameters c a) : 0 ≤ r := by
  obtain ⟨u, v, hu0, hu, _, _⟩ := hr
  simpa only [hu0] using hu 0

/-- Every smaller nonnegative initial parameter is also admissible. -/
theorem mem_admissibleStieltjesParameters_of_le {c r s : ℝ} (hc : 0 ≤ c)
    {a : ℕ → ℝ} (hs : s ∈ admissibleStieltjesParameters c a)
    (hr : 0 ≤ r) (hrs : r ≤ s) : r ∈ admissibleStieltjesParameters c a := by
  obtain ⟨u, v, hu0, hu, hv, hp⟩ := hs
  obtain ⟨u', v', hu0', hu', hv', heq⟩ :=
    exists_lower_stieltjesParameters hc hu hv hr (by simpa only [hu0] using hrs)
  refine ⟨u', v', hu0', fun k => (hu' k).1, fun k => (hv k).trans (hv' k), ?_⟩
  intro n hn
  rw [heq]
  exact hp n hn

/-- The admissible parameters form an order interval, possibly empty. -/
theorem ordConnected_admissibleStieltjesParameters {c : ℝ} (hc : 0 ≤ c)
    (a : ℕ → ℝ) : Set.OrdConnected (admissibleStieltjesParameters c a) := by
  refine ⟨fun x hx y hy z hz => ?_⟩
  exact mem_admissibleStieltjesParameters_of_le hc hy
    ((nonneg_of_mem_admissibleStieltjesParameters hx).trans hz.1) hz.2

/-- The first numerator bounds every admissible initial parameter when the shift is positive. -/
theorem mem_admissibleStieltjesParameters_le {c r : ℝ} (hc : 0 < c)
    {a : ℕ → ℝ} (hr : r ∈ admissibleStieltjesParameters c a) :
    r ≤ a 0 / c - 1 := by
  obtain ⟨u, v, hu0, _, hv, hp⟩ := hr
  have h0 := hp 0 (by simp)
  have heq : a 0 = c * (1 + r) + v 0 := by
    simpa [shiftedStieltjesNumerators, hu0] using h0
  have hv0 := hv 0
  have hquot : r + 1 ≤ a 0 / c := (le_div_iff₀ hc).mpr (by nlinarith)
  linarith

/-- An actual lower-support measure makes the corrected parameter set nonempty. -/
theorem zero_mem_admissibleStieltjesParameters {c : ℝ} (hc : 0 ≤ c)
    {a : ℕ → ℝ}
    (hmom : ∃ mu : MeasureTheory.Measure ℝ, (∀ᵐ x ∂mu, c ≤ x) ∧
      ∀ n : ℕ, MeasureTheory.Integrable (fun x : ℝ => x ^ n) mu ∧
        (∫ x : ℝ, x ^ n ∂mu) = coeff n (stieltjesTail a 0)) :
    0 ∈ admissibleStieltjesParameters c a :=
  (exists_moments_Ici_iff_active_parameters a hc).mp hmom

end PowerSeries
