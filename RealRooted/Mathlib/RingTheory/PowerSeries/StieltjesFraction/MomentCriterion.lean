/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import RealRooted.Mathlib.RingTheory.PowerSeries.StieltjesFraction.Tail
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import RealRooted.Mathlib.RingTheory.PowerSeries.StieltjesFraction.Moment
import RealRooted.Mathlib.RingTheory.PowerSeries.StieltjesFraction.InfiniteMoment
import RealRooted.Mathlib.RingTheory.PowerSeries.StieltjesFraction.FiniteMeasureFraction

/-!
# The formal Stieltjes moment criterion

A real sequence is the sequence of natural moments of a positive measure
on the nonnegative half-line exactly when its ordinary formal generating
series has a Stieltjes continued fraction with nonnegative data.

The reverse construction treats measures carried by finite sets and those
with no finite carrier separately. Zero measure, mass at the origin and
terminating fractions are included. No analytic growth or numerical
continued-fraction convergence assumption occurs.

See Sokal, "When does a hypergeometric function pFq belong to the Laguerre–Pólya
class LP+?", Proposition 7, p. 5.
-/

public section

open MeasureTheory

namespace PowerSeries

/-- Every genuine nonnegative all-moments measure has a nonnegative formal
Stieltjes fraction, with total mass as its outer scalar. -/
theorem exists_stieltjesTail_of_nonnegative_moments {mu : Measure ℝ}
    (hmom : ∀ k : ℕ, Integrable (fun x : ℝ => x ^ k) mu)
    (hpos : ∀ᵐ x ∂mu, 0 ≤ x) :
    ∃ a : ℕ → ℝ, (∀ k, 0 ≤ a k) ∧
      mk (fun k => ∫ x : ℝ, x ^ k ∂mu) = C (mu.real Set.univ) * stieltjesTail a 0 := by
  let : IsFiniteMeasure mu :=
    (integrable_const_iff_isFiniteMeasure (by norm_num : (1 : ℝ) ≠ 0)).mp
      (by simpa only [pow_zero] using hmom 0)
  by_cases hcarrier : ∃ S : Set ℝ, S.Finite ∧ mu Sᶜ = 0
  · obtain ⟨S, hS, hs⟩ := hcarrier
    exact exists_stieltjesTail_of_finite_carrier hpos S hS hs
  · have hfinite (S : Set ℝ) (hS : S.Finite) : mu Sᶜ ≠ 0 := by
      intro hs
      exact hcarrier ⟨S, hS, hs⟩
    obtain ⟨a, ha, hf⟩ := exists_pos_stieltjesTail_of_no_finite_carrier hmom hpos hfinite
    exact ⟨a, fun k => (ha k).le, hf⟩

/-- A real sequence is a genuine Stieltjes moment sequence if and only if its
formal generating series has a nonnegative Stieltjes fraction. -/
theorem exists_measure_moments_iff_stieltjesTail (m : ℕ → ℝ) :
    (∃ mu : Measure ℝ, IsFiniteMeasure mu ∧ (∀ᵐ x ∂mu, 0 ≤ x) ∧
      ∀ k : ℕ, Integrable (fun x : ℝ => x ^ k) mu ∧ (∫ x : ℝ, x ^ k ∂mu) = m k) ↔
    ∃ (c : ℝ) (a : ℕ → ℝ), 0 ≤ c ∧ (∀ k, 0 ≤ a k) ∧
      mk m = C c * stieltjesTail a 0 := by
  constructor
  · rintro ⟨mu, _, hpos, hmom⟩
    obtain ⟨a, ha, hf⟩ :=
      exists_stieltjesTail_of_nonnegative_moments (fun k => (hmom k).1) hpos
    have hseq : (fun k => ∫ x : ℝ, x ^ k ∂mu) = m := funext fun k => (hmom k).2
    exact ⟨mu.real Set.univ, a, measureReal_nonneg, ha, by simpa only [hseq] using hf⟩
  · rintro ⟨c, a, hc, ha, hf⟩
    simpa only [coeff_mk] using exists_measure_moments_of_eq_stieltjesTail ha hc hf

end PowerSeries
