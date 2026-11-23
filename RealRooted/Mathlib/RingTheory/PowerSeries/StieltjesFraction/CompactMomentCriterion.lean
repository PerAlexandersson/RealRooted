/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import RealRooted.Mathlib.RingTheory.PowerSeries.StieltjesFraction.ChainParameters
import RealRooted.Mathlib.MeasureTheory.Measure.BoundedChainSupport
import RealRooted.Mathlib.RingTheory.PowerSeries.StieltjesFraction.ChainAeration
import RealRooted.Mathlib.RingTheory.PowerSeries.StieltjesFraction.CompactMomentsChain
import RealRooted.Mathlib.RingTheory.PowerSeries.StieltjesFraction.Moment

/-!
# Wall's compact Stieltjes moment criterion

For `L ≥ 0`, genuine moments on `[0,L]` are exactly the formal fractions with
nonnegative outer mass and numerators `L*(1-g_n)*g_(n+1)`, where all parameters
lie in `[0,1]`. One may either impose `g 0 = 0` or leave the initial parameter
arbitrary in the same interval.

See Sokal, arXiv:1903.12455v2, and Sokal-Walrad, arXiv:2404.12131v1, Theorem 1.
Zero mass, a zero endpoint, and terminating fractions are included.
-/

public section

open MeasureTheory

namespace PowerSeries

/-- Every bounded chain fraction has an actual compact representing measure,
without a normalization on its initial parameter. -/
theorem exists_measure_moments_Icc_of_chain {m : ℕ → ℝ} {L mass : ℝ}
    (hL : 0 ≤ L) (hmass : 0 ≤ mass) {g : ℕ → ℝ}
    (hg : ∀ n, g n ∈ Set.Icc 0 1)
    (hf : mk m = C mass * stieltjesTail (chainStieltjesNumerators L g) 0) :
    ∃ mu : Measure ℝ, (∀ᵐ x ∂mu, x ∈ Set.Icc 0 L) ∧
      ∀ n : ℕ, Integrable (fun x : ℝ => x ^ n) mu ∧
        (∫ x : ℝ, x ^ n ∂mu) = m n := by
  obtain ⟨mu, _, hpos, hmom⟩ := exists_measure_moments_of_eq_stieltjesTail
    (chainStieltjesNumerators_nonneg hL hg) hmass hf
  have hcoeff (n : ℕ) : (∫ x : ℝ, x ^ n ∂mu) =
      mass * coeff n (stieltjesTail (chainStieltjesNumerators L g) 0) := by
    rw [(hmom n).2, hf, coeff_C_mul]
  refine ⟨mu, ae_mem_Icc_of_bounded_chain_moments hL hmass hg hpos
    (fun n => (hmom n).1) hcoeff, fun n => ⟨(hmom n).1, ?_⟩⟩
  simpa only [coeff_mk] using (hmom n).2

/-- Genuine compact nonnegative moments are exactly the normalized Wall chain fractions. -/
theorem exists_measure_moments_Icc_iff_chain (m : ℕ → ℝ) {L : ℝ} (hL : 0 ≤ L) :
    (∃ mu : Measure ℝ, (∀ᵐ x ∂mu, x ∈ Set.Icc 0 L) ∧
      ∀ n : ℕ, Integrable (fun x : ℝ => x ^ n) mu ∧
        (∫ x : ℝ, x ^ n ∂mu) = m n) ↔
    ∃ (mass : ℝ) (g : ℕ → ℝ), 0 ≤ mass ∧ g 0 = 0 ∧
      (∀ n, g n ∈ Set.Icc 0 1) ∧
      mk m = C mass * stieltjesTail (chainStieltjesNumerators L g) 0 := by
  constructor
  · rintro ⟨mu, hs, hmom⟩
    obtain ⟨g, hg0, hg, hf⟩ := exists_chainStieltjes_of_moments_Icc hL hs
      (fun n => (hmom n).1)
    have heq : (fun n => ∫ x : ℝ, x ^ n ∂mu) = m := funext fun n => (hmom n).2
    exact ⟨mu.real Set.univ, g, measureReal_nonneg, hg0, hg, by simpa only [heq] using hf⟩
  · rintro ⟨mass, g, hmass, _, hg, hf⟩
    exact exists_measure_moments_Icc_of_chain hL hmass hg hf

/-- The compact moment criterion also allows an arbitrary initial chain
parameter in `[0,1]`. -/
theorem exists_measure_moments_Icc_iff_bounded_chain (m : ℕ → ℝ) {L : ℝ} (hL : 0 ≤ L) :
    (∃ mu : Measure ℝ, (∀ᵐ x ∂mu, x ∈ Set.Icc 0 L) ∧
      ∀ n : ℕ, Integrable (fun x : ℝ => x ^ n) mu ∧
        (∫ x : ℝ, x ^ n ∂mu) = m n) ↔
    ∃ (mass : ℝ) (g : ℕ → ℝ), 0 ≤ mass ∧
      (∀ n, g n ∈ Set.Icc 0 1) ∧
      mk m = C mass * stieltjesTail (chainStieltjesNumerators L g) 0 := by
  constructor
  · intro h
    obtain ⟨mass, g, hmass, _, hg, hf⟩ := (exists_measure_moments_Icc_iff_chain m hL).mp h
    exact ⟨mass, g, hmass, hg, hf⟩
  · rintro ⟨mass, g, hmass, hg, hf⟩
    exact exists_measure_moments_Icc_of_chain hL hmass hg hf

end PowerSeries
