/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import RealRooted.Mathlib.NumberTheory.LSeries.RiemannXi.Theta
public import RealRooted.Mathlib.RingTheory.PowerSeries.StieltjesFraction.ChainParameters
import RealRooted.Mathlib.RingTheory.PowerSeries.StieltjesFraction.CompactMomentsChain
import RealRooted.Mathlib.RingTheory.PowerSeries.StieltjesFraction.ChainAeration
import RealRooted.Mathlib.RingTheory.PowerSeries.StieltjesFraction.Moment
import RealRooted.RiemannHypothesis.MomentMeasure
import RealRooted.RiemannHypothesis.MomentCriterion

/-!
# Compact chain fractions for xi logarithmic derivatives under RH

Wall's compact moment criterion applies to the genuine compact logarithmic
moment measures of every derivative of the square-variable xi function.
The signed Taylor coefficients are identified as complex numbers, not merely
after taking real parts. At derivative order zero, this is equivalent to RH.

These are consequences of the moment criterion and Wall's theorem; the generic
chain theorem itself is unconditional.
-/

public section

open Complex MeasureTheory PowerSeries

namespace RealRooted

/-- Under RH, every xi derivative has bounded chain parameters representing
the actual signed complex coefficients of its logarithmic derivative. -/
theorem exists_logDeriv_riemannXiTheta_chain (hRH : RiemannHypothesis) (s : ℕ) :
    ∃ (L mass : ℝ) (g : ℕ → ℝ), 0 ≤ L ∧ 0 ≤ mass ∧ g 0 = 0 ∧
      (∀ n, g n ∈ Set.Icc 0 1) ∧
      ∀ n : ℕ, (-1 : ℂ) ^ n * iteratedDeriv n (logDeriv (iteratedDeriv s riemannXiTheta)) 0 /
          n.factorial =
        ((mass * coeff n (stieltjesTail (chainStieltjesNumerators L g) 0) : ℝ) : ℂ) := by
  obtain ⟨_, a, mu, _, ha, _, _, _, hsupport, hmom⟩ :=
    exists_logDeriv_riemannXiTheta_moment_measure hRH s
  have hL : 0 ≤ ∑' i, a i := tsum_nonneg ha
  obtain ⟨g, hg0, hg, hf⟩ := exists_chainStieltjes_of_moments_Icc hL
    (ae_iff.mpr hsupport) (fun n => (hmom n).1)
  refine ⟨∑' i, a i, mu.real Set.univ, g, hL, measureReal_nonneg, hg0, hg, fun n => ?_⟩
  apply (hmom n).2.trans
  apply congrArg (fun x : ℝ => (x : ℂ))
  simpa only [coeff_mk, coeff_C_mul] using congrArg (coeff n) hf

/-- An exact compact chain representation for the xi logarithmic coefficients
implies RH, without requiring the initial chain parameter to vanish. -/
theorem riemannHypothesis_of_logDeriv_chain {L mass : ℝ} (hL : 0 ≤ L)
    (hmass : 0 ≤ mass) {g : ℕ → ℝ} (hg : ∀ n, g n ∈ Set.Icc 0 1)
    (hcoeff : ∀ n : ℕ, (-1 : ℂ) ^ n * iteratedDeriv n (logDeriv riemannXiTheta) 0 /
      n.factorial =
        ((mass * coeff n (stieltjesTail (chainStieltjesNumerators L g) 0) : ℝ) : ℂ)) :
    RiemannHypothesis := by
  obtain ⟨mu, _, hpos, hmom⟩ := exists_measure_moments_stieltjesTail
    (chainStieltjesNumerators L g) (chainStieltjesNumerators_nonneg hL hg) hmass
  apply riemannHypothesis_of_logDeriv_moments hpos (fun n => (hmom n).1)
  intro n
  exact (hcoeff n).trans (congrArg (fun x : ℝ => (x : ℂ)) (hmom n).2.symm)

/-- RH is equivalent to an exact normalized compact chain fraction for the
signed complex logarithmic coefficients of the square-variable xi function. -/
theorem riemannHypothesis_iff_exists_logDeriv_chain :
    RiemannHypothesis ↔
      ∃ (L mass : ℝ) (g : ℕ → ℝ), 0 ≤ L ∧ 0 ≤ mass ∧ g 0 = 0 ∧
        (∀ n, g n ∈ Set.Icc 0 1) ∧
        ∀ n : ℕ, (-1 : ℂ) ^ n * iteratedDeriv n (logDeriv riemannXiTheta) 0 /
          n.factorial =
            ((mass * coeff n (stieltjesTail (chainStieltjesNumerators L g) 0) : ℝ) : ℂ) := by
  constructor
  · intro hRH
    simpa only [iteratedDeriv_zero] using exists_logDeriv_riemannXiTheta_chain hRH 0
  · rintro ⟨L, mass, g, hL, hmass, _, hg, hcoeff⟩
    exact riemannHypothesis_of_logDeriv_chain hL hmass hg hcoeff

end RealRooted
