/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import RealRooted.Mathlib.NumberTheory.LSeries.RiemannXi.Theta
public import RealRooted.Mathlib.RingTheory.PowerSeries.StieltjesFraction.Tail
import RealRooted.Mathlib.RingTheory.PowerSeries.StieltjesFraction.StrictMoment
import RealRooted.Mathlib.RingTheory.PowerSeries.StieltjesFraction.Moment
import RealRooted.Mathlib.Analysis.Calculus.LogDeriv.Star
import RealRooted.Mathlib.Analysis.Calculus.IteratedDeriv.Star
import RealRooted.RiemannHypothesis.StrictMoments
import RealRooted.RiemannHypothesis.MomentCriterion

/-!
# RH and formal Stieltjes fractions of logarithmic xi derivatives

RH gives strictly positive formal Stieltjes numerators for the signed
logarithmic-derivative coefficients of every derivative of the square-variable
xi function. Conversely, any nonnegative formal S-fraction for the unshifted
logarithmic derivative gives a genuine moment measure and hence RH.

The identities are formal power-series identities. They do not assert
numerical convergence of the continued fraction. The converse uses the
actual complex Taylor coefficients, whose reality is proved unconditionally.
-/

public section

open Complex Polynomial MeasureTheory

namespace RealRooted

/-- Under RH, each xi derivative has a strictly positive formal S-fraction for
the signed Taylor coefficients of its logarithmic derivative. -/
theorem exists_pos_stieltjesTail_logDeriv_riemannXiTheta
    (hRH : RiemannHypothesis) (s : ℕ) :
    ∃ (c : ℝ) (a : ℕ → ℝ), 0 < c ∧ (∀ k, 0 < a k) ∧
      PowerSeries.mk (fun k => (-1 : ℝ) ^ k *
        (iteratedDeriv k (logDeriv (iteratedDeriv s riemannXiTheta)) 0).re / k.factorial) =
        PowerSeries.C c * PowerSeries.stieltjesTail a 0 := by
  let m : ℕ → ℝ := fun k => (-1 : ℝ) ^ k *
    (iteratedDeriv k (logDeriv (iteratedDeriv s riemannXiTheta)) 0).re / k.factorial
  have hpos (n : ℕ) : (momentHankelMatrix m n).PosDef := by
    have h := posDef_logDeriv_iteratedDeriv_riemannXiTheta hRH s n 0
    simp only [Nat.add_zero] at h
    exact h
  have hshift (n : ℕ) : (momentHankelMatrix (fun k => m (k + 1)) n).PosDef := by
    exact posDef_logDeriv_iteratedDeriv_riemannXiTheta hRH s n 1
  obtain ⟨a, ha, _, hf⟩ := exists_pos_stieltjesTail_of_hankel_posDef m hpos hshift
  refine ⟨m 0, a, ?_, ha, hf⟩
  simpa only [momentNormSq_zero] using momentNormSq_pos m 0 (hpos 1)

/-- Mathlib's RH is equivalent to a nonnegative formal Stieltjes fraction for
the signed logarithmic-derivative coefficients of the square-variable xi function. -/
theorem riemannHypothesis_iff_exists_stieltjesTail_logDeriv :
    RiemannHypothesis ↔ ∃ (c : ℝ) (a : ℕ → ℝ), 0 ≤ c ∧ (∀ k, 0 ≤ a k) ∧
      PowerSeries.mk (fun k => (-1 : ℝ) ^ k *
        (iteratedDeriv k (logDeriv riemannXiTheta) 0).re / k.factorial) =
        PowerSeries.C c * PowerSeries.stieltjesTail a 0 := by
  constructor
  · intro hRH
    obtain ⟨c, a, hc, ha, hf⟩ := exists_pos_stieltjesTail_logDeriv_riemannXiTheta hRH 0
    exact ⟨c, a, hc.le, fun k => (ha k).le, by simpa only [iteratedDeriv_zero] using hf⟩
  · rintro ⟨c, a, hc, ha, hf⟩
    obtain ⟨mu, _, hpos, hmom⟩ :=
      PowerSeries.exists_measure_moments_of_eq_stieltjesTail ha hc hf
    apply riemannHypothesis_of_logDeriv_moments hpos (fun k => (hmom k).1)
    intro k
    have hreal : ((iteratedDeriv k (logDeriv riemannXiTheta) 0).re : ℂ) =
        iteratedDeriv k (logDeriv riemannXiTheta) 0 :=
      ofReal_re_iteratedDeriv_zero (logDeriv_conj riemannXiTheta_conj) k
    have h := congrArg (fun r : ℝ => (r : ℂ)) (hmom k).2
    simpa only [PowerSeries.coeff_mk, ofReal_div, ofReal_mul, ofReal_pow,
      ofReal_neg, ofReal_one, ofReal_natCast, hreal] using h.symm

/-- The nonnegative-fraction criterion is equivalent to a strictly positive
one, because RH makes every shifted Hankel form strictly positive. -/
theorem riemannHypothesis_iff_exists_pos_stieltjesTail_logDeriv :
    RiemannHypothesis ↔ ∃ (c : ℝ) (a : ℕ → ℝ), 0 < c ∧ (∀ k, 0 < a k) ∧
      PowerSeries.mk (fun k => (-1 : ℝ) ^ k *
        (iteratedDeriv k (logDeriv riemannXiTheta) 0).re / k.factorial) =
        PowerSeries.C c * PowerSeries.stieltjesTail a 0 := by
  constructor
  · intro hRH
    simpa only [iteratedDeriv_zero] using exists_pos_stieltjesTail_logDeriv_riemannXiTheta hRH 0
  · rintro ⟨c, a, hc, ha, hf⟩
    exact riemannHypothesis_iff_exists_stieltjesTail_logDeriv.mpr
      ⟨c, a, hc.le, fun k => (ha k).le, hf⟩

end RealRooted
