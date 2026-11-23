/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.TypeI
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Calculus.LogDeriv
public import RealRooted.Mathlib.RingTheory.PowerSeries.StieltjesFraction.ChainParameters
import RealRooted.Mathlib.RingTheory.PowerSeries.StieltjesFraction.CompactMomentsChain
import RealRooted.Mathlib.RingTheory.PowerSeries.StieltjesFraction.ChainAeration
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.StieltjesFraction
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.LogDerivativeMeasure
import RealRooted.Mathlib.Analysis.Calculus.LogDeriv.Const

/-!
# The normalized Type-I criterion by bounded Wall chains

The actual complex signed logarithmic Taylor series of an entire function,
nonzero at zero, has a bounded Wall chain exactly when its normalization is
positive Type-I. The compact moment measure is obtained from Type-I
factorization, so no growth or support hypothesis is imposed on the function.

This combines the logarithmic moment criterion of Sokal, Proposition 6,
published p. 5, with Wall's compact moment criterion as presented in Sokal,
arXiv:1903.12455v2, and Sokal-Walrad, arXiv:2404.12131v1, Theorem 1.
The combination is stated here as a derived consequence. Constants, the
exponential atom at zero, and terminating chains are included.
-/

public section

open Complex MeasureTheory
open scoped PowerSeries

namespace RealRooted

/-- Normalized positive Type-I entire functions are exactly those whose
actual complex logarithmic Taylor series admits a bounded Wall chain with
initial parameter zero. No reality or growth premise is required. -/
theorem isLaguerrePolyaTypeI_div_iff_chainStieltjesTail
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0) :
    IsLaguerrePolyaTypeI (fun z => f z / f 0) ↔
      ∃ (L mass : ℝ) (g : ℕ → ℝ), 0 ≤ L ∧ 0 ≤ mass ∧ g 0 = 0 ∧
        (∀ n, g n ∈ Set.Icc 0 1) ∧
        PowerSeries.mk (fun n => (-1 : ℂ) ^ n * iteratedDeriv n (logDeriv f) 0 /
          n.factorial) = PowerSeries.map (algebraMap ℝ ℂ)
            (PowerSeries.C mass * PowerSeries.stieltjesTail
              (PowerSeries.chainStieltjesNumerators L g) 0) := by
  constructor
  · intro hF
    obtain ⟨_, b, mu, _, hb, _, _, _, hsupport, hmom⟩ :=
      hF.exists_logDeriv_moment_measure
        (by simp only [div_self h0, ne_eq, one_ne_zero, not_false_eq_true])
    have hL : 0 ≤ ∑' i, b i := tsum_nonneg hb
    obtain ⟨g, hg0, hg, hseries⟩ := PowerSeries.exists_chainStieltjes_of_moments_Icc
      hL (ae_iff.mpr hsupport) (fun n => (hmom n).1)
    have hlog : logDeriv (fun z => f z / f 0) = logDeriv f :=
      funext fun z => logDeriv_div_const z (f 0) h0
    refine ⟨∑' i, b i, mu.real Set.univ, g, hL, measureReal_nonneg, hg0, hg, ?_⟩
    rw [← hseries]
    ext n
    simp only [PowerSeries.coeff_mk, PowerSeries.coeff_map]
    simpa only [hlog, Complex.coe_algebraMap] using (hmom n).2
  · rintro ⟨L, mass, g, hL, hmass, _, hg, hseries⟩
    apply (isLaguerrePolyaTypeI_div_iff_stieltjesTail hf h0).mpr
    exact ⟨mass, PowerSeries.chainStieltjesNumerators L g, hmass,
      PowerSeries.chainStieltjesNumerators_nonneg hL hg, hseries⟩

/-- The initial chain parameter may be arbitrary in the closed unit interval;
the existence criterion for normalized Type-I entire functions is unchanged. -/
theorem isLaguerrePolyaTypeI_div_iff_bounded_chainStieltjesTail
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0) :
    IsLaguerrePolyaTypeI (fun z => f z / f 0) ↔
      ∃ (L mass : ℝ) (g : ℕ → ℝ), 0 ≤ L ∧ 0 ≤ mass ∧
        (∀ n, g n ∈ Set.Icc 0 1) ∧
        PowerSeries.mk (fun n => (-1 : ℂ) ^ n * iteratedDeriv n (logDeriv f) 0 /
          n.factorial) = PowerSeries.map (algebraMap ℝ ℂ)
            (PowerSeries.C mass * PowerSeries.stieltjesTail
              (PowerSeries.chainStieltjesNumerators L g) 0) := by
  constructor
  · intro hF
    obtain ⟨L, mass, g, hL, hmass, _, hg, hs⟩ :=
      (isLaguerrePolyaTypeI_div_iff_chainStieltjesTail hf h0).mp hF
    exact ⟨L, mass, g, hL, hmass, hg, hs⟩
  · rintro ⟨L, mass, g, hL, hmass, hg, hs⟩
    exact (isLaguerrePolyaTypeI_div_iff_stieltjesTail hf h0).mpr
      ⟨mass, PowerSeries.chainStieltjesNumerators L g, hmass,
        PowerSeries.chainStieltjesNumerators_nonneg hL hg, hs⟩

/-- For an entire function already normalized to one at zero, the bounded
Wall chain directly characterizes its positive Type-I membership. -/
theorem isLaguerrePolyaTypeI_iff_chainStieltjesTail
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) (h0 : f 0 = 1) :
    IsLaguerrePolyaTypeI f ↔
      ∃ (L mass : ℝ) (g : ℕ → ℝ), 0 ≤ L ∧ 0 ≤ mass ∧ g 0 = 0 ∧
        (∀ n, g n ∈ Set.Icc 0 1) ∧
        PowerSeries.mk (fun n => (-1 : ℂ) ^ n * iteratedDeriv n (logDeriv f) 0 /
          n.factorial) = PowerSeries.map (algebraMap ℝ ℂ)
            (PowerSeries.C mass * PowerSeries.stieltjesTail
              (PowerSeries.chainStieltjesNumerators L g) 0) := by
  simpa only [h0, div_one] using
    isLaguerrePolyaTypeI_div_iff_chainStieltjesTail hf (by simp only [h0, one_ne_zero, ne_eq,
      not_false_eq_true])

end RealRooted
