module

public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.TypeI
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Calculus.LogDeriv
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.TypeIMomentCriterion
public import RealRooted.Mathlib.RingTheory.PowerSeries.StieltjesFraction.Tail
import RealRooted.Mathlib.RingTheory.PowerSeries.StieltjesFraction.Moment
import RealRooted.Mathlib.RingTheory.PowerSeries.StieltjesFraction.MomentCriterion
import RealRooted.Mathlib.RingTheory.PowerSeries.StieltjesFraction.Uniqueness

/-!
# The Type-I continued-fraction criterion

An entire function nonzero at the origin is positive Type-I after normalization
exactly when its signed logarithmic-derivative Taylor series is the complex
image of a nonnegative real Stieltjes fraction. No reality or growth premise
is imposed on the original function: the formal identity compares its actual
complex coefficients.

This combines Propositions 6 and 7 of Sokal, "When does a hypergeometric
function pFq belong to the Laguerre–Pólya class LP+?", published p. 5.
The negative-numerator obstruction requires a nonzero outer scalar and no
earlier termination, as explained immediately after Proposition 7.
-/

public section

open Complex MeasureTheory
open scoped PowerSeries

namespace RealRooted

/-- The normalized Type-I class is characterized by a nonnegative formal
Stieltjes expansion of the actual complex logarithmic coefficients. -/
theorem isLaguerrePolyaTypeI_div_iff_stieltjesTail
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0) :
    IsLaguerrePolyaTypeI (fun z => f z / f 0) ↔
      ∃ (c : ℝ) (a : ℕ → ℝ), 0 ≤ c ∧ (∀ k, 0 ≤ a k) ∧
        PowerSeries.mk (fun k => (-1 : ℂ) ^ k * iteratedDeriv k (logDeriv f) 0 /
          k.factorial) = PowerSeries.map (algebraMap ℝ ℂ)
            (PowerSeries.C c * PowerSeries.stieltjesTail a 0) := by
  constructor
  · intro hF
    obtain ⟨mu, hpos, hmom⟩ :=
      (isLaguerrePolyaTypeI_div_iff_logDeriv_moments hf h0).mp hF
    obtain ⟨a, ha, hseries⟩ :=
      PowerSeries.exists_stieltjesTail_of_nonnegative_moments (fun k => (hmom k).1) hpos
    refine ⟨mu.real Set.univ, a, measureReal_nonneg, ha, ?_⟩
    rw [← hseries]
    ext k
    simp only [PowerSeries.coeff_mk, PowerSeries.coeff_map]
    exact (hmom k).2
  · rintro ⟨c, a, hc, ha, hseries⟩
    obtain ⟨mu, _, hpos, hmom⟩ := PowerSeries.exists_measure_moments_stieltjesTail a ha hc
    apply isLaguerrePolyaTypeI_div_of_logDeriv_moments hf h0 hpos (fun k => (hmom k).1)
    intro k
    have hk := congrArg (PowerSeries.coeff k) hseries
    simp only [PowerSeries.coeff_mk, PowerSeries.coeff_map, PowerSeries.coeff_C_mul] at hk
    rw [(hmom k).2]
    exact hk

/-- A negative active Stieltjes numerator excludes the normalized Type-I class.
A zero outer scalar or an earlier zero numerator would hide the negative term. -/
theorem not_isLaguerrePolyaTypeI_div_of_active_neg
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0)
    {c : ℝ} (hc : c ≠ 0) {a : ℕ → ℝ} {n : ℕ}
    (hprefix : ∀ i < n, a i ≠ 0) (hn : a n < 0)
    (hseries : PowerSeries.mk (fun k => (-1 : ℂ) ^ k *
      iteratedDeriv k (logDeriv f) 0 / k.factorial) =
      PowerSeries.map (algebraMap ℝ ℂ) (PowerSeries.C c * PowerSeries.stieltjesTail a 0)) :
    ¬ IsLaguerrePolyaTypeI (fun z => f z / f 0) := by
  intro hF
  obtain ⟨d, b, _, hb, hother⟩ := (isLaguerrePolyaTypeI_div_iff_stieltjesTail hf h0).mp hF
  have hreal := PowerSeries.map_injective (algebraMap ℝ ℂ) Complex.ofReal_injective
    (hseries.symm.trans hother)
  have hcd : c = d := by
    have h := congrArg PowerSeries.constantCoeff hreal
    simpa only [map_mul, PowerSeries.constantCoeff_C,
      PowerSeries.constantCoeff_stieltjesTail, mul_one] using h
  subst d
  have hC : (PowerSeries.C c : ℝ⟦X⟧) ≠ 0 := by
    intro hz
    apply hc
    simpa only [PowerSeries.constantCoeff_C, map_zero] using
      congrArg PowerSeries.constantCoeff hz
  apply PowerSeries.stieltjesTail_ne_of_active_neg (s := 0) (t := 0) (n := n)
    (by simpa only [Nat.zero_add] using hprefix) (by simpa only [Nat.zero_add] using hn) hb
  exact mul_left_cancel₀ hC hreal

end RealRooted
