module

public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.TypeI
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.TypeIFactorization
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.PowerSumMoments
import RealRooted.Mathlib.MeasureTheory.Integral.Bochner.PowerSum
import RealRooted.Mathlib.Analysis.Calculus.LogDeriv.Star
import RealRooted.Mathlib.Analysis.Calculus.IteratedDeriv.Star

/-!
# Positive measures for logarithmic derivatives of Type-I functions

The signed Taylor coefficients of the analytic logarithmic derivative of a
Type-I entire function nonzero at zero are moments of a finite positive measure
with compact nonnegative support. The measure has exponential mass at zero and
mass equal to each linear slope at that slope. Repeated slopes count their
multiplicities. This proves the measure-existence direction of Sokal (2022),
Proposition 6, https://doi.org/10.1016/j.jmaa.2022.126432.

The identity uses the actual complex coefficients, not only their real parts.
-/

public section

open Complex MeasureTheory

namespace RealRooted

/-- The signed logarithmic-derivative Taylor coefficients of a Type-I entire
function are moments of the atomic measure from the same product factorization. -/
theorem IsLaguerrePolyaTypeI.exists_logDeriv_moment_measure_factorization
    {f : ℂ → ℂ} (hf : IsLaguerrePolyaTypeI f) (h0 : f 0 ≠ 0) :
    ∃ (gamma : ℝ) (a : ℕ → ℝ) (mu : Measure ℝ),
      0 ≤ gamma ∧ (∀ i, 0 ≤ a i) ∧ Summable a ∧
      f = (fun z => f 0 * Complex.exp (gamma * z) * ∏' i, (1 + (a i : ℂ) * z)) ∧
      mu = ENNReal.ofReal gamma • Measure.dirac 0 +
        Measure.sum (fun i => ENNReal.ofReal (a i) • Measure.dirac (a i)) ∧
      IsFiniteMeasure mu ∧ mu (Set.Icc 0 (∑' i, a i))ᶜ = 0 ∧
      ∀ k : ℕ, Integrable (fun x : ℝ => x ^ k) mu ∧
        (-1 : ℂ) ^ k * iteratedDeriv k (logDeriv f) 0 / k.factorial =
          ((∫ x : ℝ, x ^ k ∂mu : ℝ) : ℂ) := by
  obtain ⟨gamma, a, hg, ha, hs, heq⟩ := hf.exists_eq_exp_mul_prod h0
  obtain ⟨mu, hmu, hfinite, hsupport, hmom⟩ := exists_measure_power_sum_moments ha hs hg
  refine ⟨gamma, a, mu, hg, ha, hs, heq, hmu, hfinite, hsupport, fun k => ⟨(hmom k).1, ?_⟩⟩
  have hpower := signed_logDeriv_exp_linear_product h0 gamma a hs k
  rw [← heq] at hpower
  have heqreal := hpower.trans (hmom k).2.symm
  have hreal : ((iteratedDeriv k (logDeriv f) 0).re : ℂ) =
      iteratedDeriv k (logDeriv f) 0 :=
    ofReal_re_iteratedDeriv_zero (logDeriv_conj hf.toLaguerrePolya.conj) k
  have h := congrArg (fun r : ℝ => (r : ℂ)) heqreal
  simpa only [ofReal_div, ofReal_mul, ofReal_pow, ofReal_neg, ofReal_one,
    ofReal_natCast, hreal] using h

/-- The signed logarithmic-derivative Taylor coefficients of a Type-I entire
function are the moments of an explicit finite positive atomic measure. -/
theorem IsLaguerrePolyaTypeI.exists_logDeriv_moment_measure
    {f : ℂ → ℂ} (hf : IsLaguerrePolyaTypeI f) (h0 : f 0 ≠ 0) :
    ∃ (gamma : ℝ) (a : ℕ → ℝ) (mu : Measure ℝ),
      0 ≤ gamma ∧ (∀ i, 0 ≤ a i) ∧ Summable a ∧
      mu = ENNReal.ofReal gamma • Measure.dirac 0 +
        Measure.sum (fun i => ENNReal.ofReal (a i) • Measure.dirac (a i)) ∧
      IsFiniteMeasure mu ∧ mu (Set.Icc 0 (∑' i, a i))ᶜ = 0 ∧
      ∀ k : ℕ, Integrable (fun x : ℝ => x ^ k) mu ∧
        (-1 : ℂ) ^ k * iteratedDeriv k (logDeriv f) 0 / k.factorial =
          ((∫ x : ℝ, x ^ k ∂mu : ℝ) : ℂ) := by
  obtain ⟨gamma, a, mu, hg, ha, hs, _, hmu, hfinite, hsupport, hmom⟩ :=
    hf.exists_logDeriv_moment_measure_factorization h0
  exact ⟨gamma, a, mu, hg, ha, hs, hmu, hfinite, hsupport, hmom⟩

end RealRooted
