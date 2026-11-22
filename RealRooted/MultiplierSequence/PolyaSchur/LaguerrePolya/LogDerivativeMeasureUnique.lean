module

public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.TypeI
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.LogDerivativeMeasure
import RealRooted.Mathlib.MeasureTheory.Measure.MomentDeterminacy

/-!
# Uniqueness of logarithmic-derivative moment measures

The signed logarithmic-derivative coefficients of a Type-I entire function
nonzero at zero have a unique positive representing measure. Uniqueness is
among all measures on the real line with genuine power moments; it does not
assume compact or nonnegative support for a competing measure. The explicit
measure constructed earlier has both properties. This proves the existence
and uniqueness part of Sokal (2022), Appendix A, Proposition 6.
-/

public section

open Complex MeasureTheory

namespace RealRooted

/-- Signed logarithmic-derivative coefficients of a Type-I entire function
nonzero at zero have exactly one measure with integrable power moments. -/
theorem IsLaguerrePolyaTypeI.existsUnique_logDeriv_moment_measure
    {f : ℂ → ℂ} (hf : IsLaguerrePolyaTypeI f) (h0 : f 0 ≠ 0) :
    ∃! mu : Measure ℝ, ∀ k : ℕ, Integrable (fun x : ℝ => x ^ k) mu ∧
      (-1 : ℂ) ^ k * iteratedDeriv k (logDeriv f) 0 / k.factorial =
        ((∫ x : ℝ, x ^ k ∂mu : ℝ) : ℂ) := by
  obtain ⟨gamma, a, mu, _, _, _, _, hfinite, hsupport, hmom⟩ :=
    hf.exists_logDeriv_moment_measure h0
  have : IsFiniteMeasure mu := hfinite
  refine ⟨mu, hmom, fun nu hnu => ?_⟩
  have hbound : ∀ᵐ x ∂mu, |x| ≤ ∑' i, a i := by
    have hs : ∀ᵐ x ∂mu, x ∈ Set.Icc 0 (∑' i, a i) := ae_iff.mpr hsupport
    filter_upwards [hs] with x hx
    simpa only [abs_of_nonneg hx.1] using hx.2
  apply Eq.symm
  apply Measure.ext_of_integral_pow_eq_of_ae_bounded hbound (fun k => (hnu k).1)
  intro k
  exact Complex.ofReal_injective ((hmom k).2.symm.trans (hnu k).2)

/-- A nonzero complex scalar factor leaves the unique logarithmic-derivative
moment measure unchanged. This includes the complex scalar normalization in
Sokal's definition of the positive Type-I class. -/
theorem IsLaguerrePolyaTypeI.existsUnique_logDeriv_const_mul_moment_measure
    {f : ℂ → ℂ} (hf : IsLaguerrePolyaTypeI f) (h0 : f 0 ≠ 0)
    {c : ℂ} (hc : c ≠ 0) :
    ∃! mu : Measure ℝ, ∀ k : ℕ, Integrable (fun x : ℝ => x ^ k) mu ∧
      (-1 : ℂ) ^ k * iteratedDeriv k (logDeriv (fun z => c * f z)) 0 / k.factorial =
        ((∫ x : ℝ, x ^ k ∂mu : ℝ) : ℂ) := by
  have heq : logDeriv (fun z => c * f z) = logDeriv f :=
    funext fun z => logDeriv_const_mul (f := f) z c hc
  simpa only [heq] using hf.existsUnique_logDeriv_moment_measure h0

end RealRooted
