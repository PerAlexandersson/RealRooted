module

public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.TypeI
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.MomentTypeI
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.LogDerivativeMeasure
import RealRooted.Mathlib.Analysis.Calculus.LogDeriv.Const
import RealRooted.Mathlib.Analysis.Calculus.LogDeriv.MomentContinuation
import RealRooted.Mathlib.MeasureTheory.Measure.NonnegativeMomentTransform

/-!
# The normalized Type-I logarithmic-moment criterion

For an entire function nonzero at zero, its normalization belongs to the positive
Type-I class exactly when the signed Taylor coefficients of its logarithmic
derivative are genuine moments of a nonnegative measure. The coefficients are
compared in the complex numbers, and every natural power is integrable.

This is the normalized form of Sokal (2022), Proposition 6(a)--(b),
https://doi.org/10.1016/j.jmaa.2022.126432. The converse derives the product and
its convergence from the moment measure; it assumes no growth bound.
-/

public section

open Complex MeasureTheory Set
open scoped NNReal

namespace RealRooted

/-- Dividing by the nonzero value at zero leaves the logarithmic derivative
unchanged, including its totalized values at zeros. -/
private theorem logDeriv_div_value_zero {f : ℂ → ℂ} (h0 : f 0 ≠ 0) :
    logDeriv (fun z ↦ f z / f 0) = logDeriv f := by
  funext z
  exact logDeriv_div_const z (f 0) h0

/-- Genuine nonnegative moments of the actual complex logarithmic coefficients
force the normalized entire function to be positive Type-I. -/
theorem isLaguerrePolyaTypeI_div_of_logDeriv_moments
    {f : ℂ → ℂ} {mu : Measure ℝ} (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0)
    (hpos : ∀ᵐ x ∂mu, 0 ≤ x)
    (hint : ∀ n : ℕ, Integrable (fun x : ℝ ↦ x ^ n) mu)
    (hmom : ∀ n : ℕ, (-1 : ℂ) ^ n * iteratedDeriv n (logDeriv f) 0 / n.factorial =
      ((∫ x : ℝ, x ^ n ∂mu : ℝ) : ℂ)) :
    IsLaguerrePolyaTypeI (fun z ↦ f z / f 0) := by
  have : IsFiniteMeasure mu :=
    (integrable_const_iff_isFiniteMeasure (one_ne_zero : (1 : ℝ) ≠ 0)).mp
      (by simpa only [pow_zero] using hint 0)
  obtain ⟨heq, hne⟩ := hf.eqOn_logDeriv_integral_inv_of_moments h0 hpos hint hmom
  apply isLaguerrePolyaTypeI_of_logDeriv_integral
    (hf.div_const (f 0)) (by simp only [div_self h0]) (mu.map Real.toNNReal)
  · intro z hz
    exact div_ne_zero (hne z hz) h0
  · intro z hz
    rw [logDeriv_div_value_zero h0, heq hz]
    exact (Measure.integral_inv_one_add_mul_map_toNNReal hpos z).symm

/-- An entire function's normalization is positive Type-I if and only if its
signed complex logarithmic coefficients are nonnegative-support moments.
Zero measures, constant functions, and measures supported only at zero are included. -/
theorem isLaguerrePolyaTypeI_div_iff_logDeriv_moments
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0) :
    IsLaguerrePolyaTypeI (fun z ↦ f z / f 0) ↔
      ∃ mu : Measure ℝ, (∀ᵐ x ∂mu, 0 ≤ x) ∧
        ∀ n : ℕ, Integrable (fun x : ℝ ↦ x ^ n) mu ∧
          (-1 : ℂ) ^ n * iteratedDeriv n (logDeriv f) 0 / n.factorial =
            ((∫ x : ℝ, x ^ n ∂mu : ℝ) : ℂ) := by
  constructor
  · intro hF
    obtain ⟨_, a, mu, _, _, _, _, _, hsupport, hmom⟩ :=
      hF.exists_logDeriv_moment_measure (by simp only [div_self h0, ne_eq, one_ne_zero,
        not_false_eq_true])
    refine ⟨mu, ?_, ?_⟩
    · have hs : ∀ᵐ x ∂mu, x ∈ Icc 0 (∑' i, a i) := ae_iff.mpr hsupport
      filter_upwards [hs] with x hx
      exact hx.1
    · intro n
      exact ⟨(hmom n).1, by
        simpa only [logDeriv_div_value_zero h0] using (hmom n).2⟩
  · rintro ⟨mu, hpos, hmom⟩
    exact isLaguerrePolyaTypeI_div_of_logDeriv_moments hf h0 hpos
      (fun n ↦ (hmom n).1) (fun n ↦ (hmom n).2)

/-- The logarithmic-moment criterion for entire functions normalized to one. -/
theorem isLaguerrePolyaTypeI_iff_logDeriv_moments
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) (h0 : f 0 = 1) :
    IsLaguerrePolyaTypeI f ↔
      ∃ mu : Measure ℝ, (∀ᵐ x ∂mu, 0 ≤ x) ∧
        ∀ n : ℕ, Integrable (fun x : ℝ ↦ x ^ n) mu ∧
          (-1 : ℂ) ^ n * iteratedDeriv n (logDeriv f) 0 / n.factorial =
            ((∫ x : ℝ, x ^ n ∂mu : ℝ) : ℂ) := by
  simpa only [h0, div_one] using
    isLaguerrePolyaTypeI_div_iff_logDeriv_moments hf (by simp [h0])

end RealRooted
