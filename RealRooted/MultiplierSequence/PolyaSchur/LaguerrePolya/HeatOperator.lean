module

import RealRooted.Mathlib.Analysis.Complex.HeatOperator.Derivative

public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya
public import RealRooted.Mathlib.Analysis.Complex.HeatOperator.Basic
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.HeatFlow
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.InfiniteDifferentialCoefficients
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Jensen
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Derivative
import RealRooted.Hermite.GaussianHeatOperator
import RealRooted.Mathlib.Analysis.Complex.HeatOperator.Star
import RealRooted.Mathlib.Analysis.Calculus.IteratedDeriv.Star

/-!
# Entire heat evolution preserves Laguerre--Pólya membership

For every nonnegative real time, the convergent backward heat series of an
LP input of order below two remains LP. Gaussian parity identifies each
coefficient series, and Pólya's infinite differential-symbol theorem supplies
the closure result. Zero time and the identically zero input are included.
-/

public section

open Complex Filter Topology

namespace RealRooted

/-- The entire backward heat operator preserves the LP class at every
nonnegative real time for inputs of growth order strictly below two. -/
theorem IsLaguerrePolya.heatOperator {f : ℂ → ℂ} (hf : IsLaguerrePolya f)
    {ρ : ℝ} (horder : TauCeti.OrderLE f ρ) (hρ : ρ < 2) {t : ℝ} (ht : 0 ≤ t) :
    IsLaguerrePolya (Complex.heatOperator (t : ℂ) f) := by
  have hφ := isLaguerrePolya_exp_neg_mul_sq ht
  have hc : ∀ k, Tendsto (fun n => ∑ j ∈ Finset.range n,
      (iteratedDeriv j (fun z => exp (-(t : ℂ) * z ^ 2)) 0).re *
        (iteratedDeriv (k + j) f 0).re / j.factorial) atTop
      (𝓝 ((iteratedDeriv k (Complex.heatOperator (t : ℂ) f) 0).re)) := by
    intro k
    have h := Complex.hasSum_re (hasSum_gaussian_differential hf.differentiable horder hρ t k)
    have hreal (j : ℕ) :
        (iteratedDeriv j (fun z => exp (-(t : ℂ) * z ^ 2)) 0).im = 0 := by
      rw [← Complex.ofReal_re_iteratedDeriv_zero hφ.conj j]
      simp
    simpa only [div_natCast_re, mul_re, hreal, zero_mul, sub_zero] using h.tendsto_sum_nat
  have hconj (z : ℂ) : Complex.heatOperator (t : ℂ) f (starRingEnd ℂ z) =
      starRingEnd ℂ (Complex.heatOperator (t : ℂ) f z) := by
    simpa only [conj_ofReal] using Complex.heatOperator_conj hf.conj (t : ℂ) z
  rw [eq_complexExpGeneratingFunction_of_iteratedDeriv
    (differentiable_heatOperator hf.differentiable horder hρ t)
      (fun k => (Complex.ofReal_re_iteratedDeriv_zero hconj k).symm)]
  exact hφ.infinite_differential_coefficients hf hc

end RealRooted
