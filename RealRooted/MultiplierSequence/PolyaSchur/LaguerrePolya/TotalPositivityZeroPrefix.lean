module

public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.TypeI
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.TotalPositivityConverse
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.TotalPositivity
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.TypeIClosure
import RealRooted.AissenSchoenbergWhitney
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Complex.TaylorSeries

/-!
# Entire Pólya-frequency series with initial zeros

Every entire function with a real PF generating-series germ belongs to the
positive Type-I Laguerre--Pólya class. Initial zero coefficients are removed
using the analytic divided difference at zero and restored as factors of `z`.
The identically zero function is included.

Together with the forward coefficient theorem this proves Theorem C in
O. M. Katkova, *Multiple positivity and the Riemann zeta-function*,
arXiv:math/0505174, without a nonzero constant-coefficient restriction.
-/

public section

open Complex Filter Topology

namespace RealRooted

/-- A power-series germ can be divided by its initial zero coefficient while
retaining an entire function. -/
private theorem isLaguerrePolyaTypeI_of_nonzero_coefficient
    (n : ℕ) {a : ℕ → ℝ} {f : ℂ → ℂ} (ha : IsPolyaFreqSeq a) (han : a n ≠ 0)
    (hf : Differentiable ℂ f)
    (hs : ∀ᶠ z in 𝓝 (0 : ℂ), HasSum (fun k => (a k : ℂ) * z ^ k) (f z)) :
    IsLaguerrePolyaTypeI f := by
  induction n generalizing a f with
  | zero =>
      exact ha.isLaguerrePolyaTypeI_of_hasSum ((ha.nonneg 0).lt_of_ne' han) hf hs
  | succ n ih =>
      by_cases ha0 : a 0 = 0
      · have hp : HasFPowerSeriesAt f
            (FormalMultilinearSeries.ofScalars ℂ (fun k => (a k : ℂ))) 0 := by
          simpa [hasFPowerSeriesAt_iff, smul_eq_mul, mul_comm] using hs
        have hf0 : f 0 = 0 := by
          simpa [FormalMultilinearSeries.ofScalars, ha0] using (hp.coeff_zero 1).symm
        have hd : Differentiable ℂ (dslope f 0) :=
          fun z => ((hf.analyticAt z).dslope 0).differentiableAt
        have hds : ∀ᶠ z in 𝓝 (0 : ℂ),
            HasSum (fun k => (a (k + 1) : ℂ) * z ^ k) (dslope f 0 z) := by
          simpa [hasFPowerSeriesAt_iff, FormalMultilinearSeries.coeff_fslope,
            smul_eq_mul, mul_comm] using hp.dslope_fslope
        have htype := ih (ha.tail_of_zero ha0) han hd hds
        have hid : IsLaguerrePolyaTypeI (fun z : ℂ => z) := by
          simpa using (isPFPolynomial_X_pow 1).isLaguerrePolyaTypeI
        convert hid.mul htype using 1
        funext z
        simpa [smul_eq_mul, hf0] using (sub_smul_dslope f 0 z).symm
      · exact ha.isLaguerrePolyaTypeI_of_hasSum ((ha.nonneg 0).lt_of_ne' ha0) hf hs

/-- An entire function with a real PF generating-series germ belongs to the
positive Type-I Laguerre--Pólya class, including initial zeros and the zero function. -/
theorem IsPolyaFreqSeq.isLaguerrePolyaTypeI_of_entire
    {a : ℕ → ℝ} {f : ℂ → ℂ} (ha : IsPolyaFreqSeq a) (hf : Differentiable ℂ f)
    (hs : ∀ᶠ z in 𝓝 (0 : ℂ), HasSum (fun k => (a k : ℂ) * z ^ k) (f z)) :
    IsLaguerrePolyaTypeI f := by
  by_cases hnonzero : ∃ n, a n ≠ 0
  · obtain ⟨n, hn⟩ := hnonzero
    exact isLaguerrePolyaTypeI_of_nonzero_coefficient n ha hn hf hs
  · have ha0 : ∀ n, a n = 0 := by simpa using hnonzero
    have heq : f =ᶠ[𝓝 0] 0 := by
      filter_upwards [hs] with z hz
      simpa [ha0] using hz.tsum_eq.symm
    have hfzero : f = 0 :=
      (hf.differentiableOn.analyticOnNhd isOpen_univ).eq_of_eventuallyEq
        analyticOnNhd_const heq
    simp [hfzero]

/-- An entire function with real Taylor data is positive Type-I Laguerre--Pólya
exactly when its ordinary Taylor coefficients form a Pólya-frequency sequence.
No nonvanishing or positivity assumption at the origin is required. -/
theorem isLaguerrePolyaTypeI_iff_isPolyaFreqSeq_of_entire
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hreal : ∀ k, iteratedDeriv k f 0 = ((iteratedDeriv k f 0).re : ℂ)) :
    IsLaguerrePolyaTypeI f ↔
      IsPolyaFreqSeq (fun k => (iteratedDeriv k f 0).re / k.factorial) := by
  refine ⟨IsLaguerrePolyaTypeI.isPolyaFreqSeq, fun h => ?_⟩
  apply h.isLaguerrePolyaTypeI_of_entire hf
  apply Eventually.of_forall
  intro z
  convert hasSum_taylorSeries_of_entire hf 0 z using 1
  funext k
  rw [hreal k]
  simp [smul_eq_mul, div_eq_mul_inv, mul_comm, mul_left_comm]

end RealRooted
