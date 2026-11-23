module

import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Complex.Exponential
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Dirac.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Defs
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.SortedProduct
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.MomentResidues
import RealRooted.Mathlib.Analysis.Calculus.LogDeriv.MomentContinuation
import RealRooted.Mathlib.MeasureTheory.Measure.NonnegativeMomentTransform
import RealRooted.Mathlib.MeasureTheory.Measure.NonnegativeAtomicMap
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# The sorted atomic logarithmic-moment criterion

Genuine moments of the actual complex logarithmic coefficients give the sorted
atomic measure and the corresponding entire product. The scalar `f(0)` may be
any nonzero complex number. No growth or reality assumption is added.

Together with the checked normalized Type-I criterion and moment-measure
uniqueness, this is Sokal (2022), Appendix A, Proposition 6(c), equation (7):
https://doi.org/10.1016/j.jmaa.2022.126432. Finite and empty root sets are included
by zero-multiplicity padding of a strictly decreasing summable positive sequence.
-/

public section

open Complex MeasureTheory Set
open scoped NNReal

namespace RealRooted

/-- The same strictly decreasing positive sequence represents the original
moment measure and the entire function, with actual natural zero multiplicities.
Finite and empty supports use zero multiplicities at the padded slopes. -/
theorem exists_strictAnti_factorization_of_logDeriv_moments
    {f : ℂ → ℂ} {mu : Measure ℝ} (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0)
    (hpos : ∀ᵐ x ∂mu, 0 ≤ x)
    (hint : ∀ n : ℕ, Integrable (fun x : ℝ ↦ x ^ n) mu)
    (hmom : ∀ n : ℕ, (-1 : ℂ) ^ n * iteratedDeriv n (logDeriv f) 0 / n.factorial =
      ((∫ x : ℝ, x ^ n ∂mu : ℝ) : ℂ)) :
    ∃ a : ℕ → ℝ≥0, StrictAnti a ∧ (∀ i, 0 < a i) ∧
      Summable (fun i ↦ (a i : ℝ)) ∧
      Summable (fun i ↦ (a i : ℝ) *
        (analyticOrderNatAt f ((-(a i : ℝ)⁻¹ : ℝ) : ℂ) : ℝ)) ∧
      mu = ENNReal.ofReal (mu.real {0}) • Measure.dirac 0 + Measure.sum (fun i ↦ ENNReal.ofReal
        ((a i : ℝ) * (analyticOrderNatAt f ((-(a i : ℝ)⁻¹ : ℝ) : ℂ) : ℝ)) •
          Measure.dirac (a i : ℝ)) ∧
      ∀ z : ℂ, HasProd (fun i ↦ (1 + ((a i : ℝ) : ℂ) * z) ^
          analyticOrderNatAt f ((-(a i : ℝ)⁻¹ : ℝ) : ℂ))
          (f z / (f 0 * exp ((mu.real {0} : ℂ) * z))) ∧
        f z = f 0 * exp ((mu.real {0} : ℂ) * z) * ∏' i,
          (1 + ((a i : ℝ) : ℂ) * z) ^ analyticOrderNatAt f ((-(a i : ℝ)⁻¹ : ℝ) : ℂ) := by
  have : IsFiniteMeasure mu :=
    (integrable_const_iff_isFiniteMeasure (one_ne_zero : (1 : ℝ) ≠ 0)).mp
      (by simpa only [pow_zero] using hint 0)
  let F : ℂ → ℂ := fun z ↦ f z / f 0
  let nu : Measure ℝ≥0 := mu.map Real.toNNReal
  have hF : Differentiable ℂ F := hf.div_const (f 0)
  have hF0 : F 0 = 1 := div_self h0
  have hF0n : F 0 ≠ 0 := by simp only [hF0, ne_eq, one_ne_zero, not_false_eq_true]
  have hFD : logDeriv F = logDeriv f := by
    funext z
    simpa only [F, div_eq_mul_inv] using
      logDeriv_mul_const (f := f) z (f 0)⁻¹ (inv_ne_zero h0)
  obtain ⟨heq, hne⟩ := hf.eqOn_logDeriv_integral_inv_of_moments h0 hpos hint hmom
  have hFn : ∀ z ∈ slitPlane, F z ≠ 0 := fun z hz ↦ div_ne_zero (hne z hz) h0
  have hlogF : EqOn (logDeriv F)
      (fun z ↦ ∫ x : ℝ≥0, (1 + z * ((x : ℝ) : ℂ))⁻¹ ∂nu) slitPlane := by
    intro z hz
    rw [hFD, heq hz]
    exact (Measure.integral_inv_one_add_mul_map_toNNReal hpos z).symm
  have hFc := conj_of_logDeriv_integral hF hF0 nu hFn hlogF
  have hH : ∀ z ∈ UpperHalfPlane.upperHalfPlaneSet, z ∈ slitPlane :=
    fun z hz ↦ mem_slitPlane_iff.mpr (Or.inr (ne_of_gt hz))
  obtain ⟨a, ha, hapos, hs, hms, hnu, hprod⟩ :=
    exists_strictAnti_logDeriv_factorization hF hF0n hFc nu
      (fun z hz ↦ hFn z (hH z hz)) (fun z hz ↦ hlogF (hH z hz))
  have hord (z : ℂ) : analyticOrderNatAt F z = analyticOrderNatAt f z := by
    simpa only [F, div_eq_mul_inv, Pi.mul_def] using
      analyticOrderNatAt_mul_const (hf.analyticAt z) (inv_ne_zero h0)
  simp_rw [hord] at hms hnu hprod
  have hnu0 : nu {0} = mu {0} := Measure.map_toNNReal_singleton_zero_of_ae_nonneg hpos
  have hatom : nu.real {0} = mu.real {0} := congrArg ENNReal.toReal hnu0
  have hmu := Measure.eq_atomic_of_map_toNNReal_eq hpos hnu
  rw [hnu0, ← ofReal_measureReal] at hmu
  refine ⟨a, ha, hapos, hs, hms, hmu, fun z ↦ ?_⟩
  have hp : HasProd (fun i ↦ (1 + ((a i : ℝ) : ℂ) * z) ^
        analyticOrderNatAt f ((-(a i : ℝ)⁻¹ : ℝ) : ℂ))
      (f z / (f 0 * exp ((mu.real {0} : ℂ) * z))) := by
    simpa only [hF0, one_mul, hatom, F, div_div] using (hprod z).1
  refine ⟨hp, ?_⟩
  have heq := (eq_div_iff (mul_ne_zero h0 (exp_ne_zero _))).mp hp.tprod_eq
  simpa only [mul_comm] using heq.symm

end RealRooted
