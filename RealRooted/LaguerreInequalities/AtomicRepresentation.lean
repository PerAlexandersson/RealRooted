module

public import RealRooted.LaguerreInequalities.Analytic
public import TauCeti.Analysis.Complex.Pick.Nevanlinna
public import Mathlib.MeasureTheory.Measure.Support
import RealRooted.LaguerreInequalities.MeasureSupport
import RealRooted.Mathlib.Analysis.Analytic.CountableZeros
import RealRooted.Mathlib.MeasureTheory.Integral.Bochner.Countable

/-!
# Atomic Nevanlinna sums over real zeros

A nonzero entire function has countably many real zeros. A finite measure carried
by those zeros is therefore atomic, and its Nevanlinna integral is an absolutely
convergent sum. These statements do not yet identify atom masses with zero
multiplicities.
-/

public section

open Complex MeasureTheory Set
open scoped ComplexConjugate

namespace RealRooted

/-- The masses of a finite measure supported on the real zeros of a nonzero
entire function sum to its total mass. -/
theorem hasSum_measureReal_real_zeros {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hne : f ≠ 0) {ρ : Measure ℝ} [IsFiniteMeasure ρ]
    (hs : ρ.support ⊆ {x : ℝ | f x = 0}) :
    HasSum (fun r : {x : ℝ | f x = 0} => ρ.real {(r : ℝ)}) (ρ.real univ) := by
  have hμ : ∀ᵐ (x : ℝ) ∂ρ, x ∈ {r : ℝ | f r = 0} :=
    Filter.mem_of_superset ρ.support_mem_ae hs
  simpa only [smul_eq_mul, mul_one, integral_const] using
    hasSum_integral_of_ae_mem_countable (hf.countable_real_zeroSet hne) hμ
      (integrable_const (1 : ℝ))

/-- The Nevanlinna integral of a measure supported on a nonzero entire function's
real zeros is its convergent atomic sum over those zeros. -/
theorem hasSum_nevanlinnaKernel_real_zeros {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hne : f ≠ 0) {ρ : Measure ℝ} [IsFiniteMeasure ρ]
    (hs : ρ.support ⊆ {x : ℝ | f x = 0}) {z : ℂ}
    (hz : z ∈ UpperHalfPlane.upperHalfPlaneSet) :
    HasSum (fun r : {x : ℝ | f x = 0} =>
      (ρ.real {(r : ℝ)} : ℂ) * TauCeti.nevanlinnaKernel z r)
      (∫ x, TauCeti.nevanlinnaKernel z x ∂ρ) := by
  have hμ : ∀ᵐ (x : ℝ) ∂ρ, x ∈ {r : ℝ | f r = 0} :=
    Filter.mem_of_superset ρ.support_mem_ae hs
  simpa only [Complex.real_smul] using
    hasSum_integral_of_ae_mem_countable (hf.countable_real_zeroSet hne) hμ
      (TauCeti.integrable_nevanlinnaKernel hz ρ)

/-- The atomic Nevanlinna sum over real zeros converges absolutely. -/
theorem summable_norm_nevanlinnaKernel_real_zeros {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hne : f ≠ 0) {ρ : Measure ℝ} [IsFiniteMeasure ρ]
    (hs : ρ.support ⊆ {x : ℝ | f x = 0}) {z : ℂ}
    (hz : z ∈ UpperHalfPlane.upperHalfPlaneSet) :
    Summable (fun r : {x : ℝ | f x = 0} =>
      ρ.real {(r : ℝ)} * ‖TauCeti.nevanlinnaKernel z r‖) := by
  have hμ : ∀ᵐ (x : ℝ) ∂ρ, x ∈ {r : ℝ | f r = 0} :=
    Filter.mem_of_superset ρ.support_mem_ae hs
  simpa only [smul_eq_mul] using
    (hasSum_integral_of_ae_mem_countable (hf.countable_real_zeroSet hne) hμ
      (TauCeti.integrable_nevanlinnaKernel hz ρ).norm).summable

/-- All generalized Laguerre inequalities give an absolutely convergent atomic
Nevanlinna representation over the actual real zeros, without a growth assumption. -/
theorem exists_atomic_nevanlinna_neg_logDeriv {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hc : ∀ z, f (conj z) = conj (f z)) (hne : f ≠ 0)
    (h : ∀ x n, 0 ≤ laguerreCoefficient f x n) :
    ∃ (ρ : Measure ℝ) (b : ℝ), IsFiniteMeasure ρ ∧ 0 ≤ b ∧
      ρ.support ⊆ {x : ℝ | f x = 0} ∧
      HasSum (fun r : {x : ℝ | f x = 0} => ρ.real {(r : ℝ)}) (ρ.real univ) ∧
      ∀ z ∈ UpperHalfPlane.upperHalfPlaneSet,
        HasSum (fun r : {x : ℝ | f x = 0} =>
          (ρ.real {(r : ℝ)} : ℂ) * TauCeti.nevanlinnaKernel z r)
          (-logDeriv f z - (b : ℂ) * z - (-logDeriv f I).re) ∧
        Summable (fun r : {x : ℝ | f x = 0} =>
          ρ.real {(r : ℝ)} * ‖TauCeti.nevanlinnaKernel z r‖) := by
  obtain ⟨ρ, b, hρ, hb, hrep, hs, _⟩ := exists_nevanlinna_supported_on_zeros hf hc h
  let _ := hρ
  refine ⟨ρ, b, hρ, hb, hs, hasSum_measureReal_real_zeros hf hne hs, ?_⟩
  intro z hz
  refine ⟨?_, summable_norm_nevanlinnaKernel_real_zeros hf hne hs hz⟩
  convert hasSum_nevanlinnaKernel_real_zeros hf hne hs hz using 1
  rw [hrep z hz]
  ring

end RealRooted
