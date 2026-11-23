module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.Analysis.Analytic.Order
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.MomentResidues
import RealRooted.Mathlib.MeasureTheory.Measure.SortedAtomicMeasure
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Sorted atoms of entire logarithmic-derivative moment measures

The atomic moment measure is carried by zero and by positive slopes whose
negative reciprocals are actual zeros, with each multiplicity the natural
analytic order. Sorting this support gives the finite and infinite cases of
Sokal's Proposition 6(c). Its uniqueness is supplied separately by the existing
logarithmic-moment uniqueness theorem.
-/

public section

open Complex MeasureTheory Set
open scoped ComplexConjugate NNReal

namespace RealRooted

/-- A nonzero entire function has finite nonzero natural order at each zero. -/
private theorem order_ne_zero_of_eq_zero {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0) {z : ℂ} (hz : f z = 0) :
    analyticOrderNatAt f z ≠ 0 := by
  have ha : AnalyticOnNhd ℂ f univ := fun w _ ↦ hf.analyticAt w
  have hfin := ha.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ
    (x := 0) (y := z) (mem_univ _) (mem_univ _)
    (by rw [(hf.analyticAt 0).analyticOrderAt_eq_zero.mpr h0]; simp)
  have hn := (hf.analyticAt z).analyticOrderAt_ne_zero.mpr hz
  simpa only [analyticOrderNatAt, ne_eq, ENat.toNat_eq_zero, not_or] using And.intro hn hfin

/-- The moment measure is carried by the exponential atom and the actual
positive-multiplicity reciprocal roots. The natural order is not totalized at
infinite order because the entire function is nonzero at zero. -/
theorem ae_zero_or_order_ne_zero_of_logDeriv_integral
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0)
    (hc : ∀ z, f (conj z) = conj (f z))
    (mu : Measure ℝ≥0) [IsFiniteMeasure mu]
    (hlog : ∀ z ∈ UpperHalfPlane.upperHalfPlaneSet,
      logDeriv f z = ∫ a : ℝ≥0, (1 + z * ((a : ℝ) : ℂ))⁻¹ ∂mu) :
    ∀ᵐ a : ℝ≥0 ∂mu, a = 0 ∨ analyticOrderNatAt f ((-(a : ℝ)⁻¹ : ℝ) : ℂ) ≠ 0 := by
  filter_upwards [ae_zero_or_reciprocal_zero_of_logDeriv_integral hf hc mu hlog]
    with a ha
  exact ha.imp_right (order_ne_zero_of_eq_zero hf h0)

/-- Infinitely many reciprocal roots have a strictly decreasing enumeration;
the moment mass at each slope is the slope times its actual zero multiplicity. -/
theorem exists_strictAnti_logDeriv_atoms_of_infinite
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0)
    (hc : ∀ z, f (conj z) = conj (f z))
    (mu : Measure ℝ≥0) [IsFiniteMeasure mu]
    (hlog : ∀ z ∈ UpperHalfPlane.upperHalfPlaneSet,
      logDeriv f z = ∫ a : ℝ≥0, (1 + z * ((a : ℝ) : ℂ))⁻¹ ∂mu)
    (hinf : {a : ℝ≥0 | a ≠ 0 ∧
      analyticOrderNatAt f ((-(a : ℝ)⁻¹ : ℝ) : ℂ) ≠ 0}.Infinite) :
    ∃ a : ℕ → ℝ≥0, StrictAnti a ∧ (∀ i, a i ≠ 0 ∧
      analyticOrderNatAt f ((-(a i : ℝ)⁻¹ : ℝ) : ℂ) ≠ 0) ∧
      Summable (fun i ↦ (a i : ℝ)) ∧
      Summable (fun i ↦ (a i : ℝ) *
        (analyticOrderNatAt f ((-(a i : ℝ)⁻¹ : ℝ) : ℂ) : ℝ)) ∧
      mu = mu {0} • Measure.dirac 0 + Measure.sum (fun i ↦ ENNReal.ofReal
        ((a i : ℝ) * (analyticOrderNatAt f ((-(a i : ℝ)⁻¹ : ℝ) : ℂ) : ℝ)) •
          Measure.dirac (a i)) ∧
      range a = {a : ℝ≥0 | a ≠ 0 ∧
        analyticOrderNatAt f ((-(a : ℝ)⁻¹ : ℝ) : ℂ) ≠ 0} := by
  exact mu.exists_strictAnti_atomic_representation_of_infinite
    (fun a ↦ analyticOrderNatAt f ((-(a : ℝ)⁻¹ : ℝ) : ℂ))
    (fun a ha ↦ measureReal_singleton_eq_mul_order_of_logDeriv_integral hf h0 mu hlog ha)
    (ae_zero_or_order_ne_zero_of_logDeriv_integral hf h0 hc mu hlog) hinf

/-- Finitely many reciprocal roots have a strictly decreasing finite enumeration;
the empty enumeration gives the pure exponential case. -/
theorem exists_fin_strictAnti_logDeriv_atoms_of_finite
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0)
    (hc : ∀ z, f (conj z) = conj (f z))
    (mu : Measure ℝ≥0) [IsFiniteMeasure mu]
    (hlog : ∀ z ∈ UpperHalfPlane.upperHalfPlaneSet,
      logDeriv f z = ∫ a : ℝ≥0, (1 + z * ((a : ℝ) : ℂ))⁻¹ ∂mu)
    (hfin : {a : ℝ≥0 | a ≠ 0 ∧
      analyticOrderNatAt f ((-(a : ℝ)⁻¹ : ℝ) : ℂ) ≠ 0}.Finite) :
    ∃ n : ℕ, ∃ a : Fin n → ℝ≥0, StrictAnti a ∧ (∀ i, a i ≠ 0 ∧
      analyticOrderNatAt f ((-(a i : ℝ)⁻¹ : ℝ) : ℂ) ≠ 0) ∧
      Summable (fun i ↦ (a i : ℝ)) ∧
      Summable (fun i ↦ (a i : ℝ) *
        (analyticOrderNatAt f ((-(a i : ℝ)⁻¹ : ℝ) : ℂ) : ℝ)) ∧
      mu = mu {0} • Measure.dirac 0 + Measure.sum (fun i ↦ ENNReal.ofReal
        ((a i : ℝ) * (analyticOrderNatAt f ((-(a i : ℝ)⁻¹ : ℝ) : ℂ) : ℝ)) •
          Measure.dirac (a i)) ∧
      range a = {a : ℝ≥0 | a ≠ 0 ∧
        analyticOrderNatAt f ((-(a : ℝ)⁻¹ : ℝ) : ℂ) ≠ 0} := by
  exact mu.exists_fin_strictAnti_atomic_representation_of_finite
    (fun a ↦ analyticOrderNatAt f ((-(a : ℝ)⁻¹ : ℝ) : ℂ))
    (fun a ha ↦ measureReal_singleton_eq_mul_order_of_logDeriv_integral hf h0 mu hlog ha)
    (ae_zero_or_order_ne_zero_of_logDeriv_integral hf h0 hc mu hlog) hfin

end RealRooted
