module

public import RealRooted.LaguerreInequalities.Analytic
public import TauCeti.Analysis.Complex.Pick.Nevanlinna
public import Mathlib.MeasureTheory.Measure.Support
import RealRooted.LaguerreInequalities.Nevanlinna
import RealRooted.Mathlib.Analysis.Complex.Pick.Support
import RealRooted.Mathlib.Analysis.Calculus.LogDeriv.Star

/-!
# Nevanlinna measures carried by real zeros

The measure representing a real entire function's negative logarithmic derivative
is supported on its real zeros. In particular, all generalized Laguerre
inequalities provide such a finite measure without assuming a growth bound.
-/

public section

open Complex MeasureTheory
open scoped ComplexConjugate

namespace RealRooted

/-- A finite Nevanlinna measure for the negative logarithmic derivative of a real
entire function is supported on its real zeros. -/
theorem support_nevanlinna_neg_logDeriv_subset_zeros {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hc : ∀ z, f (conj z) = conj (f z))
    {ρ : Measure ℝ} [IsFiniteMeasure ρ] {b c : ℝ}
    (hrep : ∀ z ∈ UpperHalfPlane.upperHalfPlaneSet,
      -logDeriv f z = (b : ℂ) * z + ∫ x, TauCeti.nevanlinnaKernel z x ∂ρ + c) :
    ρ.support ⊆ {x : ℝ | f x = 0} := by
  apply TauCeti.support_subset_of_nevanlinna_of_analyticAt hrep
  · intro r hr
    exact ((hf.deriv.analyticAt r).div (hf.analyticAt r) hr).neg
  · intro x
    simp only [neg_im, logDeriv_ofReal_im hc, neg_zero]

/-- Generalized Laguerre inequalities give a finite Nevanlinna representation
whose measure is carried by the actual real zero set of the function. -/
theorem exists_nevanlinna_supported_on_zeros {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hc : ∀ z, f (conj z) = conj (f z))
    (h : ∀ x n, 0 ≤ laguerreCoefficient f x n) :
    ∃ (ρ : Measure ℝ) (b : ℝ), IsFiniteMeasure ρ ∧ 0 ≤ b ∧
      (∀ z ∈ UpperHalfPlane.upperHalfPlaneSet,
        -logDeriv f z = (b : ℂ) * z + ∫ x, TauCeti.nevanlinnaKernel z x ∂ρ +
          (-logDeriv f I).re) ∧ ρ.support ⊆ {x : ℝ | f x = 0} ∧
      ∀ᵐ (x : ℝ) ∂ρ, f x = 0 := by
  obtain ⟨ρ, b, hρ, hb, hrep⟩ :=
    exists_nevanlinna_neg_logDeriv_of_laguerreCoefficient_nonneg hf hc h
  let _ := hρ
  have hs := support_nevanlinna_neg_logDeriv_subset_zeros hf hc hrep
  exact ⟨ρ, b, hρ, hb, hrep, hs, Filter.mem_of_superset ρ.support_mem_ae hs⟩

end RealRooted
