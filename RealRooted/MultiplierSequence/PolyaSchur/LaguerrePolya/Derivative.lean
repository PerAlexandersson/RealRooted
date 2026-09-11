import RealRooted.Derivative.FamilyClosure
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# Holomorphic Laguerre--Pólya limits

This opt-in analytic leaf proves that zero-aware Laguerre--Pólya limits are
holomorphic, have closed discrete zero sets when nonzero, and are closed under
the complex derivative.  It combines derivative closure for real-splitting
polynomials with Mathlib's locally uniform convergence theorems for complex
holomorphic functions.  It does not prove analytic root closure of arbitrary
locally uniform limits.
-/

open Filter Polynomial Topology

noncomputable section

namespace RealRooted

/-- A zero-aware Laguerre--Pólya limit is complex differentiable everywhere. -/
theorem IsLaguerrePolya.differentiable {f : ℂ → ℂ} (hf : IsLaguerrePolya f) :
    Differentiable ℂ f := by
  rcases hf with ⟨p, hp, hptend⟩
  have hdifferentiable := (tendstoLocallyUniformlyOn_univ.mpr hptend).differentiableOn
    (Eventually.of_forall fun n =>
      (Polynomial.differentiable ((p n).map Complex.ofRealHom)).differentiableOn)
    isOpen_univ
  exact differentiableOn_univ.mp hdifferentiable

/-- A zero-aware Laguerre--Pólya limit is analytic on the whole complex plane. -/
theorem IsLaguerrePolya.analyticOnNhd {f : ℂ → ℂ} (hf : IsLaguerrePolya f) :
    AnalyticOnNhd ℂ f Set.univ := by
  intro z _
  exact hf.differentiable.analyticAt z

/-- The zeros of a nonzero Laguerre--Pólya limit form a closed discrete subset
of the complex plane.  This does not assert that the zeros are real. -/
theorem IsLaguerrePolya.isClosed_and_isDiscrete_preimage_zero {f : ℂ → ℂ}
    (hf : IsLaguerrePolya f) (hf0 : f ≠ 0) :
    IsClosed (f ⁻¹' {0}) ∧ IsDiscrete (f ⁻¹' {0}) := by
  obtain ⟨z, hz⟩ : ∃ z, f z ≠ 0 := by
    by_contra h
    apply hf0
    funext z
    by_contra hz
    exact h ⟨z, hz⟩
  rw [← compl_mem_codiscrete_iff]
  simpa only [Set.preimage_compl] using
    hf.analyticOnNhd.preimage_zero_mem_codiscrete (x := z) hz

/-- The zero-aware Laguerre--Pólya class is closed under the complex derivative. -/
theorem IsLaguerrePolya.deriv {f : ℂ → ℂ} (hf : IsLaguerrePolya f) :
    IsLaguerrePolya (deriv f) := by
  rcases hf with ⟨p, hp, hptend⟩
  refine ⟨fun n => (p n).derivative, fun n =>
    eq_zero_or_splits_derivative (hp n), ?_⟩
  have hderiv := (tendstoLocallyUniformlyOn_univ.mpr hptend).deriv
    (Eventually.of_forall fun n =>
      (Polynomial.differentiable ((p n).map Complex.ofRealHom)).differentiableOn)
    isOpen_univ
  rw [tendstoLocallyUniformlyOn_univ] at hderiv
  convert hderiv using 1
  ext n z
  simp only [Function.comp_apply, Polynomial.deriv, ← Polynomial.derivative_map]

end RealRooted
