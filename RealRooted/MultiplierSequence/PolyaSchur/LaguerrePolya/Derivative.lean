import RealRooted.Derivative.FamilyClosure
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# Holomorphic Laguerre--Pólya limits

This opt-in analytic leaf proves that zero-aware Laguerre--Pólya limits are
holomorphic, and that the class is closed under the complex derivative.  It
combines derivative closure for real-splitting polynomials with Mathlib's
locally uniform convergence theorems for complex holomorphic functions.  It
does not prove analytic root closure of arbitrary locally uniform limits.
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
