import RealRooted.Derivative.FamilyClosure
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# Derivatives of Laguerre--Pólya limits

This opt-in analytic leaf proves derivative closure of the zero-aware
Laguerre--Pólya class.  It combines derivative closure for real-splitting
polynomials with Mathlib's locally uniform convergence theorem for complex
derivatives.  It does not prove analytic root closure of arbitrary locally
uniform limits.
-/

open Filter Polynomial Topology

noncomputable section

namespace RealRooted

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
