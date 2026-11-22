module

public import RealRooted.Mathlib.NumberTheory.LSeries.RiemannXi.Coefficients
public import RealRooted.AissenSchoenbergWhitneyBase
import RealRooted.RiemannHypothesis
import RealRooted.RiemannHypothesis.TotalPositivity
import RealRooted.Mathlib.NumberTheory.LSeries.RiemannXi.Positivity
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.TotalPositivityConverse

/-!
# The Riemann hypothesis and total positivity

Mathlib's Riemann hypothesis is equivalent to total positivity of the ordinary
Taylor coefficients `γ(k) / k!` of the square-variable xi function. This is the
RH criterion following Theorem C in O. M. Katkova, *Multiple positivity and the
Riemann zeta-function*, arXiv:math/0505174.
-/

public section

namespace RealRooted

/-- RH is equivalent to the Pólya-frequency property of the ordinary xi Taylor
coefficients. The factorial converts exponential Taylor data to ordinary coefficients. -/
theorem riemannHypothesis_iff_isPolyaFreqSeq_riemannXiCoeff :
    RiemannHypothesis ↔ IsPolyaFreqSeq (fun k => riemannXiCoeff k / k.factorial) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · simpa using isPolyaFreqSeq_riemannXiCoeff_div_factorial h 0
  · have htype : IsLaguerrePolyaTypeI riemannXiTheta :=
      (isLaguerrePolyaTypeI_iff_isPolyaFreqSeq differentiable_riemannXiTheta
        (fun k => (ofReal_riemannXiCoeff k).symm)
        (by simpa [riemannXiCoeff] using riemannXiCoeff_pos 0)).mpr h
    exact riemannHypothesis_iff_isLaguerrePolya_riemannXiTheta.mpr htype.toLaguerrePolya

/-- Equivalently, every derivative shift has a Pólya-frequency ordinary Taylor sequence. -/
theorem riemannHypothesis_iff_isPolyaFreqSeq_riemannXiCoeff_shift :
    RiemannHypothesis ↔
      ∀ n, IsPolyaFreqSeq (fun k => riemannXiCoeff (n + k) / k.factorial) := by
  refine ⟨isPolyaFreqSeq_riemannXiCoeff_div_factorial, fun h => ?_⟩
  apply riemannHypothesis_iff_isPolyaFreqSeq_riemannXiCoeff.mpr
  simpa using h 0

end RealRooted
