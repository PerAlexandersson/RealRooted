module

public import RealRooted.Mathlib.NumberTheory.LSeries.RiemannXi.Coefficients
public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.TypeI
import RealRooted.RiemannHypothesis
import RealRooted.RiemannHypothesis.MultiplierSequence
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Jensen
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Derivative
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.TotalPositivity

/-!
# Total positivity of xi Taylor coefficients under RH

For every derivative shift `n`, RH implies that the ordinary Taylor sequence
`γ(n + k) / k!` is Pólya-frequency. Thus every minor of its Toeplitz matrix is
nonnegative. This differs from the multiplier-sequence property of `γ` itself.

The unshifted implication is the forward part of the RH criterion recalled in
O. M. Katkova, *Multiple positivity and the Riemann zeta-function*,
https://arxiv.org/abs/math/0505174. The converse is not asserted here.
-/

public section

open Complex

namespace RealRooted

/-- Every derivative of the square-variable xi function is Type-I
Laguerre--Pólya under RH. -/
theorem isLaguerrePolyaTypeI_iteratedDeriv_riemannXiTheta
    (hRH : RiemannHypothesis) (n : ℕ) :
    IsLaguerrePolyaTypeI (iteratedDeriv n riemannXiTheta) := by
  have hf := (riemannHypothesis_iff_isLaguerrePolya_riemannXiTheta.mp hRH).iterate_deriv n
  have hgamma (k : ℕ) : iteratedDeriv k (iteratedDeriv n riemannXiTheta) 0 =
      (riemannXiCoeff (n + k) : ℂ) := by
    simpa only [iteratedDeriv_eq_iterate, ← Function.iterate_add_apply, Nat.add_comm]
      using (ofReal_riemannXiCoeff (n + k)).symm
  rw [eq_complexExpGeneratingFunction_of_iteratedDeriv hf.differentiable hgamma]
  exact IsPFMultiplierSequence.isLaguerrePolyaTypeI_complexExpGeneratingFunction
    (isPFMultiplierSequence_riemannXiCoeff_shift hRH n)

/-- Under RH all Toeplitz minors of every factorial-normalized shifted xi
coefficient sequence are nonnegative. -/
theorem isPolyaFreqSeq_riemannXiCoeff_div_factorial (hRH : RiemannHypothesis) (n : ℕ) :
    IsPolyaFreqSeq (fun k => riemannXiCoeff (n + k) / k.factorial) := by
  simpa only [riemannXiCoeff, iteratedDeriv_eq_iterate,
    ← Function.iterate_add_apply, Nat.add_comm] using
    (isLaguerrePolyaTypeI_iteratedDeriv_riemannXiTheta hRH n).isPolyaFreqSeq

end RealRooted
