module

public import RealRooted.Mathlib.NumberTheory.LSeries.RiemannXi.Coefficients
public import RealRooted.BasisTransform.LimitingAppellMoments
import RealRooted.Mathlib.NumberTheory.LSeries.RiemannXi.Positivity
import RealRooted.RiemannHypothesis.TotalPositivity
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.AppellMoments

/-!
# Hankel positivity of logarithmic xi coefficients under RH

For every derivative shift, normalize the square-variable xi function to one
at the origin. Under RH the Newton moments of its ordinary Taylor coefficients
have positive semidefinite Hankel matrices at every positive shift. Equivalently,
these are the signed coefficients of its formal logarithmic derivative.

This specializes the forward Hankel positivity assertion associated with
Sokal's logarithmic-derivative criterion (Appendix A, Proposition 6),
https://doi.org/10.1016/j.jmaa.2022.126432.
-/

public section

open Complex

namespace RealRooted

/-- Under RH every shifted Hankel matrix of the normalized xi Newton moments
is positive semidefinite, for every derivative shift. -/
theorem posSemidef_riemannXiCoeff_limitingAppellMoment
    (hRH : RiemannHypothesis) (s n r : ℕ) :
    Matrix.PosSemidef (fun i j : Fin n =>
      limitingAppellMoment
        (fun k => riemannXiCoeff (s + k) / (k.factorial * riemannXiCoeff s))
        (i.val + j.val + (r + 1))) := by
  have hf := isLaguerrePolyaTypeI_iteratedDeriv_riemannXiTheta hRH s
  have h0 : (iteratedDeriv s riemannXiTheta 0).re ≠ 0 :=
    (riemannXiCoeff_pos s).ne'
  simpa only [riemannXiCoeff, iteratedDeriv_eq_iterate,
    ← Function.iterate_add_apply, Nat.add_comm] using
    hf.posSemidef_limitingAppellMoment h0 n r

/-- Under RH the signed logarithmic coefficients of each normalized xi
derivative have positive semidefinite Hankel matrices at all positive shifts. -/
theorem posSemidef_riemannXiCoeff_logOf
    (hRH : RiemannHypothesis) (s n r : ℕ) :
    Matrix.PosSemidef (fun i j : Fin n =>
      let k := i.val + j.val + (r + 1)
      (-1 : ℝ) ^ (k + 1) * k * PowerSeries.coeff k (PowerSeries.logOf
        (PowerSeries.mk
          (fun j => riemannXiCoeff (s + j) / (j.factorial * riemannXiCoeff s))))) := by
  have hf := isLaguerrePolyaTypeI_iteratedDeriv_riemannXiTheta hRH s
  have h0 : (iteratedDeriv s riemannXiTheta 0).re ≠ 0 :=
    (riemannXiCoeff_pos s).ne'
  simpa only [riemannXiCoeff, iteratedDeriv_eq_iterate,
    ← Function.iterate_add_apply, Nat.add_comm] using
    hf.posSemidef_signed_coeff_logOf h0 n r

end RealRooted
