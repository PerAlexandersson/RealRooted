import RealRooted.PFPolynomial
import RealRooted.PolynomialValueEulerNumerator
import RealRooted.PolyaFrequencyConvolution.Basic
import RealRooted.PolyaFrequencyConvolution.InverseOneSubPow

/-!
# Pólya-frequency consequence of an Euler-numerator certificate

This file turns a PF certificate for the canonical Euler numerator of a
polynomial-value sequence into a PF certificate for the sequence itself.
-/

open Polynomial

namespace RealRooted

/-- Polynomial values are the Cauchy convolution of the coefficients of their
canonical Euler numerator with the appropriate inverse-power kernel. -/
theorem polynomialValueSeq_eq_eulerNumeratorCoeff_convolution (p : ℝ[X]) :
    polynomialValueSeq p =
      natCauchyConvolution (fun n => (polynomialValueEulerNumerator p).coeff n)
        (invOneSubPowCoeff p.natDegree) := by
  funext n
  have h := congrArg (PowerSeries.coeff n)
    (polynomialValueSeries_eq_eulerNumerator_mul_invOneSubPow p)
  rw [PowerSeries.coeff_mk, coeff_mul_eq_natCauchyConvolution] at h
  simpa only [Polynomial.coeff_coe, coeff_invOneSubPow_val_succ] using h

/-- A PF canonical Euler numerator certifies that the associated
polynomial-value sequence is PF. -/
theorem isPolyaFreqSeq_polynomialValueSeq_of_eulerNumerator
    {p : ℝ[X]} (h : IsPFPolynomial (polynomialValueEulerNumerator p)) :
    IsPolyaFreqSeq (polynomialValueSeq p) := by
  rw [polynomialValueSeq_eq_eulerNumeratorCoeff_convolution]
  exact h.to_sequence.natCauchyConvolution
    (invOneSubPowCoeff_isPolyaFreqSeq p.natDegree)

end RealRooted
