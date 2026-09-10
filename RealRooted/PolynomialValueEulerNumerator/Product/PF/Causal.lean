import RealRooted.PolynomialValueEulerNumerator.PF.Causal
import RealRooted.PolynomialValueEulerNumerator.Product.PF

/-!
# Product closure from polynomial-value PF hypotheses

This leaf applies the existing canonical-numerator product endpoint after
deriving its two numerator certificates by causal iteration.
-/

namespace RealRooted

/-- Pólya-frequency polynomial-value sequences remain Pólya-frequency after
polynomial multiplication. -/
theorem isPolyaFreqSeq_polynomialValueSeq_mul_of_polyaFreqSeq
    {f g : Polynomial ℝ} (hf : IsPolyaFreqSeq (polynomialValueSeq f))
    (hg : IsPolyaFreqSeq (polynomialValueSeq g)) :
    IsPolyaFreqSeq (polynomialValueSeq (f * g)) :=
  isPolyaFreqSeq_polynomialValueSeq_mul_of_eulerNumerators
    (isPFPolynomial_polynomialValueEulerNumerator_of_polyaFreqSeq hf)
    (isPFPolynomial_polynomialValueEulerNumerator_of_polyaFreqSeq hg)

/-- The qualified Wagner closure for polynomial-value Pólya-frequency
sequences. It does not extend to arbitrary Pólya-frequency sequences. -/
theorem IsPolyaFreqSeq.pointwise_mul_of_polynomialValue
    {f g : Polynomial ℝ} (hf : IsPolyaFreqSeq (polynomialValueSeq f))
    (hg : IsPolyaFreqSeq (polynomialValueSeq g)) :
    IsPolyaFreqSeq (polynomialValueSeq (f * g)) :=
  isPolyaFreqSeq_polynomialValueSeq_mul_of_polyaFreqSeq hf hg

end RealRooted
