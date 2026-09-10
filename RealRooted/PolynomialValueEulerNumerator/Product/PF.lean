import RealRooted.BorceaBranden.Applications.HarmonicSubstitution.BFJOutput.PFHomogenize
import RealRooted.PolynomialValueEulerNumerator.Product

/-!
# PF closure for products of polynomial-value Euler numerators

This file applies the BFJ construction to the canonical Euler numerators and
records the resulting PF certificate for polynomial-value sequences.

The input PF hypotheses here concern the canonical numerators themselves, not
only their polynomial-value sequences. Deriving numerator certificates from
sequence PF hypotheses is the separate converse still tracked by issue #591.
-/

open Polynomial

namespace RealRooted

noncomputable section

/-- Canonical Euler numerators with PF certificates remain PF under
polynomial multiplication. -/
theorem IsPFPolynomial.polynomialValueEulerNumerator_mul
    {f g : ℝ[X]}
    (hf : IsPFPolynomial (polynomialValueEulerNumerator f))
    (hg : IsPFPolynomial (polynomialValueEulerNumerator g)) :
    IsPFPolynomial (polynomialValueEulerNumerator (f * g)) := by
  rw [← bfjOutput_homogenize_polynomialValueEulerNumerator_eq]
  exact hf.bfjOutput_homogenize hg
    (natDegree_polynomialValueEulerNumerator_le f)
    (natDegree_polynomialValueEulerNumerator_le g)

/-- PF certificates for two canonical Euler numerators certify the
polynomial-value sequence of their product. -/
theorem isPolyaFreqSeq_polynomialValueSeq_mul_of_eulerNumerators
    {f g : ℝ[X]}
    (hf : IsPFPolynomial (polynomialValueEulerNumerator f))
    (hg : IsPFPolynomial (polynomialValueEulerNumerator g)) :
    IsPolyaFreqSeq (polynomialValueSeq (f * g)) :=
  isPolyaFreqSeq_polynomialValueSeq_of_eulerNumerator
    (hf.polynomialValueEulerNumerator_mul hg)

end

end RealRooted
