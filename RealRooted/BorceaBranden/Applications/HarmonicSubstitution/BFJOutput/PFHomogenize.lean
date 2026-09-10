import RealRooted.Basic.Coefficients.Multivariate
import RealRooted.BorceaBranden.Applications.HarmonicSubstitution.BFJOutput.PolyaFrequency
import RealRooted.BorceaBranden.Applications.HomogenizeStable

/-!
# PF certificates for BFJ outputs of homogenized polynomials

This file combines padded-homogenization stability with the coefficient-sign
and stability criterion for the BFJ output.
-/

open Polynomial

namespace RealRooted

noncomputable section

/-- The BFJ output of two padded homogenized PF polynomials is again PF. -/
theorem IsPFPolynomial.bfjOutput_homogenize
    {p q : ℝ[X]} {a b : ℕ}
    (hp : IsPFPolynomial p) (hq : IsPFPolynomial q)
    (ha : p.natDegree ≤ a) (hb : q.natDegree ≤ b) :
    IsPFPolynomial
      (MvPolynomial.bfjOutput (p.homogenize a) (q.homogenize b) b) := by
  by_cases hp0 : p = 0
  · subst p
    simpa [MvPolynomial.bfjOutput, MvPolynomial.bfjCoefficient,
      MvPolynomial.bfjAuxiliary, MvPolynomial.addAuxiliary] using
      IsPFPolynomial.zero
  by_cases hq0 : q = 0
  · subst q
    simpa [MvPolynomial.bfjOutput, MvPolynomial.bfjCoefficient,
      MvPolynomial.bfjAuxiliary, MvPolynomial.harmonicClear] using
      IsPFPolynomial.zero
  exact MvRealStable.bfjOutput_isPF
    (BorceaBranden.homogenize_stable_of_splits_nonpos_of_natDegree_le
      ha hp0 (hp.ne_zero_and_splits hp0).2 hp.roots_nonpos)
    (BorceaBranden.homogenize_stable_of_splits_nonpos_of_natDegree_le
      hb hq0 (hq.ne_zero_and_splits hq0).2 hq.roots_nonpos)
    (Polynomial.isHomogeneous_homogenize q)
    (hp.hasNonnegCoeffs.homogenize a)
    (hq.hasNonnegCoeffs.homogenize b)

end

end RealRooted
