import RealRooted.CoefficientShape
import RealRooted.PFPolynomial

/-!
# Coefficient-shape consequences of Pólya-frequency polynomials

This opt-in module packages the standard coefficient consequences of a
Pólya-frequency certificate.  It remains separate from the core PF API so
clients that only need root geometry do not inherit the coefficient-shape
dependency closure.
-/

open Polynomial

namespace RealRooted

namespace IsPFPolynomial

/-- A Pólya-frequency polynomial has ultra-log-concave coefficients. -/
theorem hasUltraLogConcaveCoeffs {p : ℝ[X]} (hp : IsPFPolynomial p) :
    HasUltraLogConcaveCoeffs p :=
  hasUltraLogConcaveCoeffs_of_hasNonnegCoeffs_of_eq_zero_or_splits
    hp.hasNonnegCoeffs hp.eq_zero_or_splits

/-- A Pólya-frequency polynomial has no internal coefficient zeros. -/
theorem hasNoInternalCoeffZeros {p : ℝ[X]} (hp : IsPFPolynomial p) :
    HasNoInternalCoeffZeros p :=
  hasNoInternalCoeffZeros_of_hasNonnegCoeffs_of_eq_zero_or_splits
    hp.hasNonnegCoeffs hp.eq_zero_or_splits

/-- A Pólya-frequency polynomial has log-concave coefficients. -/
theorem hasLogConcaveCoeffs {p : ℝ[X]} (hp : IsPFPolynomial p) :
    HasLogConcaveCoeffs p :=
  hasLogConcaveCoeffs_of_hasNonnegCoeffs_of_eq_zero_or_splits
    hp.hasNonnegCoeffs hp.eq_zero_or_splits

/-- A Pólya-frequency polynomial has unimodal coefficients. -/
theorem hasUnimodalCoeffs {p : ℝ[X]} (hp : IsPFPolynomial p) :
    HasUnimodalCoeffs p :=
  hasUnimodalCoeffs_of_hasNonnegCoeffs_of_eq_zero_or_splits
    hp.hasNonnegCoeffs hp.eq_zero_or_splits

end IsPFPolynomial

end RealRooted
