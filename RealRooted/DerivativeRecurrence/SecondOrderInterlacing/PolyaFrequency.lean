import RealRooted.DerivativeRecurrence.SecondOrderInterlacing
import RealRooted.PFPolynomial

/-!
# Pólya-frequency consequences of second-order recurrence certificates

This opt-in module converts the coefficient and root data already bundled in
an affine-lag second-order recurrence certificate into a Pólya-frequency
certificate.  It remains separate from the recurrence module so clients that
only need root geometry do not inherit the Pólya-frequency dependency closure.
-/

open Polynomial

namespace RealRooted

/-- A certified member of an affine-lag second-order recurrence is a
Pólya-frequency polynomial. -/
theorem AffineLagSecondOrderCertificate.isPFPolynomial
    {P : ℕ → ℝ[X]} {n : ℕ} (h : AffineLagSecondOrderCertificate P n) :
    IsPFPolynomial (P n) :=
  IsPFPolynomial.of_realRooted_nonneg h.nonnegCoeffs h.splits

end RealRooted
