import RealRooted.Applications.OEIS.A144438.Weighted
import RealRooted.DerivativeRecurrence.SecondOrderInterlacing.PolyaFrequency

/-!
# Pólya-frequency packaging for the A144438 recurrence

This file combines the independently proved coefficient nonnegativity and
real-rootedness of the recurrence-defined Deco Eulerian polynomials.  The base
recurrence module remains independent of the Pólya-frequency API.
-/

namespace RealRooted.Applications.OEIS

noncomputable section

/-- Every nonnegative-weight recurrence-defined Deco Eulerian polynomial is
Pólya-frequency. -/
theorem weightedDecoEulerian_isPFPolynomial {w : Real} (hw : 0 ≤ w) (n : Nat) :
    IsPFPolynomial (weightedDecoEulerian w n) :=
  (weightedDecoEulerian_certificate hw n).isPFPolynomial

/-- Every recurrence-defined Deco Eulerian polynomial is Pólya-frequency. -/
theorem decoEulerian_isPFPolynomial (n : Nat) :
    IsPFPolynomial (decoEulerian n) :=
  (decoEulerian_certificate n).isPFPolynomial

/-- The algebraic A144438 facade is Pólya-frequency at every rank. -/
theorem A144438_isPFPolynomial (n : Nat) :
    IsPFPolynomial (A144438 n) :=
  (A144438_certificate n).isPFPolynomial

end

end RealRooted.Applications.OEIS
