import RealRooted.Applications.OEIS.A144438
import RealRooted.PFPolynomial

/-!
# Pólya-frequency packaging for the A144438 recurrence

This file combines the independently proved coefficient nonnegativity and
real-rootedness of the recurrence-defined Deco Eulerian polynomials.  The base
recurrence module remains independent of the Pólya-frequency API.
-/

namespace RealRooted.Applications.OEIS

noncomputable section

/-- Every recurrence-defined Deco Eulerian polynomial is Pólya-frequency. -/
theorem decoEulerian_isPFPolynomial (n : Nat) :
    IsPFPolynomial (decoEulerian n) :=
  IsPFPolynomial.of_realRooted_nonneg
    (decoEulerian_hasNonnegCoeffs n) (decoEulerian_splits n)

/-- The algebraic A144438 facade is Pólya-frequency at every rank. -/
theorem A144438_isPFPolynomial (n : Nat) :
    IsPFPolynomial (A144438 n) :=
  decoEulerian_isPFPolynomial n

end

end RealRooted.Applications.OEIS
