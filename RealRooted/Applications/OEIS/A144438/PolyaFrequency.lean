import RealRooted.Applications.OEIS.A144438.Weighted
import RealRooted.PFPolynomial

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
  IsPFPolynomial.of_realRooted_nonneg
    (weightedDecoEulerian_hasNonnegCoeffs hw n)
    (weightedDecoEulerian_splits hw n)

/-- Every recurrence-defined Deco Eulerian polynomial is Pólya-frequency. -/
theorem decoEulerian_isPFPolynomial (n : Nat) :
    IsPFPolynomial (decoEulerian n) := by
  rw [← weightedDecoEulerian_one_weight n]
  exact weightedDecoEulerian_isPFPolynomial (by norm_num) n

/-- The algebraic A144438 facade is Pólya-frequency at every rank. -/
theorem A144438_isPFPolynomial (n : Nat) :
    IsPFPolynomial (A144438 n) :=
  decoEulerian_isPFPolynomial n

end

end RealRooted.Applications.OEIS
