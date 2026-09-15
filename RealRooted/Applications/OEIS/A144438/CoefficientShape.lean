import RealRooted.Applications.OEIS.A144438.PolyaFrequency
import RealRooted.PFPolynomial.CoefficientShape

/-!
# Coefficient shape of the A144438 recurrence family

This opt-in module derives coefficient-shape consequences from the
Pólya-frequency certificates.  It uses only the algebraic recurrence family;
no combinatorial interpretation of A144438 or of the weight is assumed.
-/

namespace RealRooted.Applications.OEIS

noncomputable section

/-- Nonnegative-weight Deco Eulerian polynomials are ultra-log-concave. -/
theorem weightedDecoEulerian_hasUltraLogConcaveCoeffs {w : Real}
    (hw : 0 ≤ w) (n : Nat) :
    HasUltraLogConcaveCoeffs (weightedDecoEulerian w n) :=
  (weightedDecoEulerian_isPFPolynomial hw n).hasUltraLogConcaveCoeffs

/-- Nonnegative-weight Deco Eulerian polynomials have no internal coefficient
zeros. -/
theorem weightedDecoEulerian_hasNoInternalCoeffZeros {w : Real}
    (hw : 0 ≤ w) (n : Nat) :
    HasNoInternalCoeffZeros (weightedDecoEulerian w n) :=
  (weightedDecoEulerian_isPFPolynomial hw n).hasNoInternalCoeffZeros

/-- Nonnegative-weight Deco Eulerian polynomials are log-concave. -/
theorem weightedDecoEulerian_hasLogConcaveCoeffs {w : Real}
    (hw : 0 ≤ w) (n : Nat) :
    HasLogConcaveCoeffs (weightedDecoEulerian w n) :=
  (weightedDecoEulerian_isPFPolynomial hw n).hasLogConcaveCoeffs

/-- Nonnegative-weight Deco Eulerian polynomials are unimodal. -/
theorem weightedDecoEulerian_hasUnimodalCoeffs {w : Real}
    (hw : 0 ≤ w) (n : Nat) :
    HasUnimodalCoeffs (weightedDecoEulerian w n) :=
  (weightedDecoEulerian_isPFPolynomial hw n).hasUnimodalCoeffs

/-- Every A144438 polynomial has ultra-log-concave coefficients. -/
theorem A144438_hasUltraLogConcaveCoeffs (n : Nat) :
    HasUltraLogConcaveCoeffs (A144438 n) :=
  (A144438_isPFPolynomial n).hasUltraLogConcaveCoeffs

/-- Every A144438 polynomial has no internal coefficient zeros. -/
theorem A144438_hasNoInternalCoeffZeros (n : Nat) :
    HasNoInternalCoeffZeros (A144438 n) :=
  (A144438_isPFPolynomial n).hasNoInternalCoeffZeros

/-- Every A144438 polynomial has log-concave coefficients. -/
theorem A144438_hasLogConcaveCoeffs (n : Nat) :
    HasLogConcaveCoeffs (A144438 n) :=
  (A144438_isPFPolynomial n).hasLogConcaveCoeffs

/-- Every A144438 polynomial has unimodal coefficients. -/
theorem A144438_hasUnimodalCoeffs (n : Nat) :
    HasUnimodalCoeffs (A144438 n) :=
  (A144438_isPFPolynomial n).hasUnimodalCoeffs

end

end RealRooted.Applications.OEIS
