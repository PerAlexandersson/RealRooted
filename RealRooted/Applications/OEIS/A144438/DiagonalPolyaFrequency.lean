import RealRooted.Applications.OEIS.A144438.DiagonalBridge
import RealRooted.Applications.OEIS.A144438.ExactLayerStability
import RealRooted.Applications.OEIS.A144438.PolyaFrequency

/-!
# Pólya-frequency consequences of the A144438 diagonal bridge

This opt-in file packages Pólya-frequency conclusions for diagonal
restrictions.  The underlying recurrence and diagonal-identification modules
remain independent of the heavier Pólya-frequency API.

The total conclusions are univariate: they do not assert stability of either
outer multivariate sum.
-/

namespace RealRooted.Applications.OEIS

noncomputable section

/-- Every individual normalization fiber is Pólya-frequency after diagonal
restriction. -/
theorem diagonal_fiberPolynomial_isPFPolynomial {h : Nat}
    (c : DecoNormalizedCode h) :
    IsPFPolynomial
      (MvPolynomial.diagonal
        (DecoNormalizedCode.fiberPolynomial (R := Real) c)) := by
  simpa only [commonPhaseRestriction_one_eq_diagonal] using
    DecoNormalizedCode.commonPhaseRestriction_fiberPolynomial_isPFPolynomial
      c (fun _ => 1) (fun _ => zero_le_one)

/-- Every dehomogenized exact-history layer is Pólya-frequency after diagonal
restriction. -/
theorem diagonal_decoExactLayerDehomogenized_isPFPolynomial {n : Nat}
    (H : DecoExceptionalHistory (n + 2)) :
    IsPFPolynomial
      (MvPolynomial.diagonal (decoExactLayerDehomogenized H)) := by
  simpa only [commonPhaseRestriction_one_eq_diagonal] using
    commonPhaseRestriction_decoExactLayerDehomogenized_isPFPolynomial
      H (fun _ => 1) (fun _ => zero_le_one)

/-- The diagonalized admissible-code enumerator is Pólya-frequency. -/
theorem diagonal_admissibleCodePolynomial_isPFPolynomial (n : Nat) :
    IsPFPolynomial
      (MvPolynomial.diagonal
        (admissibleCodePolynomial (R := Real) (n + 2))) := by
  rw [diagonal_admissibleCodePolynomial_eq_A144438]
  exact A144438_isPFPolynomial n

/-- The diagonalized normalized-fiber enumerator is Pólya-frequency. -/
theorem diagonal_normalizedFiberPolynomial_isPFPolynomial (n : Nat) :
    IsPFPolynomial
      (MvPolynomial.diagonal
        (normalizedFiberPolynomial (R := Real) (n + 2))) := by
  rw [diagonal_normalizedFiberPolynomial_eq_A144438]
  exact A144438_isPFPolynomial n

end

end RealRooted.Applications.OEIS
