import RealRooted.Applications.OEIS.A144438.ExactLayer
import RealRooted.MultivariateStability.PolyaFrequency

/-!
# Pólya-frequency restrictions of exact A144438 layers

This file combines the independently proved stability and coefficient
nonnegativity of each recurrence-defined exact layer.  It makes no claim
about the sum over different exceptional histories.
-/

namespace RealRooted.Applications.OEIS

noncomputable section

/-- Every nonnegative common-phase restriction of an exact homogeneous layer
is a Pólya-frequency polynomial. -/
theorem commonPhaseRestriction_decoExactLayer_isPFPolynomial {n : Nat}
    (H : DecoExceptionalHistory (n + 2))
    (wt : DecoLayerCoord n → Real) (hwt : ∀ i, 0 ≤ wt i) :
    IsPFPolynomial (commonPhaseRestriction wt (decoExactLayer H)) :=
  (decoExactLayer_mvRealStable H).commonPhaseRestriction_isPFPolynomial
    (decoExactLayer_hasNonnegCoeffs H) wt hwt

/-- Every nonnegative common-phase restriction of a dehomogenized exact layer
is a Pólya-frequency polynomial. -/
theorem commonPhaseRestriction_decoExactLayerDehomogenized_isPFPolynomial
    {n : Nat} (H : DecoExceptionalHistory (n + 2))
    (wt : Fin n → Real) (hwt : ∀ i, 0 ≤ wt i) :
    IsPFPolynomial
      (commonPhaseRestriction wt (decoExactLayerDehomogenized H)) :=
  RealRooted.MvRealStable.commonPhaseRestriction_isPFPolynomial
    (decoExactLayerDehomogenized_mvRealStable H)
    (decoExactLayerDehomogenized_hasNonnegCoeffs H) wt hwt

end

end RealRooted.Applications.OEIS
