import RealRooted.Applications.OEIS.A144438.TotalBridge
import RealRooted.Multiaffine

/-!
# Multiaffine structure of the Deco layer total

The ordinary-coordinate total is multiaffine.  The polynomial itself remains
defined by the normal-plus-exceptional recurrence; the proof uses the checked
comparison-bottom enumerator identity, whose summands are squarefree
finite-set monomials.

This structural result is a prerequisite for multiaffine stability criteria.
It does not assert stability of the outer sum.
-/

namespace RealRooted.Applications.OEIS

open scoped BigOperators

noncomputable section

/-- The admissible-code enumerator is multiaffine in its ordinary bottom
coordinates. -/
theorem admissibleCodePolynomial_isMultiaffine {R : Type*} [CommSemiring R]
    [Nontrivial R] (h : Nat) :
    MvPolynomial.IsMultiaffine (admissibleCodePolynomial (R := R) h) := by
  rw [admissibleCodePolynomial]
  apply MvPolynomial.IsMultiaffine.sum
  intro c hc
  unfold MinimumInsertionWord.comparisonBottomMonomial
  unfold MvPolynomial.finsetMonomial
  exact MvPolynomial.IsMultiaffine.prod_X _

/-- The normalized-fiber sum is multiaffine in its ordinary bottom
coordinates. -/
theorem normalizedFiberPolynomial_isMultiaffine {R : Type*} [CommSemiring R]
    [Nontrivial R] (h : Nat) :
    MvPolynomial.IsMultiaffine (normalizedFiberPolynomial (R := R) h) := by
  rw [← admissibleCodePolynomial_eq_normalizedFiberPolynomial]
  exact admissibleCodePolynomial_isMultiaffine h

/-- The recurrence-defined ordinary-coordinate total is multiaffine. -/
theorem decoBottomTotal_isMultiaffine (n : Nat) :
    MvPolynomial.IsMultiaffine (decoBottomTotal n) := by
  rw [← admissibleCodePolynomial_eq_decoBottomTotal]
  exact admissibleCodePolynomial_isMultiaffine (n + 2)

/-- The recurrence-defined ordinary-coordinate total has nonnegative
coefficients. -/
theorem decoBottomTotal_hasNonnegCoeffs (n : Nat) :
    MvPolynomial.HasNonnegCoeffs (decoBottomTotal n) := by
  rw [← rename_dehomogenize_decoLayerTotal_eq_decoBottomTotal]
  exact ((decoLayerTotal_hasNonnegCoeffs n).dehomogenize).rename_of_injective
    (decoLayerBottomEmbedding n).injective

/-- Stability of the homogeneous finite-coordinate layer total is exactly
common-rotation stability of its multiaffine ordinary-coordinate
dehomogenization. -/
theorem decoLayerTotal_mvRealStable_iff_commonRotation_bottomTotal (n : Nat) :
    MvRealStable (decoLayerTotal n) ↔
      MvCommonRotationStable (complexifyMv (decoBottomTotal n)) := by
  have hrename :
      MvPolynomial.rename (decoLayerBottomEmbedding n)
          (complexifyMv (MvPolynomial.dehomogenize (decoLayerTotal n))) =
        complexifyMv (decoBottomTotal n) := by
    have h := congrArg complexifyMv
      (rename_dehomogenize_decoLayerTotal_eq_decoBottomTotal n)
    simpa [complexifyMv, MvPolynomial.map_rename] using h
  rw [← hrename,
    mvCommonRotationStable_rename_iff
      (decoLayerBottomEmbedding n).injective]
  exact mvRealStable_iff_commonRotation_dehomogenize
    (decoLayerTotal_isHomogeneous n)

end

end RealRooted.Applications.OEIS
