/-
# Common-interleaver statement aliases

Shared positive-combination statement aliases used by the CommonInterleaverTwo
converse package and its extracted submodules.
-/
import RealRooted.AllCombo

open Polynomial

noncomputable section

namespace RealRooted

/-- Core two-polynomial target in positive-combination language: a
positive-leading `PosComboRealRooted` pair admits a common right interleaver. -/
def PosComboPairHasCommonInterleaverStatement : Prop :=
  ∀ ⦃f g : ℝ[X]⦄,
    HasPosLeadingCoeff f →
    HasPosLeadingCoeff g →
    PosComboRealRooted f g →
    ∃ h : ℝ[X], Prec f h ∧ Prec g h

/-- Degree-closeness bridge for positive-combination pairs. This is the
remaining degree-only ingredient needed to pass from the no-common-roots
orientation core to a full two-polynomial common-right-interleaver theorem. -/
def PosComboNatDegreeCloseStatement : Prop :=
  ∀ ⦃f g : ℝ[X]⦄,
    PosComboRealRooted f g →
    f.natDegree ≤ g.natDegree + 1 ∧
      g.natDegree ≤ f.natDegree + 1

/-- No-common-roots orientation core for the positive-combination converse.
This matches the local step parameter in
`PosComboRealRooted.prec_or_revPrec_of_posComboRealRooted_of_no_common`. -/
def PosComboNoCommonOrientationStatement : Prop :=
  ∀ ⦃f g : ℝ[X]⦄,
    PosComboRealRooted f g →
    HasPosLeadingCoeff f →
    HasPosLeadingCoeff g →
    f.natDegree ≤ g.natDegree →
    g.natDegree ≤ f.natDegree + 1 →
    (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
    Prec f g ∨ Prec g f

/-- Bridge statement: in the no-common, close-degree setup, positive-combination
real-rootedness upgrades to full all-combinations real-rootedness. -/
def PosComboNoCommonToAllComboBridgeStatement : Prop :=
  ∀ ⦃f g : ℝ[X]⦄,
    HasPosLeadingCoeff f →
    HasPosLeadingCoeff g →
    PosComboRealRooted f g →
    f.natDegree ≤ g.natDegree →
    g.natDegree ≤ f.natDegree + 1 →
    (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
    AllComboRealRooted f g

/-- Stronger no-common bridge hypothesis in the nonnegative regime: instead of
directly asking for `AllComboRealRooted f g`, assume the pair satisfies the
full positive affine family needed by Brändén's converse. This isolates the
remaining missing step as an affine-family packaging problem. -/
def PosComboNoCommonAffineFamilyStatement : Prop :=
  ∀ ⦃f g : ℝ[X]⦄,
    HasPosLeadingCoeff f →
    HasPosLeadingCoeff g →
    HasNonnegCoeffs f →
    HasNonnegCoeffs g →
    PosComboRealRooted f g →
    f.natDegree ≤ g.natDegree →
    g.natDegree ≤ f.natDegree + 1 →
    (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
    ∀ ⦃s t : ℝ⦄, 0 < s → 0 < t →
      ((((C s * X + C t) * f) + g) ≠ 0 ∧ (((C s * X + C t) * f) + g).Splits)

/-- Stronger boundary-right-pair hypothesis in the nonnegative no-common
regime: for each boundary member `C t * f + g`, orient the right-hand pair
against `X * f`.  This is a useful conditional route to the affine family, not
the current endpoint for the packet proof. -/
def PosComboNoCommonBoundaryRightPairOrientationStatement : Prop :=
  ∀ ⦃f g : ℝ[X]⦄,
    HasPosLeadingCoeff f →
    HasPosLeadingCoeff g →
    HasNonnegCoeffs f →
    HasNonnegCoeffs g →
    PosComboRealRooted f g →
    f.natDegree ≤ g.natDegree →
    g.natDegree ≤ f.natDegree + 1 →
    (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
    ∀ ⦃t : ℝ⦄, 0 < t →
      Prec (C t * f + g) (X * f) ∨ Prec (X * f) (C t * f + g)

/-- Strong shifted-pair formulation for the same-degree no-common branch after
the affine/boundary counterexample.  It remains a named conditional hypothesis;
the downstream bridge now uses the common-right-interleaver target below as the
weaker endpoint. -/
def PosComboNoCommonSameDegreeShiftedPairOrientationStatement : Prop :=
  ∀ ⦃f g : ℝ[X]⦄,
    HasPosLeadingCoeff f →
    HasPosLeadingCoeff g →
    HasNonnegCoeffs f →
    HasNonnegCoeffs g →
    PosComboRealRooted f g →
    g.natDegree = f.natDegree →
    (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
    Prec f (g + X * f)

/-- Legacy fixed-orientation same-degree target in the nonnegative no-common
regime.  It is retained for older reductions, but the repaired bridge no
longer treats this as the required same-degree endpoint. -/
def PosComboNoCommonSameDegreeOrientationNonnegStatement : Prop :=
  ∀ ⦃f g : ℝ[X]⦄,
    HasPosLeadingCoeff f →
    HasPosLeadingCoeff g →
    HasNonnegCoeffs f →
    HasNonnegCoeffs g →
    PosComboRealRooted f g →
    g.natDegree = f.natDegree →
    (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
    Prec f g

/-- Strong same-degree no-common alternative in the nonnegative regime.  This
weakens the fixed orientation, but it is still stronger than the repaired
common-right-interleaver endpoint below. -/
def PosComboNoCommonSameDegreeOrientationAlternativeNonnegStatement : Prop :=
  ∀ ⦃f g : ℝ[X]⦄,
    HasPosLeadingCoeff f →
    HasPosLeadingCoeff g →
    HasNonnegCoeffs f →
    HasNonnegCoeffs g →
    PosComboRealRooted f g →
    g.natDegree = f.natDegree →
    (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
    Prec f g ∨ Prec g f

/-- Repaired same-degree no-common target in the nonnegative regime. The
orientation alternative is too strong in degree `2`; for the
Chudnovsky--Seymour bridge the needed conclusion is only a common right
interleaver. -/
def PosComboNoCommonSameDegreePairHasCommonInterleaverNonnegStatement : Prop :=
  ∀ ⦃f g : ℝ[X]⦄,
    HasPosLeadingCoeff f →
    HasPosLeadingCoeff g →
    HasNonnegCoeffs f →
    HasNonnegCoeffs g →
    PosComboRealRooted f g →
    g.natDegree = f.natDegree →
    (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
    ∃ h : ℝ[X], Prec f h ∧ Prec g h

/-- Fixed-orientation succ-degree target in the nonnegative no-common regime.
This is stronger than what the Chudnovsky--Seymour bridge needs; the repaired
succ-degree endpoint below only asks for a common right interleaver. -/
def PosComboNoCommonSuccDegreeOrientationNonnegStatement : Prop :=
  ∀ ⦃f g : ℝ[X]⦄,
    HasPosLeadingCoeff f →
    HasPosLeadingCoeff g →
    HasNonnegCoeffs f →
    HasNonnegCoeffs g →
    PosComboRealRooted f g →
    g.natDegree = f.natDegree + 1 →
    (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
    Prec f g

/-- Repaired succ-degree no-common target for the Chudnovsky--Seymour bridge
in the nonnegative regime: when the right degree is exactly one larger, the
needed conclusion is the existence of a common interleaver, not a fixed
orientation between `f` and `g`. -/
theorem PosComboNoCommonSuccDegreePairHasCommonInterleaverNonneg :
    ∀ ⦃f g : ℝ[X]⦄,
      HasPosLeadingCoeff f →
      HasPosLeadingCoeff g →
      HasNonnegCoeffs f →
      HasNonnegCoeffs g →
      PosComboRealRooted f g →
      g.natDegree = f.natDegree + 1 →
      (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
      ∃ h : ℝ[X], Prec f h ∧ Prec g h := by
  sorry

end RealRooted
