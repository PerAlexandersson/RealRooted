/-
# Common-interleaver statement aliases

Shared positive-combination statement aliases used by the CommonInterleaverTwo
converse package and its extracted submodules.
-/
import RealRooted.AllCombo

open Polynomial

noncomputable section

namespace RealRooted

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
    ∃ h : ℝ[X], StrictInterl f h ∧ StrictInterl g h

/-- Repaired succ-degree no-common target for the Chudnovsky--Seymour bridge
in the nonnegative regime: when the right degree is exactly one larger, the
needed conclusion is the existence of a common interleaver, not a fixed
orientation between `f` and `g`. -/
def PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement : Prop :=
  ∀ ⦃f g : ℝ[X]⦄,
    HasPosLeadingCoeff f →
    HasPosLeadingCoeff g →
    HasNonnegCoeffs f →
    HasNonnegCoeffs g →
    PosComboRealRooted f g →
    g.natDegree = f.natDegree + 1 →
    (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
    ∃ h : ℝ[X], StrictInterl f h ∧ StrictInterl g h

end RealRooted
