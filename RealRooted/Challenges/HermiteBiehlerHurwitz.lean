import RealRooted.HurwitzMatrix

/-!
# Hermite--Biehler and Hurwitz challenge entry point

Human statements:

* Hermite--Biehler:
  https://www.symmetricfunctions.com/realRootedInterlacing.htm#hermiteBiehlerTheorem
* Hurwitz--Lace criterion:
  https://www.symmetricfunctions.com/realRootedInterlacing.htm#hurwitzLaceCriterion

Classical references include C. Hermite, A. Hurwitz, M. G. Krein, M. A. Naimark,
and the modern account by O. Holtz, "Hermite-Biehler, Routh-Hurwitz, and
total positivity", Linear Algebra Appl. 372 (2003), 105--110.

This module exposes the checked Hermite--Biehler theorems and the refutation of
the proposed Hurwitz criterion for the project's row-oriented matrix. The
analytic stability bridges and finite-minor plumbing remain in
`RealRooted.HermiteBiehler` and `RealRooted.HurwitzMatrix`.
-/

namespace RealRooted
namespace Challenges
namespace HermiteBiehlerHurwitz

/-- Challenge-facing name for the sign-normalized forward Hermite--Biehler
target. -/
abbrev HermiteBiehlerForwardTarget : Prop :=
  RealRooted.hermiteBiehlerForwardPosStatement

/-- Challenge-facing name for the converse Hermite--Biehler target. -/
abbrev HermiteBiehlerConverseTarget : Prop :=
  RealRooted.hermiteBiehlerConverseStatement

/-- Challenge-facing name for the proposed row-oriented Hurwitz-matrix
total-nonnegativity criterion. -/
abbrev HurwitzMatrixCriterionTarget : Prop :=
  RealRooted.HurwitzMatrixCriterionStatement

/-- Sign-normalized forward Hermite--Biehler target. -/
theorem hermiteBiehler_forward :
    HermiteBiehlerForwardTarget :=
  RealRooted.hermiteBiehlerForwardPos

/-- Converse Hermite--Biehler target. -/
theorem hermiteBiehler_converse :
    HermiteBiehlerConverseTarget :=
  @RealRooted.hermiteBiehlerConverse

/-- The proposed criterion is false for the row orientation used by
`RealRooted.hurwitz`. -/
theorem not_hurwitzMatrixCriterion :
    ¬ HurwitzMatrixCriterionTarget :=
  RealRooted.not_hurwitzMatrixCriterionStatement

end HermiteBiehlerHurwitz
end Challenges
end RealRooted
