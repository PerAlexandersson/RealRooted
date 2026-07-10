import RealRooted.HermiteBiehler
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

This module exposes the theorem-shaped interfaces currently used by the
project.  The analytic stability bridges and Hurwitz-matrix finite-minor
plumbing remain in `RealRooted.HermiteBiehler` and `RealRooted.HurwitzMatrix`.
-/

namespace RealRooted
namespace Challenges
namespace HermiteBiehlerHurwitz

/-- Sign-normalized forward Hermite--Biehler target. -/
theorem hermiteBiehler_forward :
    RealRooted.hermiteBiehlerForwardPosStatement := by
  intro f g hf hg hprec
  exact RealRooted.hermiteBiehlerForwardPos hf hg hprec

/-- Converse Hermite--Biehler target. -/
theorem hermiteBiehler_converse :
    RealRooted.hermiteBiehlerConverseStatement := by
  intro f g hf hg hstable
  exact RealRooted.hermiteBiehlerConverse hf hg hstable

/-- Hurwitz-matrix total-nonnegativity criterion interface. -/
theorem hurwitzMatrixCriterion :
    RealRooted.HurwitzMatrixCriterionStatement :=
  ⟨RealRooted.hurwitzStableToMatrixTotallyNonnegative_of_criterion,
    RealRooted.hurwitzMatrixTotallyNonnegativeToStable_of_criterion⟩

end HermiteBiehlerHurwitz
end Challenges
end RealRooted
