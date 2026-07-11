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

open Polynomial

namespace RealRooted
namespace Challenges
namespace HermiteBiehlerHurwitz

/-- Challenge-facing name for the sign-normalized forward Hermite--Biehler
target. -/
def HermiteBiehlerForwardTarget : Prop :=
  ∀ {f g : ℝ[X]},
    RealRooted.HasPosLeadingCoeff f → RealRooted.HasPosLeadingCoeff g → RealRooted.Prec g f →
    RealRooted.IsUpperHalfPlaneStable (RealRooted.hermiteBiehlerPolynomial f g)

/-- Challenge-facing name for the converse Hermite--Biehler target. -/
def HermiteBiehlerConverseTarget : Prop :=
  ∀ {f g : ℝ[X]},
    RealRooted.HasPosLeadingCoeff f → RealRooted.HasPosLeadingCoeff g →
    RealRooted.IsUpperHalfPlaneStable (RealRooted.hermiteBiehlerPolynomial f g) →
    RealRooted.Prec g f ∨ RealRooted.Prec f g

/-- Challenge-facing name for the Hurwitz-matrix total-nonnegativity
criterion. -/
def HurwitzMatrixCriterionTarget : Prop :=
  (∀ ⦃p : ℝ[X]⦄, RealRooted.IsHurwitzStable p →
    (RealRooted.hurwitz p.coeff).IsTotallyNonneg) ∧
  (∀ ⦃p : ℝ[X]⦄, (RealRooted.hurwitz p.coeff).IsTotallyNonneg →
    RealRooted.IsHurwitzStable p)

/-- Sign-normalized forward Hermite--Biehler target. -/
theorem hermiteBiehler_forward :
    HermiteBiehlerForwardTarget :=
  RealRooted.hermiteBiehlerForwardPos

/-- Converse Hermite--Biehler target. -/
theorem hermiteBiehler_converse :
    HermiteBiehlerConverseTarget :=
  @RealRooted.hermiteBiehlerConverse

/-- Hurwitz-matrix total-nonnegativity criterion interface. -/
theorem hurwitzMatrixCriterion :
    HurwitzMatrixCriterionTarget :=
  ⟨RealRooted.hurwitzStableToMatrixTotallyNonnegative_of_criterion,
    RealRooted.hurwitzMatrixTotallyNonnegativeToStable_of_criterion⟩

end HermiteBiehlerHurwitz
end Challenges
end RealRooted
