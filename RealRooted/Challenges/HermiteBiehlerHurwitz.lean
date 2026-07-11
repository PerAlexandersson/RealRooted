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

open Polynomial

namespace RealRooted
namespace Challenges
namespace HermiteBiehlerHurwitz

/-- Sign-normalized forward Hermite--Biehler target. -/
theorem hermiteBiehler_forward {f g : ℝ[X]}
    (hf : RealRooted.HasPosLeadingCoeff f) (hg : RealRooted.HasPosLeadingCoeff g)
    (hprec : RealRooted.Prec g f) :
    RealRooted.IsUpperHalfPlaneStable (RealRooted.hermiteBiehlerPolynomial f g) :=
  RealRooted.hermiteBiehlerForwardPos hf hg hprec

/-- Converse Hermite--Biehler target. -/
theorem hermiteBiehler_converse {f g : ℝ[X]}
    (hf : RealRooted.HasPosLeadingCoeff f) (hg : RealRooted.HasPosLeadingCoeff g)
    (hstable : RealRooted.IsUpperHalfPlaneStable (RealRooted.hermiteBiehlerPolynomial f g)) :
    RealRooted.Prec g f ∨ RealRooted.Prec f g :=
  RealRooted.hermiteBiehlerConverse hf hg hstable

/-- Hurwitz-matrix total-nonnegativity criterion interface. -/
theorem hurwitzMatrixCriterion :
    RealRooted.HurwitzStableToMatrixTotallyNonnegativeStatement ∧
      RealRooted.HurwitzMatrixTotallyNonnegativeToStableStatement :=
  ⟨RealRooted.hurwitzStableToMatrixTotallyNonnegative_of_criterion,
    RealRooted.hurwitzMatrixTotallyNonnegativeToStable_of_criterion⟩

end HermiteBiehlerHurwitz
end Challenges
end RealRooted
