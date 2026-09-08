import RealRooted.ClassicalHurwitzMatrix
import RealRooted.HurwitzMatrix
import RealRooted.Mathlib.LinearAlgebra.Matrix.Hurwitz.Determinant

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

/-- Challenge-facing name for the refuted converse row-oriented
Hurwitz-matrix criterion. -/
abbrev HurwitzMatrixCriterionTarget : Prop :=
  RealRooted.LegacyHurwitzMatrixTotallyNonnegativeToStableStatement

/-- Sign-normalized forward Hermite--Biehler target. -/
theorem hermiteBiehler_forward :
    HermiteBiehlerForwardTarget :=
  RealRooted.hermiteBiehlerForwardPos

/-- Converse Hermite--Biehler target. -/
theorem hermiteBiehler_converse :
    HermiteBiehlerConverseTarget :=
  @RealRooted.hermiteBiehlerConverse

/-- The converse criterion is false for the row orientation used by
`RealRooted.hurwitz`. -/
theorem not_hurwitzMatrixCriterion :
    ¬ HurwitzMatrixCriterionTarget :=
  RealRooted.not_hurwitzMatrixTotallyNonnegativeToStableStatement

/-- For the stored polynomial `X³ + 1`, the order-three leading principal
minor of the classical Hurwitz matrix is `-1`. This is the smallest regression
distinguishing the correct convention from the false Lace-oriented
criterion. -/
theorem classicalHurwitzMatrixCriterionCounterexample_det_three :
    (Matrix.hurwitzLeadingPrincipal
      RealRooted.hurwitzMatrixCriterionCounterexample.coeff 3).det = -1 := by
  norm_num [RealRooted.hurwitzMatrixCriterionCounterexample,
    Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_one]

/-- The corrected classical Hurwitz matrix rejects the stored `X³ + 1`
counterexample by total nonnegativity. -/
theorem not_classicalHurwitzMatrixCriterionCounterexample_isTotallyNonneg :
    ¬(Matrix.hurwitz
      RealRooted.hurwitzMatrixCriterionCounterexample.coeff).IsTotallyNonneg := by
  intro h
  have hminor := h (rows := fun i : Fin 3 => i) (cols := fun i : Fin 3 => i)
    Fin.val_strictMono Fin.val_strictMono
  change 0 ≤ (Matrix.hurwitzLeadingPrincipal
    RealRooted.hurwitzMatrixCriterionCounterexample.coeff 3).det at hminor
  rw [classicalHurwitzMatrixCriterionCounterexample_det_three] at hminor
  norm_num at hminor

/-- The classical and historical Lace-oriented matrices are genuinely
different conventions, already at entry `(0, 0)` for `X³ + 1`. -/
theorem classicalHurwitzMatrixCriterionCounterexample_ne_legacy :
    Matrix.hurwitz RealRooted.hurwitzMatrixCriterionCounterexample.coeff ≠
      RealRooted.hurwitz RealRooted.hurwitzMatrixCriterionCounterexample.coeff := by
  intro h
  have h00 := congrFun (congrFun h 0) 0
  norm_num [Matrix.hurwitz, RealRooted.hurwitz, RealRooted.toeplitz,
    RealRooted.hurwitzMatrixCriterionCounterexample,
    Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_one] at h00

end HermiteBiehlerHurwitz
end Challenges
end RealRooted
