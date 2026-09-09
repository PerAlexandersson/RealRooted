import RealRooted.ClassicalHurwitzMatrix
import RealRooted.ClassicalHurwitzMatrix.Stability.WeakConverse
import RealRooted.HurwitzMatrix
import RealRooted.Mathlib.LinearAlgebra.Matrix.Hurwitz.Determinant

open Polynomial

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

This module exposes the checked Hermite--Biehler theorems, the refutation of the
proposed Hurwitz criterion for the project's row-oriented matrix, and finite
regressions for the corrected classical convention. The analytic stability
bridges and finite-minor plumbing remain in `RealRooted.HermiteBiehler` and
`RealRooted.HurwitzMatrix`.
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

/-! ### Corrected-convention acceptance regressions -/

/-- Challenge-facing form of the corrected classical Hurwitz criterion for
nonzero real polynomials. -/
theorem classicalHurwitzCriterion {p : ℝ[X]} (hp : p ≠ 0) :
    RealRooted.IsHurwitzStable p ↔
      (Matrix.hurwitz p.coeff).IsTotallyNonneg :=
  RealRooted.isHurwitzStable_iff_hurwitz_isTotallyNonneg hp

/-- The stable linear-pair example rejected by the historical Lace orientation
has a totally nonnegative corrected classical Hurwitz matrix. -/
theorem classicalHurwitzLinearPair_isTotallyNonneg :
    (Matrix.hurwitz
      (RealRooted.oddEvenPolynomial
        (Polynomial.X + Polynomial.C (2 : ℝ))
        (Polynomial.X + Polynomial.C (1 : ℝ))).coeff).IsTotallyNonneg := by
  apply Matrix.hurwitz_isTotallyNonneg_of_hurwitzStable
  apply RealRooted.nonnegPrecToHurwitzOddEven_of_hermiteBiehlerPos
    @RealRooted.hermiteBiehlerForwardPos
    @RealRooted.hermiteBiehlerStableToHurwitzOddEven
  · exact RealRooted.hasNonnegCoeffs_X_add_C (by norm_num)
  · exact RealRooted.hasNonnegCoeffs_X_add_C (by norm_num)
  · rw [RealRooted.prec_X_add_C_iff]
    norm_num

/-- The corrected minor of the stored parity-swapped binomial sequence on
rows `[1, 2]` and columns `[8, 9]` has determinant `-16`. -/
theorem classicalHurwitzCexA_minor :
    ((Matrix.hurwitz RealRooted.cexA).submatrix ![1, 2] ![8, 9]).det = -16 := by
  have h18 : Matrix.hurwitz RealRooted.cexA 1 8 = 120 := by
    norm_num [Matrix.hurwitz, RealRooted.cexA, RealRooted.cexFirstColumn,
      Nat.choose]
  have h19 : Matrix.hurwitz RealRooted.cexA 1 9 = 1 := by
    norm_num [Matrix.hurwitz, RealRooted.cexA, RealRooted.cexFirstColumn]
  have h28 : Matrix.hurwitz RealRooted.cexA 2 8 = 16 := by
    norm_num [Matrix.hurwitz, RealRooted.cexA, RealRooted.cexFirstColumn]
  have h29 : Matrix.hurwitz RealRooted.cexA 2 9 = 0 := by
    norm_num [Matrix.hurwitz, RealRooted.cexA, RealRooted.cexFirstColumn]
  rw [Matrix.det_fin_two]
  simp only [Matrix.submatrix_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  rw [h18, h19, h28, h29]
  norm_num

/-- The corrected classical Hurwitz matrix rejects the stored parity-swapped
binomial sequence. -/
theorem not_classicalHurwitzCexA_isTotallyNonneg :
    ¬ (Matrix.hurwitz RealRooted.cexA).IsTotallyNonneg := by
  intro h
  have hminor := h (rows := ![1, 2]) (cols := ![8, 9]) (by decide) (by decide)
  rw [classicalHurwitzCexA_minor] at hminor
  norm_num at hminor

/-- The stored odd-zero sequence is the coefficient sequence of `1 + X²`. -/
theorem cexOddZero_eq_one_add_X_sq_coeff :
    RealRooted.cexOddZero = (1 + Polynomial.X ^ 2 : ℝ[X]).coeff := by
  funext n
  match n with
  | 0 =>
      norm_num [RealRooted.cexOddZero, Polynomial.coeff_add,
        Polynomial.coeff_X_pow, Polynomial.coeff_one]
  | 1 =>
      norm_num [RealRooted.cexOddZero, Polynomial.coeff_add,
        Polynomial.coeff_X_pow, Polynomial.coeff_one]
  | n + 2 =>
      by_cases hn : n = 0
      · subst n
        norm_num [RealRooted.cexOddZero, Polynomial.coeff_add,
          Polynomial.coeff_X_pow, Polynomial.coeff_one]
      · simp [RealRooted.cexOddZero, Polynomial.coeff_add,
          Polynomial.coeff_X_pow, Polynomial.coeff_one]

/-- The polynomial `1 + X²` is weakly Hurwitz stable: its two roots lie on the
imaginary-axis boundary. -/
theorem isHurwitzStable_one_add_X_sq :
    RealRooted.IsHurwitzStable (1 + Polynomial.X ^ 2 : ℝ[X]) := by
  refine ⟨?_, ?_⟩
  · intro n
    simp only [Polynomial.coeff_add, Polynomial.coeff_one,
      Polynomial.coeff_X_pow]
    split <;> split <;> norm_num
  · intro z hz hroot
    simp only [RealRooted.complexify, Polynomial.map_add, Polynomial.map_one,
      Polynomial.map_pow, Polynomial.map_X, Polynomial.eval_add,
      Polynomial.eval_one, Polynomial.eval_pow, Polynomial.eval_X] at hroot
    rw [pow_two] at hroot
    have hre := congrArg Complex.re hroot
    have him := congrArg Complex.im hroot
    simp only [Complex.one_re, Complex.add_re, Complex.mul_re,
      Complex.zero_re, Complex.one_im, Complex.add_im, Complex.mul_im,
      Complex.zero_im] at hre him
    have hzim : z.im = 0 := by
      have hprod : z.re * z.im = 0 := by nlinarith
      exact (mul_eq_zero.mp hprod).resolve_left hz.ne'
    rw [hzim] at hre
    nlinarith

/-- The corrected classical Hurwitz matrix accepts the stored `1 + X²`
imaginary-axis boundary example. -/
theorem classicalHurwitzCexOddZero_isTotallyNonneg :
    (Matrix.hurwitz RealRooted.cexOddZero).IsTotallyNonneg := by
  rw [cexOddZero_eq_one_add_X_sq_coeff]
  exact Matrix.hurwitz_isTotallyNonneg_of_hurwitzStable
    isHurwitzStable_one_add_X_sq

/-- The corrected Hurwitz matrix of the zero polynomial is totally
nonnegative, so the nonzero hypothesis in the equivalence is essential. -/
theorem classicalHurwitzZero_isTotallyNonneg :
    (Matrix.hurwitz (0 : ℝ[X]).coeff).IsTotallyNonneg := by
  simpa using Matrix.hurwitz_C_isTotallyNonneg (0 : ℝ) (by norm_num)

/-- The zero polynomial is not weakly Hurwitz stable. -/
theorem not_isHurwitzStable_zero :
    ¬ RealRooted.IsHurwitzStable (0 : ℝ[X]) := by
  intro h
  exact h.rightHalfPlaneStable 1 (by norm_num)
    (by simp [RealRooted.complexify])

/-- The polynomial `X` is weakly Hurwitz stable, with its root on the boundary.
-/
theorem isHurwitzStable_X :
    RealRooted.IsHurwitzStable (Polynomial.X : ℝ[X]) := by
  refine ⟨RealRooted.hasNonnegCoeffs_X, ?_⟩
  intro z hz hroot
  simp [RealRooted.complexify] at hroot
  subst z
  norm_num at hz

/-- The corrected classical Hurwitz matrix accepts the zero-constant boundary
example `X`. -/
theorem classicalHurwitzX_isTotallyNonneg :
    (Matrix.hurwitz (Polynomial.X : ℝ[X]).coeff).IsTotallyNonneg :=
  Matrix.hurwitz_isTotallyNonneg_of_hurwitzStable isHurwitzStable_X

end HermiteBiehlerHurwitz
end Challenges
end RealRooted
