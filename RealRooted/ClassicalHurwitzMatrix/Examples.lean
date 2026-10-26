module

public import RealRooted.ClassicalHurwitzMatrix
public import RealRooted.ClassicalHurwitzMatrix.Stability.Closure
public import RealRooted.ClassicalHurwitzMatrix.Stability.CoefficientSigns
public import RealRooted.ClassicalHurwitzMatrix.Stability.Converse
public import RealRooted.HurwitzMatrix
public import RealRooted.Mathlib.LinearAlgebra.Matrix.Hurwitz.Determinant

/-!
# Counterexamples and boundary examples for the Hurwitz criterion

The criterion "the Hurwitz matrix is totally nonnegative" characterizes weak Hurwitz stability
of nonzero real polynomials for the classical matrix `Matrix.hurwitz`
(`RealRooted.isHurwitzStable_iff_hurwitz_isTotallyNonneg`), but fails for the row-oriented
matrix `RealRooted.hurwitz` (`RealRooted.not_forall_isHurwitzStable_of_hurwitz_isTotallyNonneg`).

This module records the finite checks behind that distinction: the classical matrix rejects the
stored counterexamples `X³ + 1` and `RealRooted.cexA` through explicit negative minors,
accepts stable examples rejected by the row orientation, and accepts the boundary examples
`1 + X²` and `X`; the zero polynomial shows that the nonzero hypothesis is needed.
-/

@[expose] public section

open Polynomial

namespace RealRooted

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

/-- The classical and the row-oriented (historical Lace) Hurwitz matrices are genuinely
different conventions, already at entry `(0, 0)` for `X³ + 1`. -/
theorem classicalHurwitzMatrixCriterionCounterexample_ne_row :
    Matrix.hurwitz RealRooted.hurwitzMatrixCriterionCounterexample.coeff ≠
      RealRooted.hurwitz RealRooted.hurwitzMatrixCriterionCounterexample.coeff := by
  intro h
  have h00 := congrFun (congrFun h 0) 0
  norm_num [Matrix.hurwitz, RealRooted.hurwitz, RealRooted.toeplitz,
    RealRooted.hurwitzMatrixCriterionCounterexample,
    Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_one] at h00

/-- The stable linear-pair example rejected by the historical Lace orientation
has a totally nonnegative corrected classical Hurwitz matrix. -/
theorem classicalHurwitzLinearPair_isTotallyNonneg :
    (Matrix.hurwitz
      (RealRooted.oddEvenPolynomial
        (Polynomial.X + 2) (Polynomial.X + 1)).coeff).IsTotallyNonneg := by
  rw [show (Polynomial.X + 2 : ℝ[X]) = Polynomial.X + Polynomial.C 2 by rw [map_ofNat],
    show (Polynomial.X + 1 : ℝ[X]) = Polynomial.X + Polynomial.C 1 by rw [map_one]]
  apply Matrix.hurwitz_isTotallyNonneg_of_hurwitzStable
  apply RealRooted.isHurwitzStable_oddEvenPolynomial_of_strictInterl
  · exact RealRooted.hasNonnegCoeffs_X_add_C (by norm_num)
  · exact RealRooted.hasNonnegCoeffs_X_add_C (by norm_num)
  · rw [RealRooted.StrictInterl.X_add_C_iff]
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
      have hprod : z.re * z.im = 0 := by linarith
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

end RealRooted
