import RealRooted.VeroneseSection

open Polynomial Matrix

noncomputable section

namespace RealRooted

/-!
# Hurwitz matrix criterion interface

This file records checked interface lemmas for the Hurwitz-matrix worker.  The
classical analytic theorem is not proved here; the point is to expose the exact
finite-minor statement needed by the existing `VeroneseSection` route.
-/

@[simp] theorem hurwitz_coeff_even_row (p : ℝ[X]) (i j : ℕ) :
    hurwitz (fun k => p.coeff k) (2 * i) j = toeplitz (fun k => p.coeff (2 * k + 1)) i j := by
  simp [hurwitz]

@[simp] theorem hurwitz_coeff_odd_row (p : ℝ[X]) (i j : ℕ) :
    hurwitz (fun k => p.coeff k) (2 * i + 1) j = toeplitz (fun k => p.coeff (2 * k)) i j := by
  simp [hurwitz, show (2 * i + 1) / 2 = i by lia]

theorem hurwitz_coeff_even_row_apply (p : ℝ[X]) (i j : ℕ) :
    hurwitz (fun k => p.coeff k) (2 * i) j = if j ≤ i then p.coeff (2 * (i - j) + 1) else 0 := by
  simp [toeplitz, hurwitz_coeff_even_row]

theorem hurwitz_coeff_odd_row_apply (p : ℝ[X]) (i j : ℕ) :
    hurwitz (fun k => p.coeff k) (2 * i + 1) j = if j ≤ i then p.coeff (2 * (i - j)) else 0 := by
  simp [toeplitz, hurwitz_coeff_odd_row]

/-- Unfolded finite-minor form of
`HurwitzStableToMatrixTotallyNonnegativeStatement`.

This is the statement to target if one proves the classical theorem directly
from determinant formulas: every finite minor of the row-oriented Hurwitz
matrix attached to a Hurwitz-stable polynomial is nonnegative. -/
def HurwitzStableToHurwitzMatrixMinorsStatement : Prop :=
  ∀ {p : ℝ[X]}, IsHurwitzStable p → (hurwitz p.coeff).IsTotallyNonneg

theorem hurwitzStableToMatrixTotallyNonnegativeStatement_iff_minors :
    HurwitzStableToMatrixTotallyNonnegativeStatement ↔
      HurwitzStableToHurwitzMatrixMinorsStatement := by
  rfl

/-- Reverse direction of the classical total-nonnegativity criterion, kept as a
separate interface because the current Veronese route only needs the forward
direction. -/
def HurwitzMatrixTotallyNonnegativeToStableStatement : Prop :=
  ∀ ⦃p : ℝ[X]⦄, (hurwitz p.coeff).IsTotallyNonneg → IsHurwitzStable p

/-- The converse Hurwitz-matrix criterion gives the converse odd/even Lace
bridge by the explicit Hurwitz/Lace matrix identity. -/
theorem fullyInterlacingPairToHurwitzOddEvenStable_of_matrixTNN
    (hMatrix : HurwitzMatrixTotallyNonnegativeToStableStatement) :
    FullyInterlacingPairToHurwitzOddEvenStableStatement :=
  fun {p q} hfull =>
    hMatrix
      ((hurwitzMatrixTotallyNonnegative_oddEvenPolynomial_iff_fullyInterlacingPair p q).2
        hfull)

/-- Full weak Hurwitz-matrix criterion in the coefficient-nonnegative
convention used in this project. -/
def HurwitzMatrixCriterionStatement : Prop :=
  HurwitzStableToMatrixTotallyNonnegativeStatement ∧
    HurwitzMatrixTotallyNonnegativeToStableStatement

theorem hurwitzStableToMatrixTotallyNonnegative_of_criterion
    (h : HurwitzMatrixCriterionStatement) :
    HurwitzStableToMatrixTotallyNonnegativeStatement :=
  h.1

theorem hurwitzStableToHurwitzMatrixMinors_of_criterion
    (h : HurwitzMatrixCriterionStatement) :
    HurwitzStableToHurwitzMatrixMinorsStatement :=
  hurwitzStableToMatrixTotallyNonnegativeStatement_iff_minors.1 h.1

theorem hurwitzMatrixTotallyNonnegativeToStable_of_criterion
    (h : HurwitzMatrixCriterionStatement) :
    HurwitzMatrixTotallyNonnegativeToStableStatement :=
  h.2

theorem fullyInterlacingPairToHurwitzOddEvenStable_of_criterion
    (h : HurwitzMatrixCriterionStatement) :
    FullyInterlacingPairToHurwitzOddEvenStableStatement :=
  fullyInterlacingPairToHurwitzOddEvenStable_of_matrixTNN
    (hurwitzMatrixTotallyNonnegativeToStable_of_criterion h)

theorem hurwitzOddEvenToFullyInterlacingPair_of_matrixMinors
    (h : HurwitzStableToHurwitzMatrixMinorsStatement) :
    HurwitzOddEvenToFullyInterlacingPairStatement :=
  hurwitzOddEvenToFullyInterlacingPair_of_matrixTNN
    (hurwitzStableToMatrixTotallyNonnegativeStatement_iff_minors.2 h)

theorem hurwitzOddEvenToFullyInterlacingPair_of_criterion
    (h : HurwitzMatrixCriterionStatement) :
    HurwitzOddEvenToFullyInterlacingPairStatement :=
  hurwitzOddEvenToFullyInterlacingPair_of_matrixMinors
    (hurwitzStableToHurwitzMatrixMinors_of_criterion h)

end RealRooted
