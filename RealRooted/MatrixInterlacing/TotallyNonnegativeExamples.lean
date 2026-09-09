import RealRooted.Mathlib.LinearAlgebra.Matrix.TotallyNonneg.Bidiagonal
import RealRooted.MatrixInterlacing.TotallyNonnegative

/-!
# Examples for totally nonnegative interlacing-sequence mixing

These examples exercise square, genuinely rectangular, zero-output-row, and
elementary Jacobi (bidiagonal) instances of the constant-matrix theorem.
-/

open Polynomial

noncomputable section

namespace Matrix

/-- The leading `m × n` rectangle cut out of the infinite identity matrix. -/
def leadingRectangularIdentity (m n : ℕ) : Matrix (Fin m) (Fin n) ℝ :=
  (1 : Matrix ℕ ℕ ℝ).submatrix Fin.val Fin.val

/-- Every leading rectangular identity section is totally nonnegative. -/
theorem leadingRectangularIdentity_isTotallyNonnegRect (m n : ℕ) :
    (leadingRectangularIdentity m n).IsTotallyNonnegRect :=
  (IsTotallyNonneg.one (R := ℝ)).toRect.submatrix
    Fin.val_strictMono Fin.val_strictMono

/-- Every nonnegative lower-bidiagonal TNN matrix, including elementary lower Jacobi factors,
preserves positive-leading interlacing sequences after zero outputs are removed. -/
theorem lowerBidiagonalFin_map_interlacingSeq_of_posLeadingCoeff
    {n : ℕ} (d s : ℕ → ℝ) (hd : ∀ i, 0 ≤ d i) (hs : ∀ i, 0 ≤ s i)
    (fs : List ℝ[X]) (hfs_len : fs.length = n)
    (hfs_real : ∀ p ∈ fs, RealRooted.HasPosLeadingCoeff p ∧ p.Splits)
    (hfs : RealRooted.IsInterlacingSeq fs) :
    RealRooted.IsInterlacingSeq
        ((RealRooted.tnnMatrixAction (lowerBidiagonalFin n d s) fs).filter
          (· ≠ 0)) ∧
      ∀ p ∈
          (RealRooted.tnnMatrixAction (lowerBidiagonalFin n d s) fs).filter
            (· ≠ 0),
        RealRooted.HasPosLeadingCoeff p ∧ p.Splits :=
  (isTotallyNonneg_lowerBidiagonalFin n d s hd hs).toRect
    |>.map_interlacingSeq_of_posLeadingCoeff fs hfs_len hfs_real hfs

end Matrix

namespace RealRooted

/-- A `1 × 1` identity action tests the full theorem on the split singleton
`X - 1`, whose negative constant coefficient prevents direct use of the
nonnegative-coefficient core. -/
theorem tnnMixing_square_singleton_X_sub_one :
    IsInterlacingSeq
        ((tnnMatrixAction (Matrix.leadingRectangularIdentity 1 1)
          [X - C 1]).filter (· ≠ 0)) ∧
      ∀ p ∈
          (tnnMatrixAction (Matrix.leadingRectangularIdentity 1 1)
            [X - C 1]).filter (· ≠ 0),
        HasPosLeadingCoeff p ∧ p.Splits := by
  apply (Matrix.leadingRectangularIdentity_isTotallyNonnegRect 1 1)
    |>.map_interlacingSeq_of_posLeadingCoeff
  · simp
  · intro p hp
    simp only [List.mem_singleton] at hp
    subst p
    constructor
    · exact hasPosLeadingCoeff_X_sub_C 1
    · simpa [sub_eq_add_neg] using
        (isRealRooted_affine_factor (s := 1) (t := -1) zero_lt_one).2
  · simp [IsInterlacingSeq]

/-- The leading `2 × 1` identity rectangle has a zero second row. Its action
keeps the singleton `X - 1` and discards the zero output without changing row
order. -/
theorem tnnMixing_rectangular_zero_row_X_sub_one :
    (tnnMatrixAction (Matrix.leadingRectangularIdentity 2 1) [X - C 1]).filter
        (· ≠ 0) = [X - C 1] ∧
      IsInterlacingSeq
        ((tnnMatrixAction (Matrix.leadingRectangularIdentity 2 1)
          [X - C 1]).filter (· ≠ 0)) := by
  constructor
  · have hne : (X - C (1 : ℝ) : ℝ[X]) ≠ 0 := X_sub_C_ne_zero 1
    have hne' : (X - (1 : ℝ[X]) : ℝ[X]) ≠ 0 := by simpa using hne
    simp [tnnMatrixAction, matPolyAction, constantPolynomialMatrix,
      Matrix.leadingRectangularIdentity, Matrix.submatrix_apply,
      Matrix.one_apply, hne']
  · exact ((Matrix.leadingRectangularIdentity_isTotallyNonnegRect 2 1)
      |>.map_interlacingSeq_of_posLeadingCoeff [X - C 1] (by simp)
        (by
          intro p hp
          simp only [List.mem_singleton] at hp
          subst p
          exact ⟨hasPosLeadingCoeff_X_sub_C 1, by
            simpa [sub_eq_add_neg] using
              (isRealRooted_affine_factor
                (s := 1) (t := -1) zero_lt_one).2⟩)
        (by simp [IsInterlacingSeq])).1

/-- The nontrivial elementary lower Jacobi factor
`[[1, 0], [1, 1]]` sends `[1, X - 1]` to `[1, X]`, exercising both the matrix
orientation and a genuine two-row sum. -/
theorem tnnMixing_lowerJacobi_two :
    tnnMatrixAction
        (Matrix.lowerBidiagonalFin 2 (fun _ => (1 : ℝ)) (fun _ => 1))
        [1, X - C 1] = [1, X] ∧
      IsInterlacingSeq
        (tnnMatrixAction
          (Matrix.lowerBidiagonalFin 2 (fun _ => (1 : ℝ)) (fun _ => 1))
          [1, X - C 1]) := by
  have hreal :
      ∀ p ∈ ([1, X - C 1] : List ℝ[X]),
        HasPosLeadingCoeff p ∧ p.Splits := by
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · simp [HasPosLeadingCoeff]
    · have hp' : p = X - C (1 : ℝ) := List.mem_singleton.mp hp
      subst p
      exact ⟨hasPosLeadingCoeff_X_sub_C 1, by
        simpa [sub_eq_add_neg] using
          (isRealRooted_affine_factor
            (s := 1) (t := -1) zero_lt_one).2⟩
  have hseq : IsInterlacingSeq ([1, X - C 1] : List ℝ[X]) := by
    rw [isInterlacingSeq_iff_pairwise]
    simpa using
      (interlaces_one_linear (p := X - C (1 : ℝ))
        (Polynomial.natDegree_X_sub_C 1)).toPrec
  have hpres := Matrix.lowerBidiagonalFin_map_interlacingSeq_of_posLeadingCoeff
    (n := 2) (fun _ => (1 : ℝ)) (fun _ => 1)
    (fun _ => zero_le_one) (fun _ => zero_le_one)
    [1, X - C 1] (by simp) hreal hseq
  have haction :
      tnnMatrixAction
          (Matrix.lowerBidiagonalFin 2 (fun _ => (1 : ℝ)) (fun _ => 1))
          [1, X - C 1] = [1, X] := by
    simp [tnnMatrixAction, matPolyAction, constantPolynomialMatrix,
      Matrix.lowerBidiagonalFin_apply]
  refine ⟨haction, ?_⟩
  rw [haction] at hpres
  rw [haction]
  simpa using hpres.1

end RealRooted
