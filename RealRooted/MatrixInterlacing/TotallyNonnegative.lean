import RealRooted.AffineProperPosition
import RealRooted.InterlacingSequence.NonnegativeShift
import RealRooted.Mathlib.LinearAlgebra.Matrix.TotallyNonneg
import RealRooted.MatrixInterlacing.Preservation

/-!
# Totally nonnegative constant matrices preserve interlacing sequences

This file bridges rectangular total nonnegativity to the existing polynomial
matrix preservation theorem. It first proves the zero-aware algebraic core for
nonnegative-coefficient inputs, then obtains Fisk's positive-leading-
coefficient formulation by translating a finite input family simultaneously.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- Regard a finite real matrix as a row-major list matrix of constant
polynomials. -/
def constantPolynomialMatrix {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    List (List ℝ[X]) :=
  List.ofFn fun i : Fin m => List.ofFn fun j : Fin n => C (A i j)

@[simp] lemma length_constantPolynomialMatrix {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) :
    (constantPolynomialMatrix A).length = m := by
  simp [constantPolynomialMatrix]

@[simp] lemma get_constantPolynomialMatrix {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (i : Fin m) :
    (constantPolynomialMatrix A).get ⟨i, by simp⟩ =
      List.ofFn (fun j : Fin n => C (A i j)) := by
  simp [constantPolynomialMatrix]

lemma constantPolynomialMatrix_rect {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) :
    ∀ row ∈ constantPolynomialMatrix A, row.length = n := by
  simp [constantPolynomialMatrix]

lemma constantPolynomialMatrix_nonneg {m n : ℕ}
    {A : Matrix (Fin m) (Fin n) ℝ} (hA : A.IsTotallyNonnegRect) :
    ∀ row ∈ constantPolynomialMatrix A, ∀ p ∈ row, HasNonnegCoeffs p := by
  simp only [constantPolynomialMatrix, List.forall_mem_ofFn_iff]
  exact fun i j => hasNonnegCoeffs_C (hA.nonneg i j)

/-- Row-ordered action of a finite constant real matrix on a polynomial list. -/
def tnnMatrixAction {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (fs : List ℝ[X]) : List ℝ[X] :=
  matPolyAction (constantPolynomialMatrix A) fs

@[simp] lemma length_tnnMatrixAction {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (fs : List ℝ[X]) :
    (tnnMatrixAction A fs).length = m := by
  simp [tnnMatrixAction]

private lemma zipWith_C_mul_sum_comp_X_add_C
    (as : List ℝ) (fs : List ℝ[X]) (r : ℝ) :
    ((as.map C).zipWith (· * ·) fs).sum.comp (X + C r) =
      ((as.map C).zipWith (· * ·) (fs.map fun p => p.comp (X + C r))).sum := by
  induction as generalizing fs with
  | nil => simp
  | cons a as ih =>
      cases fs with
      | nil => simp
      | cons f fs => simp [ih, add_comp]

/-- A constant matrix action commutes with simultaneous translation of its
polynomial inputs. -/
theorem tnnMatrixAction_map_comp_X_add_C
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (fs : List ℝ[X]) (r : ℝ) :
    tnnMatrixAction A (fs.map fun p => p.comp (X + C r)) =
      (tnnMatrixAction A fs).map fun p => p.comp (X + C r) := by
  simp only [tnnMatrixAction, matPolyAction, constantPolynomialMatrix,
    List.map_map]
  apply List.map_congr_left
  intro row hrow
  rcases List.mem_ofFn.mp hrow with ⟨i, rfl⟩
  simpa [Function.comp_def] using
    (zipWith_C_mul_sum_comp_X_add_C (List.ofFn fun j => A i j) fs r).symm

end RealRooted

namespace Matrix

open RealRooted

/-- Every ordered `2 × 2` selection from a rectangular totally nonnegative
constant matrix satisfies the weak affine condition used by the polynomial
matrix preservation theorem. Repeated rows or columns are allowed. -/
theorem IsTotallyNonnegRect.has2x2InterlacingProperty0
    {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ}
    (hA : A.IsTotallyNonnegRect) (i₁ i₂ : Fin m) (j₁ j₂ : Fin n)
    (hi : i₁ ≤ i₂) (hj : j₁ ≤ j₂) :
    Has2x2InterlacingProperty0
      (C (A i₁ j₁)) (C (A i₁ j₂)) (C (A i₂ j₁)) (C (A i₂ j₂)) := by
  intro s t hs _ht
  apply prec0_const_entries_affine_of_det_nonneg
  · exact hA.nonneg i₁ j₁
  · exact hA.nonneg i₁ j₂
  · exact hA.nonneg i₂ j₁
  · exact hA.nonneg i₂ j₂
  · exact hs
  · by_cases hi_eq : i₁ = i₂
    · subst i₂
      simp [mul_comm]
    by_cases hj_eq : j₁ = j₂
    · subst j₂
      simp
    have hi_lt : i₁ < i₂ := lt_of_le_of_ne hi hi_eq
    have hj_lt : j₁ < j₂ := lt_of_le_of_ne hj hj_eq
    let rows : Fin 2 → Fin m := ![i₁, i₂]
    let cols : Fin 2 → Fin n := ![j₁, j₂]
    have hrows : StrictMono rows := by
      intro a b hab
      fin_cases a <;> fin_cases b <;> simp_all [rows]
    have hcols : StrictMono cols := by
      intro a b hab
      fin_cases a <;> fin_cases b <;> simp_all [cols]
    have hminor := hA hrows hcols
    simp only [Matrix.det_fin_two, Matrix.submatrix_apply, rows, cols,
      Matrix.cons_val_zero, Matrix.cons_val_one] at hminor
    linarith

private lemma IsTotallyNonnegRect.constantPolynomialMatrix_has2x2
    {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ}
    (hA : A.IsTotallyNonnegRect) :
    ∀ (i₁ i₂ : Fin (constantPolynomialMatrix A).length) (j₁ j₂ : Fin n),
      i₁ ≤ i₂ → j₁ ≤ j₂ →
      Has2x2InterlacingProperty0
        (((constantPolynomialMatrix A).get i₁).get
          ⟨j₁, by simp [constantPolynomialMatrix]⟩)
        (((constantPolynomialMatrix A).get i₁).get
          ⟨j₂, by simp [constantPolynomialMatrix]⟩)
        (((constantPolynomialMatrix A).get i₂).get
          ⟨j₁, by simp [constantPolynomialMatrix]⟩)
        (((constantPolynomialMatrix A).get i₂).get
          ⟨j₂, by simp [constantPolynomialMatrix]⟩) := by
  intro i₁ i₂ j₁ j₂ hi hj
  let i₁' : Fin m := ⟨i₁, by simpa [constantPolynomialMatrix] using i₁.isLt⟩
  let i₂' : Fin m := ⟨i₂, by simpa [constantPolynomialMatrix] using i₂.isLt⟩
  have hi' : i₁' ≤ i₂' := by simpa [i₁', i₂'] using hi
  simp only [constantPolynomialMatrix]
  simpa [i₁', i₂'] using
    hA.has2x2InterlacingProperty0 i₁' i₂' j₁ j₂ hi' hj

/-- A rectangular totally nonnegative constant matrix sends a strict
nonnegative interlacing sequence to a weak zero-aware one, in row order. -/
theorem IsTotallyNonnegRect.map_interlacingSeq0
    {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ}
    (hA : A.IsTotallyNonnegRect) (fs : List ℝ[X])
    (hfs_len : fs.length = n) (hfs : IsInterlacingSeqNonneg fs) :
    IsInterlacingSeq0Nonneg (tnnMatrixAction A fs) := by
  change IsInterlacingSeq0Nonneg
    (matPolyAction (constantPolynomialMatrix A) fs)
  exact matrix_preserves_interlacing_seq0_of_2x2
    (n := n) (G := constantPolynomialMatrix A)
    (hG_rect := constantPolynomialMatrix_rect A)
    (hG_nonneg := constantPolynomialMatrix_nonneg hA)
    (hG_affine := hA.constantPolynomialMatrix_has2x2)
    fs hfs_len hfs

/-- Fisk's row-ordered list conclusion in the repository's nonnegative-
coefficient setting: discard precisely the zero output rows after TNN mixing. -/
theorem IsTotallyNonnegRect.map_interlacingSeq
    {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ}
    (hA : A.IsTotallyNonnegRect) (fs : List ℝ[X])
    (hfs_len : fs.length = n) (hfs : IsInterlacingSeqNonneg fs) :
    IsInterlacingSeqNonneg ((tnnMatrixAction A fs).filter (· ≠ 0)) := by
  change IsInterlacingSeqNonneg
    ((matPolyAction (constantPolynomialMatrix A) fs).filter (· ≠ 0))
  exact matrix_preserves_interlacing_seq0_filter_ne_zero_of_2x2
    (n := n) (G := constantPolynomialMatrix A)
    (hG_rect := constantPolynomialMatrix_rect A)
    (hG_nonneg := constantPolynomialMatrix_nonneg hA)
    (hG_affine := hA.constantPolynomialMatrix_has2x2)
    fs hfs_len hfs

/-- Full positive-leading-coefficient form of Fisk's constant-matrix theorem.
Every input is assumed split explicitly, because pairwise interlacing is
vacuous for singleton lists. The nonzero output rows retain positive leading
coefficient and splitness, in addition to forming an interlacing sequence. -/
theorem IsTotallyNonnegRect.map_interlacingSeq_of_posLeadingCoeff
    {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ}
    (hA : A.IsTotallyNonnegRect) (fs : List ℝ[X])
    (hfs_len : fs.length = n)
    (hfs_real : ∀ p ∈ fs, HasPosLeadingCoeff p ∧ p.Splits)
    (hfs : IsInterlacingSeq fs) :
    IsInterlacingSeq ((tnnMatrixAction A fs).filter (· ≠ 0)) ∧
      ∀ p ∈ (tnnMatrixAction A fs).filter (· ≠ 0),
        HasPosLeadingCoeff p ∧ p.Splits := by
  obtain ⟨r, hshift⟩ :=
    exists_comp_X_add_C_isInterlacingSeqNonneg fs hfs_real hfs
  have hshift_len : (fs.map fun p => p.comp (X + C r)).length = n := by
    simpa using hfs_len
  have hout := hA.map_interlacingSeq
    (fs.map fun p => p.comp (X + C r)) hshift_len hshift
  rw [tnnMatrixAction_map_comp_X_add_C,
    filter_map_comp_X_add_C_ne_zero] at hout
  refine ⟨(isInterlacingSeq_map_comp_X_add_C_iff
    ((tnnMatrixAction A fs).filter (· ≠ 0)) r).mp hout.2, ?_⟩
  intro p hp
  have hp_shift_mem :
      p.comp (X + C r) ∈
        ((tnnMatrixAction A fs).filter (· ≠ 0)).map
          (fun q => q.comp (X + C r)) :=
    List.mem_map.mpr ⟨p, hp, rfl⟩
  have hp_shift := hout.realRooted (p.comp (X + C r)) hp_shift_mem
  have hp_shift_pos := hout.posLeadingCoeff
    (p.comp (X + C r)) hp_shift_mem
  have hp_pos_back := hp_shift_pos.comp_X_add_C (-r)
  have hp_real_back := isRealRooted_comp_X_add_C
    hp_shift.1 hp_shift.2 (-r)
  constructor
  · simpa [Polynomial.comp_assoc, add_assoc, add_left_comm, add_comm,
      sub_eq_add_neg] using hp_pos_back
  · simpa [Polynomial.comp_assoc, add_assoc, add_left_comm, add_comm,
      sub_eq_add_neg] using hp_real_back.2

/-- Square totally nonnegative matrices are a direct special case of the
rectangular positive-leading mixing theorem. -/
theorem IsTotallyNonneg.map_interlacingSeq_of_posLeadingCoeff
    {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsTotallyNonneg) (fs : List ℝ[X])
    (hfs_len : fs.length = n)
    (hfs_real : ∀ p ∈ fs, HasPosLeadingCoeff p ∧ p.Splits)
    (hfs : IsInterlacingSeq fs) :
    IsInterlacingSeq ((tnnMatrixAction A fs).filter (· ≠ 0)) ∧
      ∀ p ∈ (tnnMatrixAction A fs).filter (· ≠ 0),
        HasPosLeadingCoeff p ∧ p.Splits :=
  hA.toRect.map_interlacingSeq_of_posLeadingCoeff fs hfs_len hfs_real hfs

end Matrix
