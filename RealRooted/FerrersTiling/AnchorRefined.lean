import RealRooted.MatrixInterlacing

/-!
# Refined anchor-word recursion

This file formalizes the polynomial transfer matrix from
Ahlberg--Alexandersson, *Polynomials from tilings of rectangles*, Section 3.
Index `0` represents the terminal symbol `∞`; index `j + 1` represents row
`j + 1`.  The construction is algebraic: the layer-2 anchor-word model is not
used here.
-/

open Polynomial

namespace RealRooted
namespace FerrersTiling

noncomputable section

/-- Entry `(i,j)` of the refined anchor transfer matrix.  Its first row is
all `1`; row `i > 0` contains `X` before column `i` and `0` thereafter. -/
def anchorTransferEntry (i j : ℕ) : ℝ[X] :=
  if i = 0 then 1 else if j < i then X else 0

/-- The `(d+1) × (d+1)` transfer matrix for the refined polynomials
`(Q_(d,n,∞), Q_(d,n,1), ..., Q_(d,n,d))`. -/
def anchorTransferMatrix (d : ℕ) : List (List ℝ[X]) :=
  (List.range (d + 1)).map fun i =>
    (List.range (d + 1)).map fun j => anchorTransferEntry i j

@[simp] theorem length_anchorTransferMatrix (d : ℕ) :
    (anchorTransferMatrix d).length = d + 1 := by
  simp [anchorTransferMatrix]

theorem anchorTransferMatrix_rect (d : ℕ) :
    ∀ row ∈ anchorTransferMatrix d, row.length = d + 1 := by
  intro row hrow
  simp only [anchorTransferMatrix, List.mem_map, List.mem_range] at hrow
  obtain ⟨i, hi, rfl⟩ := hrow
  simp

@[simp] theorem getElem_anchorTransferMatrix (d i j : ℕ)
    (hi : i < (anchorTransferMatrix d).length)
    (hj : j < (anchorTransferMatrix d)[i].length) :
    (anchorTransferMatrix d)[i][j] = anchorTransferEntry i j := by
  simp [anchorTransferMatrix]

theorem anchorTransferMatrix_nonneg (d : ℕ) :
    ∀ row ∈ anchorTransferMatrix d, ∀ p ∈ row, HasNonnegCoeffs p := by
  intro row hrow p hp
  simp only [anchorTransferMatrix, List.mem_map, List.mem_range] at hrow
  obtain ⟨i, hi, rfl⟩ := hrow
  simp only [List.mem_map, List.mem_range] at hp
  obtain ⟨j, hj, rfl⟩ := hp
  unfold anchorTransferEntry
  split_ifs
  · exact hasNonnegCoeffs_one
  · exact hasNonnegCoeffs_X
  · exact hasNonnegCoeffs_zero

private theorem atomic_has2x2_1111 :
    Has2x2InterlacingProperty0 1 1 1 1 := by
  exact Atomic2x2Matrix.hasAffineProperty_of_isAffineAdmissible
    (M := ⟨.one, .one, .one, .one⟩) (by decide)

private theorem atomic_has2x2_11XX :
    Has2x2InterlacingProperty0 1 1 X X := by
  exact Atomic2x2Matrix.hasAffineProperty_of_isAffineAdmissible
    (M := ⟨.one, .one, .x, .x⟩) (by decide)

private theorem atomic_has2x2_11X0 :
    Has2x2InterlacingProperty0 1 1 X 0 := by
  exact Atomic2x2Matrix.hasAffineProperty_of_isAffineAdmissible
    (M := ⟨.one, .one, .x, .zero⟩) (by decide)

private theorem atomic_has2x2_1100 :
    Has2x2InterlacingProperty0 1 1 0 0 := by
  exact Atomic2x2Matrix.hasAffineProperty_of_isAffineAdmissible
    (M := ⟨.one, .one, .zero, .zero⟩) (by decide)

private theorem atomic_has2x2_XXXX :
    Has2x2InterlacingProperty0 X X X X := by
  exact Atomic2x2Matrix.hasAffineProperty_of_isAffineAdmissible
    (M := ⟨.x, .x, .x, .x⟩) (by decide)

private theorem atomic_has2x2_X0XX :
    Has2x2InterlacingProperty0 X 0 X X := by
  exact Atomic2x2Matrix.hasAffineProperty_of_isAffineAdmissible
    (M := ⟨.x, .zero, .x, .x⟩) (by decide)

private theorem atomic_has2x2_X0X0 :
    Has2x2InterlacingProperty0 X 0 X 0 := by
  exact Atomic2x2Matrix.hasAffineProperty_of_isAffineAdmissible
    (M := ⟨.x, .zero, .x, .zero⟩) (by decide)

private theorem atomic_has2x2_00XX :
    Has2x2InterlacingProperty0 0 0 X X := by
  exact Atomic2x2Matrix.hasAffineProperty_of_isAffineAdmissible
    (M := ⟨.zero, .zero, .x, .x⟩) (by decide)

private theorem atomic_has2x2_00X0 :
    Has2x2InterlacingProperty0 0 0 X 0 := by
  exact Atomic2x2Matrix.hasAffineProperty_of_isAffineAdmissible
    (M := ⟨.zero, .zero, .x, .zero⟩) (by decide)

private theorem atomic_has2x2_0000 :
    Has2x2InterlacingProperty0 0 0 0 0 := by
  exact Atomic2x2Matrix.hasAffineProperty_of_isAffineAdmissible
    (M := ⟨.zero, .zero, .zero, .zero⟩) (by decide)

private theorem anchorTransferEntry_has2x2 {i₁ i₂ j₁ j₂ : ℕ}
    (hi : i₁ ≤ i₂) (hj : j₁ ≤ j₂) :
    Has2x2InterlacingProperty0
      (anchorTransferEntry i₁ j₁) (anchorTransferEntry i₁ j₂)
      (anchorTransferEntry i₂ j₁) (anchorTransferEntry i₂ j₂) := by
  by_cases hi₁ : i₁ = 0
  · subst i₁
    by_cases hi₂ : i₂ = 0
    · subst i₂
      simpa [anchorTransferEntry] using atomic_has2x2_1111
    · have hi₂pos : 0 < i₂ := Nat.pos_of_ne_zero hi₂
      by_cases hj₂ : j₂ < i₂
      · have hj₁ : j₁ < i₂ := lt_of_le_of_lt hj hj₂
        simpa [anchorTransferEntry, hi₂, hj₁, hj₂] using atomic_has2x2_11XX
      · by_cases hj₁ : j₁ < i₂
        · simpa [anchorTransferEntry, hi₂, hj₁, hj₂] using atomic_has2x2_11X0
        · simpa [anchorTransferEntry, hi₂, hj₁, hj₂] using atomic_has2x2_1100
  · have hi₁pos : 0 < i₁ := Nat.pos_of_ne_zero hi₁
    have hi₂pos : 0 < i₂ := hi₁pos.trans_le hi
    have hi₂ : i₂ ≠ 0 := Nat.ne_of_gt hi₂pos
    by_cases hj₂i₁ : j₂ < i₁
    · have hj₁i₁ : j₁ < i₁ := lt_of_le_of_lt hj hj₂i₁
      have hj₁i₂ : j₁ < i₂ := hj₁i₁.trans_le hi
      have hj₂i₂ : j₂ < i₂ := hj₂i₁.trans_le hi
      simpa [anchorTransferEntry, hi₁, hi₂, hj₁i₁, hj₂i₁, hj₁i₂, hj₂i₂] using
        atomic_has2x2_XXXX
    · by_cases hj₁i₁ : j₁ < i₁
      · have hj₁i₂ : j₁ < i₂ := hj₁i₁.trans_le hi
        by_cases hj₂i₂ : j₂ < i₂
        · simpa [anchorTransferEntry, hi₁, hi₂, hj₁i₁, hj₂i₁, hj₁i₂, hj₂i₂] using
            atomic_has2x2_X0XX
        · simpa [anchorTransferEntry, hi₁, hi₂, hj₁i₁, hj₂i₁, hj₁i₂, hj₂i₂] using
            atomic_has2x2_X0X0
      · by_cases hj₂i₂ : j₂ < i₂
        · have hj₁i₂ : j₁ < i₂ := lt_of_le_of_lt hj hj₂i₂
          simpa [anchorTransferEntry, hi₁, hi₂, hj₁i₁, hj₂i₁, hj₁i₂, hj₂i₂] using
            atomic_has2x2_00XX
        · by_cases hj₁i₂ : j₁ < i₂
          · simpa [anchorTransferEntry, hi₁, hi₂, hj₁i₁, hj₂i₁, hj₁i₂, hj₂i₂] using
              atomic_has2x2_00X0
          · simpa [anchorTransferEntry, hi₁, hi₂, hj₁i₁, hj₂i₁, hj₁i₂, hj₂i₂] using
              atomic_has2x2_0000

theorem anchorTransferMatrix_has2x2 (d : ℕ) :
    ∀ (i₁ i₂ : Fin (anchorTransferMatrix d).length) (j₁ j₂ : Fin (d + 1)),
      i₁ ≤ i₂ → j₁ ≤ j₂ →
      Has2x2InterlacingProperty0
        (((anchorTransferMatrix d).get i₁).get
          ⟨j₁, by rw [anchorTransferMatrix_rect d _ (List.get_mem _ i₁)]; exact j₁.2⟩)
        (((anchorTransferMatrix d).get i₁).get
          ⟨j₂, by rw [anchorTransferMatrix_rect d _ (List.get_mem _ i₁)]; exact j₂.2⟩)
        (((anchorTransferMatrix d).get i₂).get
          ⟨j₁, by rw [anchorTransferMatrix_rect d _ (List.get_mem _ i₂)]; exact j₁.2⟩)
        (((anchorTransferMatrix d).get i₂).get
          ⟨j₂, by rw [anchorTransferMatrix_rect d _ (List.get_mem _ i₂)]; exact j₂.2⟩) := by
  intro i₁ i₂ j₁ j₂ hi hj
  simp only [List.get_eq_getElem, getElem_anchorTransferMatrix]
  exact anchorTransferEntry_has2x2 hi hj

/-- The refined vector, initialized by `(1,0,...,0)` and advanced by the
paper's transfer matrix. -/
def anchorRefinedList (d : ℕ) : ℕ → List ℝ[X]
  | 0 => oneSupportSeq (d + 1) ⟨0, by lia⟩
  | n + 1 => matPolyAction (anchorTransferMatrix d) (anchorRefinedList d n)

@[simp] theorem length_anchorRefinedList (d n : ℕ) :
    (anchorRefinedList d n).length = d + 1 := by
  cases n <;> simp [anchorRefinedList]

/-- The exact vector recursion of the paper. -/
theorem anchorRefinedList_succ (d n : ℕ) :
    anchorRefinedList d (n + 1) =
      matPolyAction (anchorTransferMatrix d) (anchorRefinedList d n) := by
  rfl

/-- The refined polynomial with terminal state `i`; state `0` is `∞`, and
state `j+1` is row `j+1`. -/
def anchorRefinedPolynomial (d n : ℕ) (i : Fin (d + 1)) : ℝ[X] :=
  (anchorRefinedList d n).get ⟨i, by rw [length_anchorRefinedList]; exact i.2⟩

/-- Every refined vector is a zero-aware nonnegative interlacing sequence,
and every nonzero member is real-rooted. -/
theorem anchorRefined_interlacing (d n : ℕ) :
    IsInterlacingSeq0NonnegRealRooted (anchorRefinedList d n) := by
  induction n with
  | zero =>
      exact isInterlacingSeq0NonnegRealRooted_oneSupportSeq ⟨0, by lia⟩
  | succ n ih =>
      rw [anchorRefinedList_succ]
      exact matrix_preserves_interlacing_seq0_of_2x2_weak
        (anchorTransferMatrix d)
        (anchorTransferMatrix_rect d)
        (anchorTransferMatrix_nonneg d)
        (anchorTransferMatrix_has2x2 d)
        (anchorRefinedList d n)
        (length_anchorRefinedList d n)
        ih.1 ih.2

/-- Ordered refined components interlace. -/
theorem anchorRefinedPolynomial_interl (d n : ℕ) (i j : Fin (d + 1))
    (hij : i < j) :
    Interl (anchorRefinedPolynomial d n i) (anchorRefinedPolynomial d n j) := by
  let i' : Fin (anchorRefinedList d n).length :=
    ⟨i, by rw [length_anchorRefinedList]; exact i.2⟩
  let j' : Fin (anchorRefinedList d n).length :=
    ⟨j, by rw [length_anchorRefinedList]; exact j.2⟩
  have hij' : i' < j' := by simpa [i', j'] using hij
  have h := (anchorRefined_interlacing d n).1.1.interl hij'
  simpa [anchorRefinedPolynomial, i', j'] using h

/-- Every refined component is real-rooted, including the zero polynomial
under the library's splitting convention. -/
theorem anchorRefinedPolynomial_splits (d n : ℕ) (i : Fin (d + 1)) :
    (anchorRefinedPolynomial d n i).Splits := by
  apply (anchorRefined_interlacing d n).splits_of_mem
  exact List.get_mem _ _

/-- The unrefined anchor polynomial is the `∞` component one step later, as
in the paper's identity `Q_(d,n) = Q_(d,n+1,∞)`. -/
def anchorRefinedTotal (d n : ℕ) : ℝ[X] :=
  anchorRefinedPolynomial d (n + 1) ⟨0, by lia⟩

/-- The total anchor polynomial obtained from the refined recursion is
real-rooted. -/
theorem anchorRefinedTotal_splits (d n : ℕ) :
    (anchorRefinedTotal d n).Splits :=
  anchorRefinedPolynomial_splits d (n + 1) ⟨0, by lia⟩

end

end FerrersTiling
end RealRooted
