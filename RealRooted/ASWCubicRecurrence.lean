import RealRooted.ASWCubicMinors

/-!
# Cubic recurrences for ASW Toeplitz minors

This file proves the order-three recurrences for the shift-one and shift-two
contiguous Toeplitz minors used in the cubic
Aissen--Schoenberg--Whitney argument. The shift-one recurrence follows from
a last-column expansion of the gap minors. The shift-two recurrence follows
by reversing the four supported coefficients and transposing the matrix.

Reference: S. Karlin, *Total Positivity*, Vol. I, Chapter 8, Section 3.
-/

open Matrix

noncomputable section

namespace RealRooted

private def aswGapPenultimateCofactor (u : ℕ → ℝ) (k : ℕ) :
    Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ :=
  (aswGapToeplitzMatrix u (k + 2)).submatrix
    (Fin.last k).castSucc.succAbove Fin.castSucc

private lemma aswGapPenultimateCofactor_lastRow_apply (u : ℕ → ℝ)
    (hu : ∀ j, 4 ≤ j → u j = 0) (k : ℕ) (j : Fin (k + 1)) :
    aswGapPenultimateCofactor u k (Fin.last k) j =
      if j = Fin.last k then u 3 else 0 := by
  have hrow :
      (Fin.last k).castSucc.succAbove (Fin.last k) = Fin.last (k + 1) := by
    ext
    simp
  simp only [aswGapPenultimateCofactor, Matrix.submatrix_apply,
    aswGapToeplitzMatrix]
  rw [hrow]
  simp only [aswGapRow, Fin.val_last, if_pos, Fin.val_castSucc,
    toeplitz_apply]
  by_cases hj : j = Fin.last k
  · rw [if_pos hj, hj]
    rw [if_pos (by lia)]
    simp only [Fin.val_last]
    rw [show k + 1 + 2 = k + 3 by lia, Nat.add_sub_cancel_left]
  · rw [if_neg hj]
    have hjlt : (j : ℕ) < k := by
      have := j.isLt
      have hjne : (j : ℕ) ≠ k := by
        intro h
        apply hj
        ext
        simpa using h
      lia
    rw [if_pos (by lia)]
    exact hu _ (by lia)

private lemma aswGapPenultimateCofactor_lastCofactor (u : ℕ → ℝ) (k : ℕ) :
    (aswGapPenultimateCofactor u k).submatrix Fin.castSucc Fin.castSucc =
      aswShiftedToeplitzMatrix u 1 k := by
  ext i j
  simp only [aswGapPenultimateCofactor, aswGapToeplitzMatrix,
    aswShiftedToeplitzMatrix, Matrix.submatrix_apply, Fin.val_castSucc]
  rw [Fin.succAbove_castSucc_of_lt]
  · rw [show aswGapRow (k + 2) i.castSucc.castSucc = (i : ℕ) + 1 by
      simp only [aswGapRow, Fin.val_castSucc]
      rw [if_neg (by have := i.isLt; lia)]]
  · simp

private lemma aswGapPenultimateCofactor_det (u : ℕ → ℝ)
    (hu : ∀ j, 4 ≤ j → u j = 0) (k : ℕ) :
    (aswGapPenultimateCofactor u k).det =
      u 3 * aswShiftedToeplitzMinor u 1 k := by
  have hdet := Matrix.det_succ_row
    (aswGapPenultimateCofactor u k) (Fin.last k)
  rw [Fin.sum_univ_succAbove _ (Fin.last k)] at hdet
  simp only [Fin.succAbove_last] at hdet
  have hsum :
      (∑ j : Fin k,
        (-1 : ℝ) ^ ((Fin.last k : ℕ) + (j.castSucc : Fin (k + 1))) *
          aswGapPenultimateCofactor u k (Fin.last k) j.castSucc *
            ((aswGapPenultimateCofactor u k).submatrix
              Fin.castSucc j.castSucc.succAbove).det) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    rw [aswGapPenultimateCofactor_lastRow_apply u hu]
    simp [Fin.castSucc_ne_last]
  rw [hsum, add_zero] at hdet
  simp only [aswGapPenultimateCofactor_lastRow_apply u hu, if_pos,
    aswGapPenultimateCofactor_lastCofactor, Fin.val_last] at hdet
  have heven : (-1 : ℝ) ^ (k + k) = 1 := by
    rw [show k + k = 2 * k by lia]
    simp [pow_mul]
  rw [heven, one_mul] at hdet
  exact hdet

private lemma aswGap_last_cofactor (u : ℕ → ℝ) (k : ℕ) :
    (aswGapToeplitzMatrix u (k + 2)).submatrix Fin.castSucc Fin.castSucc =
      aswShiftedToeplitzMatrix u 1 (k + 1) := by
  ext i j
  simp only [aswGapToeplitzMatrix, aswShiftedToeplitzMatrix,
    Matrix.submatrix_apply, Fin.val_castSucc]
  rw [show aswGapRow (k + 2) i.castSucc = (i : ℕ) + 1 by
    simp only [aswGapRow, Fin.val_castSucc]
    rw [if_neg (by have := i.isLt; lia)]]

private lemma aswGap_lastColumn_apply (u : ℕ → ℝ) (k : ℕ)
    (i : Fin (k + 2)) :
    aswGapToeplitzMatrix u (k + 2) i (Fin.last (k + 1)) =
      if i = (Fin.last k).castSucc then u 0
      else if i = Fin.last (k + 1) then u 2 else 0 := by
  simp only [aswGapToeplitzMatrix, Matrix.submatrix_apply, toeplitz_apply,
    Fin.val_last]
  by_cases hip : i = (Fin.last k).castSucc
  · rw [if_pos hip, hip]
    simp [aswGapRow]
  · rw [if_neg hip]
    by_cases hil : i = Fin.last (k + 1)
    · rw [if_pos hil, hil]
      simp only [aswGapRow, Fin.val_last]
      rw [if_pos (by lia), if_pos (by lia)]
      congr 1
      lia
    · rw [if_neg hil]
      have hivallt : (i : ℕ) < k := by
        have hnep : (i : ℕ) ≠ k := by
          intro h
          apply hip
          ext
          simpa using h
        have hnel : (i : ℕ) ≠ k + 1 := by
          intro h
          apply hil
          ext
          simpa using h
        have := i.isLt
        lia
      simp only [aswGapRow]
      rw [if_neg (by lia)]

/-- Under cubic support, the gap minors are a two-term combination of
shift-one contiguous minors. -/
lemma aswGapToeplitzMinor_cubic (u : ℕ → ℝ)
    (hu : ∀ j, 4 ≤ j → u j = 0) (k : ℕ) :
    aswGapToeplitzMinor u (k + 2) =
      u 2 * aswShiftedToeplitzMinor u 1 (k + 1) -
        u 0 * u 3 * aswShiftedToeplitzMinor u 1 k := by
  have hdet := Matrix.det_succ_column
    (aswGapToeplitzMatrix u (k + 2)) (Fin.last (k + 1))
  rw [Fin.sum_univ_succAbove _ (Fin.last (k + 1))] at hdet
  simp only [Fin.succAbove_last] at hdet
  have hsum :
      (∑ i : Fin (k + 1),
        (-1 : ℝ) ^ ((i.castSucc : Fin (k + 2)) + (Fin.last (k + 1) : ℕ)) *
          aswGapToeplitzMatrix u (k + 2) i.castSucc (Fin.last (k + 1)) *
            ((aswGapToeplitzMatrix u (k + 2)).submatrix
              i.castSucc.succAbove Fin.castSucc).det) =
        -u 0 * u 3 * aswShiftedToeplitzMinor u 1 k := by
    rw [Finset.sum_eq_single (Fin.last k)]
    · simp only [aswGap_lastColumn_apply, if_pos, Fin.val_castSucc, Fin.val_last]
      rw [show (-1 : ℝ) ^ (k + (k + 1)) = -1 by
        rw [show k + (k + 1) = 2 * k + 1 by lia, pow_add]
        simp [pow_mul]]
      change -1 * u 0 * (aswGapPenultimateCofactor u k).det =
        -u 0 * u 3 * aswShiftedToeplitzMinor u 1 k
      rw [aswGapPenultimateCofactor_det u hu]
      ring
    · intro b _ hblast
      rw [aswGap_lastColumn_apply]
      simp [hblast, Fin.castSucc_ne_last]
    · simp
  rw [hsum] at hdet
  have hlastne : Fin.last (k + 1) ≠ (Fin.last k).castSucc :=
    (Fin.castSucc_ne_last _).symm
  simp only [aswGap_lastColumn_apply, if_neg hlastne, if_pos,
    aswGap_last_cofactor, Fin.val_last] at hdet
  have heven : (-1 : ℝ) ^ ((k + 1) + (k + 1)) = 1 := by
    rw [show (k + 1) + (k + 1) = 2 * (k + 1) by lia]
    simp [pow_mul]
  rw [heven, one_mul] at hdet
  change aswGapToeplitzMinor u (k + 2) =
    u 2 * aswShiftedToeplitzMinor u 1 (k + 1) +
      -u 0 * u 3 * aswShiftedToeplitzMinor u 1 k at hdet
  linear_combination hdet

/-- The order-three recurrence for shift-one Toeplitz minors of a cubic
coefficient sequence. -/
theorem aswShiftedToeplitzMinor_one_cubic_rec (u : ℕ → ℝ)
    (hu : ∀ j, 4 ≤ j → u j = 0) (k : ℕ) :
    aswShiftedToeplitzMinor u 1 (k + 3) =
      u 1 * aswShiftedToeplitzMinor u 1 (k + 2) -
        u 0 * u 2 * aswShiftedToeplitzMinor u 1 (k + 1) +
          u 0 ^ 2 * u 3 * aswShiftedToeplitzMinor u 1 k := by
  have hgap := aswGapToeplitzMinor_identity u (k + 1)
  have hcubic := aswGapToeplitzMinor_cubic u hu k
  linear_combination hgap - u 0 * hcubic

/-- Coefficient reversal through degree three, extended by zero. -/
def aswCubicReverse (u : ℕ → ℝ) (j : ℕ) : ℝ :=
  if j ≤ 3 then u (3 - j) else 0

@[simp]
lemma aswCubicReverse_zero (u : ℕ → ℝ) : aswCubicReverse u 0 = u 3 := by simp [aswCubicReverse]

@[simp]
lemma aswCubicReverse_one (u : ℕ → ℝ) : aswCubicReverse u 1 = u 2 := by simp [aswCubicReverse]

@[simp]
lemma aswCubicReverse_two (u : ℕ → ℝ) : aswCubicReverse u 2 = u 1 := by simp [aswCubicReverse]

@[simp]
lemma aswCubicReverse_three (u : ℕ → ℝ) : aswCubicReverse u 3 = u 0 := by simp [aswCubicReverse]

lemma aswCubicReverse_eq_zero (u : ℕ → ℝ) {j : ℕ} (hj : 4 ≤ j) :
    aswCubicReverse u j = 0 := by
  simp [aswCubicReverse, show ¬j ≤ 3 by lia]

private lemma aswCubicReverse_sub_eq (u : ℕ → ℝ) (i j : ℕ)
    (hji : j ≤ i + 2) (hij : i ≤ j + 1) :
    aswCubicReverse u (j + 1 - i) = u (i + 2 - j) := by
  rw [aswCubicReverse, if_pos (by lia)]
  congr 1
  grind

/-- For a cubic-supported sequence, the shift-two Toeplitz matrix is the
transpose of the shift-one matrix for the reversed coefficients. -/
lemma aswShiftedToeplitzMatrix_two_eq_cubicReverse_transpose (u : ℕ → ℝ)
    (hu : ∀ j, 4 ≤ j → u j = 0) (n : ℕ) :
    aswShiftedToeplitzMatrix u 2 n =
      (aswShiftedToeplitzMatrix (aswCubicReverse u) 1 n)ᵀ := by
  ext i j
  simp only [aswShiftedToeplitzMatrix, Matrix.submatrix_apply,
    Matrix.transpose_apply, toeplitz_apply]
  by_cases hji : (j : ℕ) ≤ (i : ℕ) + 2
  · rw [if_pos hji]
    by_cases hij : (i : ℕ) ≤ (j : ℕ) + 1
    · rw [if_pos hij]
      exact (aswCubicReverse_sub_eq u i j hji hij).symm
    · rw [if_neg hij]
      exact hu _ (by lia)
  · rw [if_neg hji]
    rw [if_pos (by lia)]
    exact (aswCubicReverse_eq_zero u (by lia)).symm

lemma aswShiftedToeplitzMinor_two_eq_cubicReverse_one (u : ℕ → ℝ)
    (hu : ∀ j, 4 ≤ j → u j = 0) (n : ℕ) :
    aswShiftedToeplitzMinor u 2 n =
      aswShiftedToeplitzMinor (aswCubicReverse u) 1 n := by
  rw [aswShiftedToeplitzMinor, aswShiftedToeplitzMinor,
    aswShiftedToeplitzMatrix_two_eq_cubicReverse_transpose u hu, Matrix.det_transpose]

/-- The order-three recurrence for shift-two Toeplitz minors of a cubic
coefficient sequence. -/
theorem aswShiftedToeplitzMinor_two_cubic_rec (u : ℕ → ℝ)
    (hu : ∀ j, 4 ≤ j → u j = 0) (k : ℕ) :
    aswShiftedToeplitzMinor u 2 (k + 3) =
      u 2 * aswShiftedToeplitzMinor u 2 (k + 2) -
        u 1 * u 3 * aswShiftedToeplitzMinor u 2 (k + 1) +
          u 0 * u 3 ^ 2 * aswShiftedToeplitzMinor u 2 k := by
  have hreverse : ∀ j, 4 ≤ j → aswCubicReverse u j = 0 := by
    intro j hj
    exact aswCubicReverse_eq_zero u hj
  have hrec := aswShiftedToeplitzMinor_one_cubic_rec
    (aswCubicReverse u) hreverse k
  rw [aswCubicReverse_zero, aswCubicReverse_one, aswCubicReverse_two,
    aswCubicReverse_three] at hrec
  rw [aswShiftedToeplitzMinor_two_eq_cubicReverse_one u hu (k + 3),
    aswShiftedToeplitzMinor_two_eq_cubicReverse_one u hu (k + 2),
    aswShiftedToeplitzMinor_two_eq_cubicReverse_one u hu (k + 1),
    aswShiftedToeplitzMinor_two_eq_cubicReverse_one u hu k]
  linear_combination hrec

end RealRooted

