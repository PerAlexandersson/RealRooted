import RealRooted.AissenSchoenbergWhitneyBase

/-!
# Toeplitz minor families for the cubic ASW argument

This file defines the two contiguous shifted-minor families and the
single-row-gap family used in the degree-three
Aissen--Schoenberg--Whitney argument.

For a sequence `u`, write `A n` for the minor with rows
`1, ..., n`, `E n` for the minor with rows `2, ..., n + 1`, and
`G n` for the minor with rows `1, ..., n - 1, n + 1`; all three use
columns `0, ..., n - 1`. Expanding `A (n + 1)` along its last column
gives

`u 0 * G n = u 1 * A n - A (n + 1)`.

The unbounded gap family is essential: no bounded order of Toeplitz minors
detects every cubic with a nonreal conjugate pair.

Reference: S. Karlin, *Total Positivity*, Vol. I, Chapter 8, Section 3.
-/

open Matrix

noncomputable section

namespace RealRooted

/-- The shifted contiguous `n × n` Toeplitz matrix with row shift `shift`. -/
def aswShiftedToeplitzMatrix (u : ℕ → ℝ) (shift n : ℕ) :
    Matrix (Fin n) (Fin n) ℝ :=
  (toeplitz u).submatrix
    (fun i : Fin n => (i : ℕ) + shift)
    (fun j : Fin n => (j : ℕ))

/-- Determinant of the shifted contiguous Toeplitz matrix. The cubic argument
uses shifts one and two, conventionally denoted `A n` and `E n`. -/
def aswShiftedToeplitzMinor (u : ℕ → ℝ) (shift n : ℕ) : ℝ :=
  (aswShiftedToeplitzMatrix u shift n).det

/-- The increasing row map `1, ..., n - 1, n + 1`, which skips row `n`. -/
def aswGapRow (n : ℕ) (i : Fin n) : ℕ :=
  if (i : ℕ) + 1 = n then (i : ℕ) + 2 else (i : ℕ) + 1

lemma strictMono_aswGapRow (n : ℕ) : StrictMono (aswGapRow n) := by
  intro i j hij
  have hij' : (i : ℕ) < (j : ℕ) := hij
  have hjlt : (j : ℕ) < n := j.isLt
  simp only [aswGapRow]
  split_ifs <;> lia

/-- The `n × n` Toeplitz matrix with rows `1, ..., n - 1, n + 1` and
columns `0, ..., n - 1`. -/
def aswGapToeplitzMatrix (u : ℕ → ℝ) (n : ℕ) :
    Matrix (Fin n) (Fin n) ℝ :=
  (toeplitz u).submatrix (aswGapRow n) (fun j : Fin n => (j : ℕ))

/-- Determinant of the single-row-gap Toeplitz matrix, conventionally
denoted `G n` in the cubic argument. -/
def aswGapToeplitzMinor (u : ℕ → ℝ) (n : ℕ) : ℝ :=
  (aswGapToeplitzMatrix u n).det

/-- Every shifted contiguous minor of a Pólya-frequency sequence is
nonnegative. -/
lemma IsPolyaFreqSeq.aswShiftedToeplitzMinor_nonneg {u : ℕ → ℝ}
    (hpf : IsPolyaFreqSeq u) (shift n : ℕ) :
    0 ≤ aswShiftedToeplitzMinor u shift n :=
  hpf (fun _ _ h => by lia) Fin.val_strictMono

/-- Every single-row-gap minor of a Pólya-frequency sequence is nonnegative. -/
lemma IsPolyaFreqSeq.aswGapToeplitzMinor_nonneg {u : ℕ → ℝ}
    (hpf : IsPolyaFreqSeq u) (n : ℕ) :
    0 ≤ aswGapToeplitzMinor u n :=
  hpf (strictMono_aswGapRow n) Fin.val_strictMono

@[simp]
lemma aswShiftedToeplitzMinor_zero (u : ℕ → ℝ) (shift : ℕ) :
    aswShiftedToeplitzMinor u shift 0 = 1 := by
  simp [aswShiftedToeplitzMinor, aswShiftedToeplitzMatrix]

@[simp]
lemma aswShiftedToeplitzMinor_one (u : ℕ → ℝ) (shift : ℕ) :
    aswShiftedToeplitzMinor u shift 1 = u shift := by
  simp [aswShiftedToeplitzMinor, aswShiftedToeplitzMatrix, toeplitz]

lemma aswShiftedToeplitzMinor_one_two (u : ℕ → ℝ) :
    aswShiftedToeplitzMinor u 1 2 = u 1 ^ 2 - u 0 * u 2 := by
  norm_num [aswShiftedToeplitzMinor, aswShiftedToeplitzMatrix, toeplitz,
    Matrix.det_fin_two]
  ring

lemma aswShiftedToeplitzMinor_two_two (u : ℕ → ℝ) :
    aswShiftedToeplitzMinor u 2 2 = u 2 ^ 2 - u 1 * u 3 := by
  norm_num [aswShiftedToeplitzMinor, aswShiftedToeplitzMatrix, toeplitz,
    Matrix.det_fin_two]
  ring

@[simp]
lemma aswGapToeplitzMinor_zero (u : ℕ → ℝ) :
    aswGapToeplitzMinor u 0 = 1 := by
  simp [aswGapToeplitzMinor, aswGapToeplitzMatrix]

@[simp]
lemma aswGapToeplitzMinor_one (u : ℕ → ℝ) :
    aswGapToeplitzMinor u 1 = u 2 := by
  norm_num [aswGapToeplitzMinor, aswGapToeplitzMatrix, aswGapRow, toeplitz]

lemma aswGapToeplitzMinor_two (u : ℕ → ℝ) :
    aswGapToeplitzMinor u 2 = u 1 * u 2 - u 0 * u 3 := by
  norm_num [aswGapToeplitzMinor, aswGapToeplitzMatrix, aswGapRow, toeplitz,
    Matrix.det_fin_two]

private lemma penultimate_succAbove_add_one (k : ℕ) (i : Fin (k + 1)) :
    (((Fin.last k).castSucc.succAbove i : Fin (k + 2)) : ℕ) + 1 =
      aswGapRow (k + 1) i := by
  simp only [aswGapRow]
  by_cases hi : (i : ℕ) + 1 = k + 1
  · rw [if_pos hi]
    have hilast : i = Fin.last k := by
      ext
      simp only [Fin.val_last]
      lia
    rw [hilast, Fin.succAbove_castSucc_of_le _ _ (le_refl _)]
    simp
  · rw [if_neg hi]
    have hivallt : (i : ℕ) < k := by
      have := i.isLt
      lia
    have hilt : i < Fin.last k := Fin.mk_lt_mk.mpr hivallt
    rw [Fin.succAbove_castSucc_of_lt _ _ hilt]
    rfl

private lemma aswA_last_cofactor (u : ℕ → ℝ) (k : ℕ) :
    (aswShiftedToeplitzMatrix u 1 (k + 2)).submatrix
        Fin.castSucc Fin.castSucc =
      aswShiftedToeplitzMatrix u 1 (k + 1) := by
  ext i j
  simp [aswShiftedToeplitzMatrix, Matrix.submatrix]

private lemma aswA_penultimate_cofactor (u : ℕ → ℝ) (k : ℕ) :
    (aswShiftedToeplitzMatrix u 1 (k + 2)).submatrix
        (Fin.last k).castSucc.succAbove Fin.castSucc =
      aswGapToeplitzMatrix u (k + 1) := by
  ext i j
  simp only [aswShiftedToeplitzMatrix, aswGapToeplitzMatrix,
    Matrix.submatrix_apply, Fin.val_castSucc]
  rw [penultimate_succAbove_add_one]

private lemma aswA_lastColumn_apply (u : ℕ → ℝ) (k : ℕ)
    (i : Fin (k + 2)) :
    aswShiftedToeplitzMatrix u 1 (k + 2) i (Fin.last (k + 1)) =
      if i = (Fin.last k).castSucc then u 0
      else if i = Fin.last (k + 1) then u 1 else 0 := by
  simp only [aswShiftedToeplitzMatrix, Matrix.submatrix_apply,
    toeplitz_apply, Fin.val_last]
  by_cases hip : i = (Fin.last k).castSucc
  · rw [if_pos hip, hip]
    simp
  · rw [if_neg hip]
    by_cases hil : i = Fin.last (k + 1)
    · rw [if_pos hil, hil]
      simp
    · rw [if_neg hil, if_neg]
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
      lia

/-- The key relation between the shift-one contiguous minors and the
single-row-gap minors. It follows by expanding the `(k + 2) × (k + 2)`
shift-one matrix along its last column. -/
theorem aswGapToeplitzMinor_identity (u : ℕ → ℝ) (k : ℕ) :
    u 0 * aswGapToeplitzMinor u (k + 1) =
      u 1 * aswShiftedToeplitzMinor u 1 (k + 1) -
        aswShiftedToeplitzMinor u 1 (k + 2) := by
  have hdet := Matrix.det_succ_column
    (aswShiftedToeplitzMatrix u 1 (k + 2)) (Fin.last (k + 1))
  rw [Fin.sum_univ_succAbove _ (Fin.last (k + 1))] at hdet
  simp only [Fin.succAbove_last] at hdet
  have hsum :
      (∑ i : Fin (k + 1),
        (-1 : ℝ) ^ ((i.castSucc : Fin (k + 2)) + (Fin.last (k + 1) : ℕ)) *
          aswShiftedToeplitzMatrix u 1 (k + 2) i.castSucc (Fin.last (k + 1)) *
            ((aswShiftedToeplitzMatrix u 1 (k + 2)).submatrix
              i.castSucc.succAbove Fin.castSucc).det) =
        -u 0 * aswGapToeplitzMinor u (k + 1) := by
    rw [Finset.sum_eq_single (Fin.last k)]
    · simp only [aswA_lastColumn_apply, ↓reduceIte,
        aswA_penultimate_cofactor, aswGapToeplitzMinor, Fin.val_castSucc,
        Fin.val_last]
      rw [show (-1 : ℝ) ^ (k + (k + 1)) = -1 by
        rw [show k + (k + 1) = 2 * k + 1 by lia, pow_add]
        simp [pow_mul]]
      ring
    · intro b _ hblast
      rw [aswA_lastColumn_apply]
      simp [hblast, Fin.castSucc_ne_last]
    · simp
  rw [hsum] at hdet
  have hlastne : Fin.last (k + 1) ≠ (Fin.last k).castSucc :=
    (Fin.castSucc_ne_last _).symm
  simp only [aswA_lastColumn_apply, if_neg hlastne, if_pos,
    aswA_last_cofactor, Fin.val_last] at hdet
  have heven : (-1 : ℝ) ^ ((k + 1) + (k + 1)) = 1 := by
    rw [show (k + 1) + (k + 1) = 2 * (k + 1) by lia]
    simp [pow_mul]
  rw [heven, one_mul] at hdet
  change aswShiftedToeplitzMinor u 1 (k + 2) =
    u 1 * aswShiftedToeplitzMinor u 1 (k + 1) +
      -u 0 * aswGapToeplitzMinor u (k + 1) at hdet
  linear_combination hdet

end RealRooted
