/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/

import RealRooted.Mathlib.LinearAlgebra.Matrix.TotallyNonneg

/-!
# Variable lower-bidiagonal totally nonnegative matrices

This file provides the reusable lower-bidiagonal constructor whose diagonal and
subdiagonal entries may vary independently. The proof is by induction on the
minor size and does not require strict positivity of either sequence.
-/

namespace Matrix

variable {R : Type*} [CommRing R] [PartialOrder R] [IsStrictOrderedRing R]

/-- A lower-bidiagonal matrix with diagonal `d` and subdiagonal `s`. -/
def lowerBidiagonal (d s : ℕ → R) : Matrix ℕ ℕ R :=
  Matrix.of fun i j => if i = j then d i else if i = j + 1 then s j else 0

omit [PartialOrder R] [IsStrictOrderedRing R] in
@[simp] lemma lowerBidiagonal_apply (d s : ℕ → R) (i j : ℕ) :
    lowerBidiagonal d s i j =
      if i = j then d i else if i = j + 1 then s j else 0 :=
  rfl

/-- Every variable lower-bidiagonal matrix with nonnegative entries is totally
nonnegative. Zero diagonal and subdiagonal entries are allowed. -/
theorem isTotallyNonneg_lowerBidiagonal (d s : ℕ → R)
    (hd : ∀ i, 0 ≤ d i) (hs : ∀ i, 0 ≤ s i) :
    (lowerBidiagonal d s).IsTotallyNonneg := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      intro rows cols hrows hcols
      let S := (lowerBidiagonal d s).submatrix rows cols
      rcases lt_or_ge (cols 0) (rows 0) with hlt | hge
      · rcases eq_or_lt_of_le (Nat.succ_le_of_lt hlt) with heq | hlt_succ
        · have h00 : S 0 0 = s (cols 0) := by
            simp [S, heq.symm]
          have hne1 (i : Fin n) : rows i.succ ≠ cols 0 := by
            have h := hrows (Fin.succ_pos i)
            lia
          have hne2 (i : Fin n) : rows i.succ ≠ cols 0 + 1 := by
            have h := hrows (Fin.succ_pos i)
            lia
          have hi0 (i : Fin n) : S i.succ 0 = 0 := by
            simp only [S, submatrix_apply, lowerBidiagonal_apply,
              hne1 i, hne2 i, ↓reduceIte]
          rw [det_succ_column_zero S]
          have hsum :
              (∑ i : Fin (n + 1), (-1) ^ (i : ℕ) * S i 0 *
                  det (S.submatrix i.succAbove Fin.succ)) =
                s (cols 0) *
                  det (S.submatrix (0 : Fin (n + 1)).succAbove Fin.succ) := by
            rw [Fin.sum_univ_succ]
            simp [hi0, h00]
          rw [hsum, submatrix_submatrix]
          exact mul_nonneg (hs _) <|
            ih (hrows.comp (Fin.strictMono_succAbove 0))
              (hcols.comp Fin.strictMono_succ)
        · have hne1 (i : Fin (n + 1)) : rows i ≠ cols 0 := by
            have h := hrows.monotone (Fin.zero_le i)
            lia
          have hne2 (i : Fin (n + 1)) : rows i ≠ cols 0 + 1 := by
            have h := hrows.monotone (Fin.zero_le i)
            lia
          have hi0 (i : Fin (n + 1)) : S i 0 = 0 := by
            simp only [S, submatrix_apply, lowerBidiagonal_apply,
              hne1 i, hne2 i, ↓reduceIte]
          rw [det_succ_column_zero S]
          simp_all
      · rcases eq_or_lt_of_le hge with heq | hlt
        · have h00 : S 0 0 = d (rows 0) := by simp [S, heq]
          have hne1 (j : Fin n) : rows 0 ≠ cols j.succ := by
            have h := hcols (Fin.succ_pos j)
            lia
          have hne2 (j : Fin n) : rows 0 ≠ cols j.succ + 1 := by
            have h := hcols (Fin.succ_pos j)
            lia
          have h0j (j : Fin n) : S 0 j.succ = 0 := by
            simp only [S, submatrix_apply, lowerBidiagonal_apply,
              hne1 j, hne2 j, ↓reduceIte]
          rw [det_succ_row_zero S]
          have hsum :
              (∑ j : Fin (n + 1), (-1) ^ (j : ℕ) * S 0 j *
                  det (S.submatrix Fin.succ j.succAbove)) =
                d (rows 0) *
                  det (S.submatrix Fin.succ (0 : Fin (n + 1)).succAbove) := by
            rw [Fin.sum_univ_succ]
            simp [h0j, h00]
          rw [hsum, submatrix_submatrix]
          exact mul_nonneg (hd _) <|
            ih (hrows.comp Fin.strictMono_succ)
              (hcols.comp (Fin.strictMono_succAbove 0))
        · have hne1 (j : Fin (n + 1)) : rows 0 ≠ cols j := by
            have h := hcols.monotone (Fin.zero_le j)
            lia
          have hne2 (j : Fin (n + 1)) : rows 0 ≠ cols j + 1 := by
            have h := hcols.monotone (Fin.zero_le j)
            lia
          have h0j (j : Fin (n + 1)) : S 0 j = 0 := by
            simp only [S, submatrix_apply, lowerBidiagonal_apply,
              hne1 j, hne2 j, ↓reduceIte]
          rw [det_succ_row_zero S]
          simp_all

end Matrix
