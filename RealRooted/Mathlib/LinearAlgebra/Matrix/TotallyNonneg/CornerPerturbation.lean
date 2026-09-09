import RealRooted.Mathlib.LinearAlgebra.Matrix.Charpoly.Submatrix
import RealRooted.Mathlib.LinearAlgebra.Matrix.TotallyNonneg

/-!
# Corner perturbations of totally nonnegative matrices

This file proves that adding a nonnegative scalar to the northwest corner of a
finite matrix preserves total nonnegativity. The determinant update is isolated
as a general commutative-ring identity.
-/

namespace Matrix

open Polynomial

/-- Adding `t` to the northwest corner changes the determinant by `t` times the
complementary southeast principal minor. -/
theorem det_add_single_zero_zero {R : Type*} [CommRing R] {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (t : R) :
    (A + Matrix.single 0 0 t).det =
      A.det + t * (A.submatrix Fin.succ Fin.succ).det := by
  have hsub (j : Fin (n + 1)) :
      (A + Matrix.single 0 0 t).submatrix Fin.succ j.succAbove =
        A.submatrix Fin.succ j.succAbove := by
    ext i k
    rw [Matrix.submatrix_apply, Matrix.add_apply, Matrix.single_apply,
      Matrix.submatrix_apply]
    split_ifs with h
    · exact (Fin.succ_ne_zero i h.1.symm).elim
    · exact add_zero _
  rw [det_succ_row_zero, det_succ_row_zero]
  simp_rw [hsub]
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
  have hzero : ∀ j : Fin n, (0 : Fin (n + 1)) ≠ j.succ := fun j =>
    Ne.symm (Fin.succ_ne_zero j)
  simp only [Fin.val_zero, pow_zero, one_mul, add_apply, Matrix.single_apply,
    add_mul]
  simp [hzero, Fin.succAbove_zero]
  ring

/-- Adding `t` to the northwest corner subtracts `C t` times the complementary
southeast principal characteristic polynomial from the characteristic
polynomial. -/
theorem charpoly_add_single_zero_zero {R : Type*} [CommRing R] {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (t : R) :
    (A + Matrix.single 0 0 t).charpoly =
      A.charpoly - C t * (A.submatrix Fin.succ Fin.succ).charpoly := by
  have hcharmatrix :
      (A + Matrix.single 0 0 t).charmatrix =
        A.charmatrix + Matrix.single 0 0 (-C t) := by
    apply Matrix.ext
    intro i j
    by_cases h : 0 = i ∧ 0 = j
    · rcases h with ⟨rfl, rfl⟩
      simp
      ring
    · simp [Matrix.charmatrix_apply, h]
  rw [Matrix.charpoly, hcharmatrix, det_add_single_zero_zero,
    charmatrix_submatrix_self A Fin.succ (Fin.succ_injective n)]
  change A.charmatrix.det + -C t * _ =
    A.charmatrix.det - C t * (A.submatrix Fin.succ Fin.succ).charmatrix.det
  ring

/-- Adding a nonnegative scalar to the northwest corner of a totally
nonnegative finite matrix preserves total nonnegativity. -/
theorem IsTotallyNonneg.add_single_zero_zero {R : Type*}
    [CommRing R] [PartialOrder R] [IsStrictOrderedRing R] {N : ℕ}
    {A : Matrix (Fin (N + 1)) (Fin (N + 1)) R}
    (hA : A.IsTotallyNonneg) {t : R} (ht : 0 ≤ t) :
    (A + Matrix.single 0 0 t).IsTotallyNonneg := by
  intro n rows cols hrows hcols
  cases n with
  | zero => simp
  | succ n =>
      by_cases hr : rows 0 = 0
      · by_cases hc : cols 0 = 0
        · have hmatrix :
              (A + Matrix.single 0 0 t).submatrix rows cols =
                A.submatrix rows cols + Matrix.single 0 0 t := by
            have hrows_zero (i : Fin (n + 1)) : 0 = rows i ↔ 0 = i := by
              constructor
              · intro hi
                exact hrows.injective (hr.trans hi)
              · rintro rfl
                exact hr.symm
            have hcols_zero (j : Fin (n + 1)) : 0 = cols j ↔ 0 = j := by
              constructor
              · intro hj
                exact hcols.injective (hc.trans hj)
              · rintro rfl
                exact hc.symm
            ext i j
            simp only [Matrix.submatrix_apply, Matrix.add_apply,
              Matrix.single_apply]
            simp only [hrows_zero, hcols_zero]
          rw [hmatrix, det_add_single_zero_zero]
          exact add_nonneg (hA hrows hcols)
            (mul_nonneg ht <| hA (hrows.comp Fin.strictMono_succ)
              (hcols.comp Fin.strictMono_succ))
        · have hcols_ne : ∀ j, cols j ≠ 0 := by
            intro j hj
            apply hc
            apply le_antisymm
            · simpa [hj] using hcols.monotone (Fin.zero_le j)
            · exact Fin.zero_le _
          have hmatrix :
              (A + Matrix.single 0 0 t).submatrix rows cols =
                A.submatrix rows cols := by
            ext i j
            simp [ne_comm, hcols_ne j]
          rw [hmatrix]
          exact hA hrows hcols
      · have hrows_ne : ∀ i, rows i ≠ 0 := by
          intro i hi
          apply hr
          apply le_antisymm
          · simpa [hi] using hrows.monotone (Fin.zero_le i)
          · exact Fin.zero_le _
        have hmatrix :
            (A + Matrix.single 0 0 t).submatrix rows cols =
              A.submatrix rows cols := by
          ext i j
          simp [ne_comm, hrows_ne i]
        rw [hmatrix]
        exact hA hrows hcols

end Matrix
