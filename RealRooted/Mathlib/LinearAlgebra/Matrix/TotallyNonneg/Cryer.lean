import RealRooted.Mathlib.LinearAlgebra.Matrix.TotallyNonneg

/-!
# Trailing initial-column minors

This file records the bordered-minor step used in the finite Cryer criterion.
It transfers initial-column flag minors to a trailing block under a positive
leading pivot; the full criterion remains separate.
-/

namespace Matrix

/-- Bordering a trailing initial-column minor with row and column zero factors
its determinant when the first row is zero away from the pivot. -/
theorem det_zero_succRows_initialColumns_eq
    {R : Type*} [CommRing R] {N m : ℕ}
    (A : Matrix (Fin (N + 1)) (Fin (N + 1)) R) (hm : m ≤ N)
    (rows : Fin m → Fin N) (hzero : ∀ j : Fin N, A 0 j.succ = 0) :
    (A.submatrix (Fin.cases 0 fun i => (rows i).succ)
      (Fin.castLE (Nat.succ_le_succ hm))).det =
      A 0 0 * ((A.submatrix Fin.succ Fin.succ).submatrix rows (Fin.castLE hm)).det := by
  let M := A.submatrix (Fin.cases 0 fun i => (rows i).succ)
    (Fin.castLE (Nat.succ_le_succ hm))
  have hzeroM : ∀ j : Fin m, M 0 j.succ = 0 := by
    intro j
    dsimp [M]
    convert hzero (Fin.castLE hm j) using 1
    apply congrArg (fun j : Fin (N + 1) => A 0 j)
    exact Fin.ext rfl
  rw [show A.submatrix (Fin.cases 0 fun i => (rows i).succ)
      (Fin.castLE (Nat.succ_le_succ hm)) = M from rfl]
  rw [Matrix.det_succ_row_zero M, Fin.sum_univ_succ]
  have htail : ∑ j : Fin m,
      (-1 : R) ^ ((j.succ : Fin (m + 1)) : ℕ) * M 0 j.succ *
        (M.submatrix Fin.succ j.succ.succAbove).det = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    rw [hzeroM j]
    simp
  rw [htail]
  simp only [Fin.val_zero, pow_zero, one_mul]
  have htrailing : M.submatrix Fin.succ (0 : Fin (m + 1)).succAbove =
      (A.submatrix Fin.succ Fin.succ).submatrix rows (Fin.castLE hm) := by
    ext i j
    simp [M]
  rw [htrailing]
  simp [M]

/-- A positive leading pivot transfers a bordered initial-column flag minor
to the corresponding trailing-block initial-column minor. -/
theorem nonneg_trailing_initialColumns_of_nonneg_zero_succRows
    {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    {N m : ℕ} (A : Matrix (Fin (N + 1)) (Fin (N + 1)) R) (hm : m ≤ N)
    (rows : Fin m → Fin N) (hzero : ∀ j : Fin N, A 0 j.succ = 0)
    (hdiag : 0 < A 0 0)
    (hflag : 0 ≤ (A.submatrix (Fin.cases 0 fun i => (rows i).succ)
      (Fin.castLE (Nat.succ_le_succ hm))).det) :
    0 ≤ ((A.submatrix Fin.succ Fin.succ).submatrix rows (Fin.castLE hm)).det := by
  rw [det_zero_succRows_initialColumns_eq A hm rows hzero] at hflag
  exact nonneg_of_mul_nonneg_right hflag hdiag

end Matrix
