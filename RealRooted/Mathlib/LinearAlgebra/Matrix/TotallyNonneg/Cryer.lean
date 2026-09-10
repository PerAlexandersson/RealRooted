import RealRooted.Mathlib.LinearAlgebra.Matrix.TotallyNonneg

/-!
# Trailing initial-column minors

This file records the bordered-minor step used in the finite Cryer criterion.
It transfers initial-column flag minors to a trailing block under a positive
leading pivot; the full criterion remains separate.
-/

namespace Matrix

/-- A square matrix has nonnegative initial-column flag minors when every
minor with arbitrary ordered rows and the first consecutive columns has
nonnegative determinant. -/
def HasNonnegInitialColumnMinors {R : Type*} [CommRing R] [PartialOrder R]
    {N : ℕ} (A : Matrix (Fin N) (Fin N) R) : Prop :=
  ∀ ⦃m : ℕ⦄ (hm : m ≤ N) (rows : Fin m → Fin N), StrictMono rows →
    0 ≤ (A.submatrix rows (Fin.castLE hm)).det

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

/-- Initial-column flag minors are inherited by the trailing block after a
positive first-row pivot. -/
theorem HasNonnegInitialColumnMinors.trailing
    {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    {N : ℕ} (A : Matrix (Fin (N + 1)) (Fin (N + 1)) R)
    (hA : A.HasNonnegInitialColumnMinors)
    (hzero : ∀ j : Fin N, A 0 j.succ = 0) (hdiag : 0 < A 0 0) :
    (A.submatrix Fin.succ Fin.succ).HasNonnegInitialColumnMinors := by
  intro m hm rows hrows
  apply nonneg_trailing_initialColumns_of_nonneg_zero_succRows A hm rows hzero hdiag
  apply hA (Nat.succ_le_succ hm) (Fin.cases 0 fun i => (rows i).succ)
  intro i j hij
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
  · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
    · exact (lt_irrefl _ hij).elim
    · simp
  · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
    · simp at hij
    · exact Fin.succ_lt_succ_iff.mpr (hrows (Fin.succ_lt_succ_iff.mp hij))

/-- A first row which vanishes away from its pivot gives the corresponding
trailing determinant factorization. -/
theorem det_eq_firstEntry_mul_det_trailing
    {R : Type*} [CommRing R] {N : ℕ}
    (A : Matrix (Fin (N + 1)) (Fin (N + 1)) R)
    (hzero : ∀ j : Fin N, A 0 j.succ = 0) :
    A.det = A 0 0 * (A.submatrix Fin.succ Fin.succ).det := by
  have h := det_zero_succRows_initialColumns_eq A (Nat.le_refl N) (fun i => i) hzero
  calc
    A.det = (A.submatrix (Fin.cases 0 fun i : Fin N => i.succ)
        (Fin.castLE (Nat.succ_le_succ (Nat.le_refl N)))).det := by
      congr 1
      ext i j
      rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨k, rfl⟩ <;> rfl
    _ = A 0 0 * ((A.submatrix Fin.succ Fin.succ).submatrix (fun i => i)
        (Fin.castLE (Nat.le_refl N))).det := h
    _ = A 0 0 * (A.submatrix Fin.succ Fin.succ).det := by
      congr 1

/-- Bordering a trailing minor with row and column zero factors its determinant
when the first row is zero away from the pivot. -/
theorem det_zero_succRows_succCols_eq
    {R : Type*} [CommRing R] {N m : ℕ}
    (A : Matrix (Fin (N + 1)) (Fin (N + 1)) R)
    (rows cols : Fin m → Fin N) (hzero : ∀ j : Fin N, A 0 j.succ = 0) :
    (A.submatrix (Fin.cases 0 fun i => (rows i).succ)
      (Fin.cases 0 fun j => (cols j).succ)).det =
      A 0 0 * ((A.submatrix Fin.succ Fin.succ).submatrix rows cols).det := by
  let M := A.submatrix (Fin.cases 0 fun i => (rows i).succ)
    (Fin.cases 0 fun j => (cols j).succ)
  have hzeroM : ∀ j : Fin m, M 0 j.succ = 0 := by
    intro j
    dsimp [M]
    exact hzero (cols j)
  rw [show A.submatrix (Fin.cases 0 fun i => (rows i).succ)
      (Fin.cases 0 fun j => (cols j).succ) = M from rfl]
  rw [det_eq_firstEntry_mul_det_trailing M hzeroM]
  have htrailing : M.submatrix Fin.succ Fin.succ =
      (A.submatrix Fin.succ Fin.succ).submatrix rows cols := by
    ext i j
    simp [M]
  rw [htrailing]
  simp [M]

/-- A nonnegative first pivot and trailing total nonnegativity give
nonnegativity of every minor whose selected first row and column are zero. -/
theorem nonneg_of_isTotallyNonneg_trailing_zero_zero
    {R : Type*} [CommRing R] [PartialOrder R] [IsOrderedRing R]
    {N m : ℕ} (A : Matrix (Fin (N + 1)) (Fin (N + 1)) R)
    (rows cols : Fin m → Fin N) (hzero : ∀ j : Fin N, A 0 j.succ = 0)
    (hdiag : 0 ≤ A 0 0)
    (hB : (A.submatrix Fin.succ Fin.succ).IsTotallyNonneg)
    (hrows : StrictMono rows) (hcols : StrictMono cols) :
    0 ≤ (A.submatrix (Fin.cases 0 fun i => (rows i).succ)
      (Fin.cases 0 fun j => (cols j).succ)).det := by
  rw [det_zero_succRows_succCols_eq A rows cols hzero]
  exact mul_nonneg hdiag (hB hrows hcols)

/-- A nonzero determinant and nonnegative initial-column flag minors force a
positive first pivot and a nonzero trailing determinant. -/
theorem HasNonnegInitialColumnMinors.pivot_pos_and_trailing_det_ne_zero
    {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    {N : ℕ} (A : Matrix (Fin (N + 1)) (Fin (N + 1)) R)
    (hA : A.HasNonnegInitialColumnMinors)
    (hzero : ∀ j : Fin N, A 0 j.succ = 0) (hdet : A.det ≠ 0) :
    0 < A 0 0 ∧ (A.submatrix Fin.succ Fin.succ).det ≠ 0 := by
  rw [det_eq_firstEntry_mul_det_trailing A hzero] at hdet
  obtain ⟨hpivot, htrailing⟩ := mul_ne_zero_iff.mp hdet
  have hnonneg : 0 ≤ A 0 0 := by
    simpa using hA (m := 1) (by simp) ![0] (by simp)
  exact ⟨lt_of_le_of_ne hnonneg (Ne.symm hpivot), htrailing⟩

/-- If the trailing block is totally nonnegative, then every ordered minor
whose selected columns all avoid column zero is nonnegative. -/
theorem nonneg_of_isTotallyNonneg_trailing
    {R : Type*} [CommRing R] [PartialOrder R]
    {N : ℕ} (A : Matrix (Fin (N + 1)) (Fin (N + 1)) R)
    (hzero : ∀ j : Fin N, A 0 j.succ = 0)
    (hB : (A.submatrix Fin.succ Fin.succ).IsTotallyNonneg)
    {n : ℕ} (rows : Fin n → Fin (N + 1)) (cols : Fin n → Fin N)
    (hrows : StrictMono rows) (hcols : StrictMono cols) :
    0 ≤ (A.submatrix rows (fun j => (cols j).succ)).det := by
  cases n with
  | zero =>
    simpa using hB (rows := cols) (cols := cols) hcols hcols
  | succ n =>
    by_cases hfirst : rows 0 = 0
    · have hrow : ∀ j : Fin (n + 1),
          (A.submatrix rows (fun j => (cols j).succ)) 0 j = 0 := by
        intro j
        simpa [hfirst] using hzero (cols j)
      rw [det_eq_zero_of_row_eq_zero (0 : Fin (n + 1)) hrow]
    · have hrows_ne_zero : ∀ i, rows i ≠ 0 := by
        intro i hzeroi
        apply hfirst
        apply Fin.le_zero_iff.mp
        simpa [hzeroi] using hrows.monotone (Fin.zero_le i)
      let rows' : Fin (n + 1) → Fin N := fun i => (rows i).pred (hrows_ne_zero i)
      have hrows' : StrictMono rows' := by
        intro i j hij
        exact Fin.pred_lt_pred_iff.mpr (hrows hij)
      have heq : A.submatrix rows (fun j => (cols j).succ) =
          (A.submatrix Fin.succ Fin.succ).submatrix rows' cols := by
        ext i j
        simp [rows']
      rw [heq]
      exact hB hrows' hcols

end Matrix
