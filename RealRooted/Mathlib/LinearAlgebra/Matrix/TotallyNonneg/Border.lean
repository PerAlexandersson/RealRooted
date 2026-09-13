import RealRooted.Mathlib.LinearAlgebra.Matrix.TotallyNonneg.Cryer

/-!
# Zero borders of totally nonnegative matrices

This file proves that adjoining a nonnegative scalar as an isolated first
coordinate preserves total nonnegativity.  The theorem is phrased in terms of
the first row, first column, and trailing block so clients need not commit to a
particular block-matrix encoding.
-/

namespace Matrix

/-- A nonnegative isolated first coordinate and a totally nonnegative trailing
block give a totally nonnegative matrix. -/
theorem IsTotallyNonneg.of_zero_border
    {R : Type*} [CommRing R] [PartialOrder R] [IsOrderedRing R]
    {N : ℕ} (A : Matrix (Fin (N + 1)) (Fin (N + 1)) R)
    (hrow : ∀ j : Fin N, A 0 j.succ = 0)
    (hcol : ∀ i : Fin N, A i.succ 0 = 0)
    (hpivot : 0 ≤ A 0 0)
    (htrail : (A.submatrix Fin.succ Fin.succ).IsTotallyNonneg) :
    A.IsTotallyNonneg := by
  intro n rows cols hrows hcols
  cases n with
  | zero => simp
  | succ n =>
      by_cases hr0 : rows 0 = 0
      · by_cases hc0 : cols 0 = 0
        · have hrows_tail_ne : ∀ i : Fin n, rows i.succ ≠ 0 := by
            intro i hi
            have hlt := hrows (by simp : (0 : Fin (n + 1)) < i.succ)
            simp [hr0, hi] at hlt
          have hcols_tail_ne : ∀ j : Fin n, cols j.succ ≠ 0 := by
            intro j hj
            have hlt := hcols (by simp : (0 : Fin (n + 1)) < j.succ)
            simp [hc0, hj] at hlt
          let rows' : Fin n → Fin N := fun i =>
            (rows i.succ).pred (hrows_tail_ne i)
          let cols' : Fin n → Fin N := fun j =>
            (cols j.succ).pred (hcols_tail_ne j)
          have hrows' : StrictMono rows' := by
            intro i j hij
            exact Fin.pred_lt_pred_iff.mpr
              (hrows (Fin.succ_lt_succ_iff.mpr hij))
          have hcols' : StrictMono cols' := by
            intro i j hij
            exact Fin.pred_lt_pred_iff.mpr
              (hcols (Fin.succ_lt_succ_iff.mpr hij))
          have hrows_eq :
              (Fin.cases 0 fun i => (rows' i).succ) = rows := by
            funext i
            refine Fin.cases ?_ (fun j => ?_) i
            · exact hr0.symm
            · simp [rows']
          have hcols_eq :
              (Fin.cases 0 fun j => (cols' j).succ) = cols := by
            funext j
            refine Fin.cases ?_ (fun k => ?_) j
            · exact hc0.symm
            · simp [cols']
          rw [← hrows_eq, ← hcols_eq]
          exact nonneg_of_isTotallyNonneg_trailing_zero_zero
            A rows' cols' hrow hpivot htrail hrows' hcols'
        · have hcols_ne_zero : ∀ j : Fin (n + 1), cols j ≠ 0 := by
            intro j hj
            apply hc0
            apply Fin.le_zero_iff.mp
            simpa [hj] using hcols.monotone (Fin.zero_le j)
          have hminor_row : ∀ j : Fin (n + 1),
              (A.submatrix rows cols) 0 j = 0 := by
            intro j
            simpa [hr0] using hrow ((cols j).pred (hcols_ne_zero j))
          rw [det_eq_zero_of_row_eq_zero (0 : Fin (n + 1)) hminor_row]
      · by_cases hc0 : cols 0 = 0
        · have hrows_ne_zero : ∀ i : Fin (n + 1), rows i ≠ 0 := by
            intro i hi
            apply hr0
            apply Fin.le_zero_iff.mp
            simpa [hi] using hrows.monotone (Fin.zero_le i)
          have hminor_col : ∀ i : Fin (n + 1),
              (A.submatrix rows cols) i 0 = 0 := by
            intro i
            simpa [hc0] using hcol ((rows i).pred (hrows_ne_zero i))
          rw [det_eq_zero_of_column_eq_zero (0 : Fin (n + 1)) hminor_col]
        · have hrows_ne_zero : ∀ i : Fin (n + 1), rows i ≠ 0 := by
            intro i hi
            apply hr0
            apply Fin.le_zero_iff.mp
            simpa [hi] using hrows.monotone (Fin.zero_le i)
          have hcols_ne_zero : ∀ j : Fin (n + 1), cols j ≠ 0 := by
            intro j hj
            apply hc0
            apply Fin.le_zero_iff.mp
            simpa [hj] using hcols.monotone (Fin.zero_le j)
          let rows' : Fin (n + 1) → Fin N := fun i =>
            (rows i).pred (hrows_ne_zero i)
          let cols' : Fin (n + 1) → Fin N := fun j =>
            (cols j).pred (hcols_ne_zero j)
          have hrows' : StrictMono rows' := by
            intro i j hij
            exact Fin.pred_lt_pred_iff.mpr (hrows hij)
          have hcols' : StrictMono cols' := by
            intro i j hij
            exact Fin.pred_lt_pred_iff.mpr (hcols hij)
          have heq : A.submatrix rows cols =
              (A.submatrix Fin.succ Fin.succ).submatrix rows' cols' := by
            ext i j
            simp [rows', cols']
          rw [heq]
          exact htrail hrows' hcols'

end Matrix
