import RealRooted.Mathlib.LinearAlgebra.Matrix.Determinant.Plucker
import RealRooted.Mathlib.Order.Fin.Tuple
import RealRooted.Mathlib.Data.Fin.Basic

/-!
# Strict consecutive-column minors

This leaf derives strict positivity of every ordered minor of a rectangular
matrix from strict positivity on consecutive column intervals. It is the
strict algebraic component of the finite Cryer route; the non-strict limiting
argument remains separate.
-/

namespace Matrix

private theorem det_delete_interior_pos_of_ordered_plucker
    {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] {q : ℕ}
    (M : Matrix (Fin (q + 2)) (Fin (q + 3)) R) (b : Fin (q + 1))
    (hpivot : 0 < (M.submatrix Fin.castSucc
      (fun j : Fin (q + 1) => j.castSucc.succ)).det)
    (hdeleteLast : 0 < (M.submatrix id Fin.castSucc).det)
    (hdeleteZero : 0 < (M.submatrix id Fin.succ).det)
    (hAB : 0 < (M.submatrix Fin.castSucc
      (fun j : Fin (q + 1) => (b.castSucc.succAbove j).succ)).det)
    (hBC : 0 < (M.submatrix Fin.castSucc
      (fun j : Fin (q + 1) => (b.succ.succAbove j).castSucc)).det) :
    0 < (M.submatrix id b.castSucc.succ.succAbove).det := by
  have h := det_ordered_delete_column_plucker M b (ne_of_gt hpivot)
  dsimp at h
  simp only [Fin.succAbove_last] at h
  have hsum : 0 <
      (M.submatrix id Fin.castSucc).det *
          (M.submatrix Fin.castSucc
            (fun j : Fin (q + 1) => (b.castSucc.succAbove j).succ)).det +
        (M.submatrix id Fin.succ).det *
          (M.submatrix Fin.castSucc
            (fun j : Fin (q + 1) => (b.succ.succAbove j).castSucc)).det :=
    add_pos (mul_pos hdeleteLast hAB) (mul_pos hdeleteZero hBC)
  have hprod : 0 < (M.submatrix id b.castSucc.succ.succAbove).det *
      (M.submatrix Fin.castSucc
        (fun j : Fin (q + 1) => j.castSucc.succ)).det := by
    rw [h]
    exact hsum
  rcases (mul_pos_iff.mp hprod) with hpos | hneg
  · exact hpos.1
  · exact (not_lt_of_ge hpivot.le hneg.2).elim

private theorem strict_gap_of_smaller_minors
    {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    {n N q : Nat} (A : Matrix (Fin n) (Fin N) R)
    (rows : Fin (q + 2) → Fin n) (cols : Fin (q + 2) → Fin N)
    (hrows : StrictMono rows) (_hcols : StrictMono cols)
    (u : Fin (q + 3) → Fin N) (r : Fin (q + 1))
    (hu : StrictMono u)
    (hdel : u ∘ r.castSucc.succ.succAbove = cols)
    (hsmall : ∀ (rows' : Fin (q + 1) → Fin n) (cols' : Fin (q + 1) → Fin N),
      StrictMono rows' → StrictMono cols' → 0 < (A.submatrix rows' cols').det)
    (hspan : ∀ (cols' : Fin (q + 2) → Fin N), StrictMono cols' →
      (cols' (Fin.last (q + 1))).val - (cols' 0).val <
        (cols (Fin.last (q + 1))).val - (cols 0).val →
      0 < (A.submatrix rows cols').det) :
    0 < (A.submatrix rows cols).det := by
  let M := A.submatrix rows u
  have hrowsSmall : StrictMono (rows ∘ Fin.castSucc) :=
    hrows.comp Fin.strictMono_castSucc
  have hmiddle : StrictMono (fun j : Fin (q + 1) => j.castSucc.succ) :=
    Fin.strictMono_succ.comp Fin.strictMono_castSucc
  have hABcols : StrictMono (fun j : Fin (q + 1) =>
      (r.castSucc.succAbove j).succ) :=
    Fin.strictMono_succ.comp (Fin.strictMono_succAbove r.castSucc)
  have hBCcols : StrictMono (fun j : Fin (q + 1) =>
      (r.succ.succAbove j).castSucc) :=
    Fin.strictMono_castSucc.comp (Fin.strictMono_succAbove r.succ)
  have hpivot : 0 < (M.submatrix Fin.castSucc
      (fun j : Fin (q + 1) => j.castSucc.succ)).det := by
    change 0 < (A.submatrix (rows ∘ Fin.castSucc)
      (u ∘ fun j : Fin (q + 1) => j.castSucc.succ)).det
    exact hsmall _ _ hrowsSmall (hu.comp hmiddle)
  have hAB : 0 < (M.submatrix Fin.castSucc
      (fun j : Fin (q + 1) => (r.castSucc.succAbove j).succ)).det := by
    change 0 < (A.submatrix (rows ∘ Fin.castSucc)
      (u ∘ fun j : Fin (q + 1) => (r.castSucc.succAbove j).succ)).det
    exact hsmall _ _ hrowsSmall (hu.comp hABcols)
  have hBC : 0 < (M.submatrix Fin.castSucc
      (fun j : Fin (q + 1) => (r.succ.succAbove j).castSucc)).det := by
    change 0 < (A.submatrix (rows ∘ Fin.castSucc)
      (u ∘ fun j : Fin (q + 1) => (r.succ.succAbove j).castSucc)).det
    exact hsmall _ _ hrowsSmall (hu.comp hBCcols)
  have hu0 : u 0 = cols 0 := by
    simpa only [Function.comp_apply, Fin.succ_castSucc, Fin.succAbove_zero_of_interior] using
      congrFun hdel 0
  have hulast : u (Fin.last (q + 2)) = cols (Fin.last (q + 1)) := by
    simpa only [Function.comp_apply, Fin.succ_castSucc, Fin.succAbove_last_of_interior] using
      congrFun hdel (Fin.last (q + 1))
  have hdeleteLastCols : StrictMono (u ∘ Fin.castSucc) := hu.comp Fin.strictMono_castSucc
  have hdeleteZeroCols : StrictMono (u ∘ Fin.succ) := hu.comp Fin.strictMono_succ
  have hdeleteLastSpan :
      ((u ∘ Fin.castSucc) (Fin.last (q + 1))).val - ((u ∘ Fin.castSucc) 0).val <
        (cols (Fin.last (q + 1))).val - (cols 0).val := by
    rw [← hu0, ← hulast]
    exact hu.span_castSucc_last_lt
  have hdeleteZeroSpan :
      ((u ∘ Fin.succ) (Fin.last (q + 1))).val - ((u ∘ Fin.succ) 0).val <
        (cols (Fin.last (q + 1))).val - (cols 0).val := by
    rw [← hu0, ← hulast]
    simpa only [Function.comp_apply, Fin.succ_last] using hu.span_succ_zero_lt
  have hdeleteLast : 0 < (M.submatrix id Fin.castSucc).det := by
    change 0 < (A.submatrix rows (u ∘ Fin.castSucc)).det
    exact hspan _ hdeleteLastCols hdeleteLastSpan
  have hdeleteZero : 0 < (M.submatrix id Fin.succ).det := by
    change 0 < (A.submatrix rows (u ∘ Fin.succ)).det
    exact hspan _ hdeleteZeroCols hdeleteZeroSpan
  have hgap := det_delete_interior_pos_of_ordered_plucker M r hpivot
    hdeleteLast hdeleteZero hAB hBC
  change (A.submatrix rows (u ∘ r.castSucc.succ.succAbove)).det > 0 at hgap
  rwa [hdel] at hgap

/-- Strict positivity of all arbitrary ordered minors follows from strict positivity on
consecutive column intervals. -/
theorem pos_minor_of_pos_consecutive_column_minors
    {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    {n N : Nat} (A : Matrix (Fin n) (Fin N) R)
    (hconsecutive : ∀ {k c : Nat} (hkc : c + k ≤ N)
      (rows : Fin k → Fin n), StrictMono rows →
      0 < (A.submatrix rows (fun j => Fin.castLE hkc (Fin.natAdd c j))).det) :
    ∀ {k : Nat} (rows : Fin k → Fin n) (cols : Fin k → Fin N),
      StrictMono rows → StrictMono cols → 0 < (A.submatrix rows cols).det := by
  intro k
  refine Nat.strongRecOn k ?_
  intro k ih rows cols hrows hcols
  cases k with
  | zero => simp
  | succ k =>
    cases k with
    | zero =>
      have hkc : (cols 0).val + 1 ≤ N := Nat.succ_le_of_lt (cols 0).isLt
      have hcols_eq : cols = fun j => Fin.castLE hkc (Fin.natAdd (cols 0).val j) := by
        funext j
        apply Fin.ext
        fin_cases j
        simp [Fin.natAdd]
      rw [hcols_eq]
      exact hconsecutive hkc rows hrows
    | succ q =>
      let initialSpan := (cols (Fin.last (q + 1))).val - (cols 0).val
      refine Nat.strongRecOn initialSpan
        (motive := fun span =>
          ∀ cols : Fin (q + 2) → Fin N, StrictMono cols →
            (cols (Fin.last (q + 1))).val - (cols 0).val = span →
              0 < (A.submatrix rows cols).det) ?_ cols hcols rfl
      intro span ihspan cols hcols hspan
      rcases hcols.consecutive_or_exists_missing_between with hcon | hgap
      · let c := (cols 0).val
        have hlast : c + (q + 1) < N := by
          calc
            c + (q + 1) = (cols (Fin.last (q + 1))).val := by
              simpa [c] using (hcon (Fin.last (q + 1))).symm
            _ < N := (cols (Fin.last (q + 1))).isLt
        have hkc : c + (q + 2) ≤ N := by
          simpa [Nat.succ_eq_add_one, Nat.add_assoc] using Nat.succ_le_of_lt hlast
        have hcols_eq : cols = fun j => Fin.castLE hkc (Fin.natAdd c j) := by
          funext j
          apply Fin.ext
          change (cols j).val = c + j.val
          exact hcon j
        rw [hcols_eq]
        exact hconsecutive hkc rows hrows
      · obtain ⟨b, hleft, hright, hb⟩ := hgap
        obtain ⟨u, r, hu, _hrb, hdel⟩ :=
          hcols.exists_ordered_interior_insert hb hleft hright
        have hsmall : ∀ (rows' : Fin (q + 1) → Fin n) (cols' : Fin (q + 1) → Fin N),
            StrictMono rows' → StrictMono cols' → 0 < (A.submatrix rows' cols').det := by
          intro rows' cols' hrows' hcols'
          exact ih (q + 1) (by lia) rows' cols' hrows' hcols'
        have hspan' : ∀ (cols' : Fin (q + 2) → Fin N), StrictMono cols' →
            (cols' (Fin.last (q + 1))).val - (cols' 0).val <
              (cols (Fin.last (q + 1))).val - (cols 0).val →
            0 < (A.submatrix rows cols').det := by
          intro cols' hcols' hspan'
          refine ihspan _ (by simpa [hspan] using hspan') cols' hcols' rfl
        exact strict_gap_of_smaller_minors A rows cols hrows hcols u r hu hdel hsmall hspan'

end Matrix
