module

public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Data.Fin.Rev
public import Mathlib.LinearAlgebra.Matrix.Determinant.TotallyNonneg
public import RealRooted.Mathlib.LinearAlgebra.Matrix.Determinant.Basic

public section

namespace Matrix
variable {ι κ R : Type*} [PartialOrder ι] [PartialOrder κ] [CommRing R] [PartialOrder R]
  {M : Matrix ι ι R} {i j : ι} {f g : κ → ι}

/-- A rectangular matrix is totally nonnegative if all its square minors have
nonnegative determinant. -/
@[expose]
def IsTotallyNonnegRect (M : Matrix ι κ R) : Prop :=
  ∀ ⦃n : ℕ⦄ ⦃rows : Fin n → ι⦄ ⦃cols : Fin n → κ⦄,
    StrictMono rows → StrictMono cols → 0 ≤ (M.submatrix rows cols).det

/-- Square total nonnegativity as rectangular total nonnegativity. -/
protected lemma IsTotallyNonneg.toRect (hM : M.IsTotallyNonneg) :
    M.IsTotallyNonnegRect :=
  hM

/-- Rectangular total nonnegativity specializes to the square predicate. -/
protected lemma IsTotallyNonnegRect.toSquare (hM : M.IsTotallyNonnegRect) :
    M.IsTotallyNonneg :=
  hM

protected lemma IsTotallyNonnegRect.submatrix {ι' κ' : Type*}
    [PartialOrder ι'] [PartialOrder κ'] {M : Matrix ι κ R}
    (hM : M.IsTotallyNonnegRect) {rows : ι' → ι} {cols : κ' → κ}
    (hrows : StrictMono rows) (hcols : StrictMono cols) :
    (M.submatrix rows cols).IsTotallyNonnegRect :=
  fun n rows' cols' hrows' hcols' => by
    simpa using hM (hrows.comp hrows') (hcols.comp hcols')

protected lemma IsTotallyNonnegRect.transpose {M : Matrix ι κ R}
    (hM : M.IsTotallyNonnegRect) : M.transpose.IsTotallyNonnegRect := by
  intro n rows cols hrows hcols
  rw [← Matrix.det_transpose, transpose_submatrix]
  exact hM hcols hrows

/-- Simultaneously reversing the rows and columns of a finite totally
nonnegative matrix preserves total nonnegativity. -/
theorem IsTotallyNonneg.finRev {N : ℕ} {A : Matrix (Fin N) (Fin N) R}
    (hA : A.IsTotallyNonneg) :
    (Matrix.reindex Fin.revPerm Fin.revPerm A).IsTotallyNonneg := by
  intro n rows cols hrows hcols
  rw [← Matrix.det_submatrix_equiv_self Fin.revPerm]
  exact hA (fun _ _ h ↦ Fin.rev_lt_rev.2 (hrows (Fin.rev_lt_rev.2 h)))
    (fun _ _ h ↦ Fin.rev_lt_rev.2 (hcols (Fin.rev_lt_rev.2 h)))

lemma IsTotallyNonnegRect.nonneg {M : Matrix ι κ R}
    (hM : M.IsTotallyNonnegRect) (i : ι) (j : κ) : 0 ≤ M i j := by
  simpa only [Matrix.det_fin_one, Matrix.submatrix_apply, Matrix.cons_val_zero] using
    hM (rows := ![i]) (cols := ![j]) (Subsingleton.strictMono _) (Subsingleton.strictMono _)

variable [IsStrictOrderedRing R]

/-- Multiplying rows and columns by nonnegative scalars preserves total
nonnegativity. -/
protected lemma IsTotallyNonneg.scaleRowsCols {M : Matrix ι ι R}
    (hM : M.IsTotallyNonneg) (r c : ι → R)
    (hr : ∀ i, 0 ≤ r i) (hc : ∀ i, 0 ≤ c i) :
    (Matrix.of fun i j => r i * (c j * M i j)).IsTotallyNonneg := by
  intro n rows cols hrows hcols
  have hmatrix :
      (Matrix.of fun i j => r i * (c j * M i j)).submatrix rows cols =
        Matrix.of fun i j =>
          r (rows i) * (c (cols j) * (M.submatrix rows cols) i j) := by
    rfl
  rw [hmatrix]
  change 0 ≤ (Matrix.of fun i j => r (rows i) * (c (cols j) * M (rows i) (cols j))).det
  have hrow :
      (Matrix.of fun i j => r (rows i) * (c (cols j) * M (rows i) (cols j))).det =
        (∏ i, r (rows i)) *
          (Matrix.of fun i j => c (cols j) * M (rows i) (cols j)).det :=
    Matrix.det_mul_column (fun i => r (rows i))
      (Matrix.of fun i j => c (cols j) * M (rows i) (cols j))
  rw [hrow]
  change 0 ≤ (∏ i, r (rows i)) *
    (Matrix.of fun i j => c (cols j) * (M.submatrix rows cols) i j).det
  rw [Matrix.det_mul_row (fun j => c (cols j)) (M.submatrix rows cols)]
  exact mul_nonneg (Finset.prod_nonneg fun i _ => hr (rows i))
    (mul_nonneg (Finset.prod_nonneg fun j _ => hc (cols j))
      (hM hrows hcols))

/-- Every `2 × 2` minor of the entrywise product of two totally nonnegative
matrices is nonnegative.  The analogous statement is false for larger minors
of arbitrary totally nonnegative matrices. -/
theorem IsTotallyNonneg.hadamard_det_fin_two {M N : Matrix ι ι R}
    (hM : M.IsTotallyNonneg) (hN : N.IsTotallyNonneg) {rows cols : Fin 2 → ι}
    (hrows : StrictMono rows) (hcols : StrictMono cols) :
    0 ≤ ((Matrix.of fun i j => M i j * N i j).submatrix rows cols).det := by
  have hMdet := hM hrows hcols
  have hNdet := hN hrows hcols
  rw [Matrix.det_fin_two] at hMdet hNdet ⊢
  simp only [Matrix.submatrix_apply, Matrix.of_apply] at hMdet hNdet ⊢
  have hM01 : 0 ≤ M (rows 0) (cols 1) := hM.nonneg _ _
  have hM10 : 0 ≤ M (rows 1) (cols 0) := hM.nonneg _ _
  have hN00 : 0 ≤ N (rows 0) (cols 0) := hN.nonneg _ _
  have hN11 : 0 ≤ N (rows 1) (cols 1) := hN.nonneg _ _
  have h1 := mul_nonneg hMdet (mul_nonneg hN00 hN11)
  have h2 := mul_nonneg (mul_nonneg hM01 hM10) hNdet
  grind

/-- Every minor of size at most two of the entrywise product of two totally
nonnegative matrices is nonnegative. -/
theorem IsTotallyNonneg.hadamard_det_of_card_le_two {M N : Matrix ι ι R}
    (hM : M.IsTotallyNonneg) (hN : N.IsTotallyNonneg)
    {n : ℕ} {rows cols : Fin n → ι} (hrows : StrictMono rows) (hcols : StrictMono cols)
    (hn : n ≤ 2) :
    0 ≤ ((Matrix.of fun i j => M i j * N i j).submatrix rows cols).det := by
  rcases n with _ | n
  · simp
  rcases n with _ | n
  · rw [Matrix.det_fin_one]
    simp only [Matrix.submatrix_apply, Matrix.of_apply]
    exact mul_nonneg (hM.nonneg (rows 0) (cols 0)) (hN.nonneg (rows 0) (cols 0))
  rcases n with _ | n
  · exact hM.hadamard_det_fin_two hN hrows hcols
  · simp_all

end Matrix
