module

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

/-- A matrix is totally nonnegative if all its finite minors have nonnegative determinant. -/
@[expose]
def IsTotallyNonneg (M : Matrix ι ι R) : Prop :=
  ∀ ⦃n : ℕ⦄ ⦃rows cols : Fin n → ι⦄, StrictMono rows → StrictMono cols →
    0 ≤ (M.submatrix rows cols).det

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

protected lemma IsTotallyNonneg.submatrix (hM : M.IsTotallyNonneg) (hf : StrictMono f)
    (hg : StrictMono g) : (M.submatrix f g).IsTotallyNonneg :=
  fun n rows cols hrows hcols ↦ by simpa using hM (hf.comp hrows) (hg.comp hcols)

lemma IsTotallyNonneg.nonneg (hM : M.IsTotallyNonneg) (i j : ι) : 0 ≤ M i j := by
  simpa using hM (rows := ![i]) (cols := ![j])

lemma IsTotallyNonnegRect.nonneg {M : Matrix ι κ R}
    (hM : M.IsTotallyNonnegRect) (i : ι) (j : κ) : 0 ≤ M i j := by
  simpa using hM (rows := ![i]) (cols := ![j])

variable [IsStrictOrderedRing R]

@[simp] protected lemma IsTotallyNonneg.zero : (0 : Matrix ι ι R).IsTotallyNonneg
  | 0 => by simp
  | n + 1 => by simp

theorem IsTotallyNonneg.one : (1 : Matrix ℕ ℕ R).IsTotallyNonneg := by
  intro n rows cols hrows hcols
  by_cases hrange : Set.range rows = Set.range cols
  · have heq : rows = cols := by
      have h_card : (Set.range rows).toFinset.card = n := by
        rw [Set.toFinset_card, Set.card_range_of_injective hrows.injective, Fintype.card_fin]
      have h_rows_eq := Finset.orderEmbOfFin_unique h_card (fun _ ↦ by simp) hrows
      have h_cols_eq := Finset.orderEmbOfFin_unique h_card (fun x ↦ by simp [hrange]) hcols
      grind
    rw [heq, submatrix_one cols hcols.injective]
    simp
  · have hnot : ∃ i : Fin n, rows i ∉ Set.range cols := by
      by_contra! hcon
      have : Set.range rows ⊆ Set.range cols := by grind
      have hcard_rows : (Set.range rows).toFinset.card = n := by
        rw [Set.toFinset_card, Set.card_range_of_injective hrows.injective, Fintype.card_fin]
      have hcard_cols : (Set.range cols).toFinset.card = n := by
        rw [Set.toFinset_card, Set.card_range_of_injective hcols.injective, Fintype.card_fin]
      have heq_set : Set.range rows = Set.range cols := by
        rw [← Set.toFinset_inj]
        refine Finset.eq_of_subset_of_card_le ?_ (by simp_all)
        grind
      simp_all
    rcases hnot with ⟨i, hi⟩
    have hrow : ∀ j : Fin n, ((1 : Matrix ℕ ℕ R).submatrix rows cols) i j = 0 := by
      intro j
      simp only [submatrix_apply, one_apply]
      grind
    exact det_eq_zero_of_row_eq_zero i hrow |>.ge

lemma IsTotallyNonneg.smul {M : Matrix ι ι R}
    (hM : M.IsTotallyNonneg) (c : R) (hc : 0 ≤ c) :
    (c • M).IsTotallyNonneg := by
  intro n rows cols hrows hcols
  change 0 ≤ (c • M.submatrix rows cols).det
  rw [Matrix.det_smul]
  exact mul_nonneg (by positivity) (hM hrows hcols)

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
