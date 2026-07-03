module

public import RealRooted.Mathlib.LinearAlgebra.Matrix.Determinant.Basic

public section

namespace Matrix
variable {ι κ R : Type*} [PartialOrder ι] [PartialOrder κ] [CommRing R] [PartialOrder R]
  {M : Matrix ι ι R} {i j : ι} {f g : κ → ι}

/-- A matrix is totally nonnegative if all its finite minors have nonnegative determinant. -/
@[expose]
def IsTotallyNonneg (M : Matrix ι ι R) : Prop :=
  ∀ ⦃n : ℕ⦄ ⦃rows cols : Fin n → ι⦄, StrictMono rows → StrictMono cols →
    0 ≤ (M.submatrix rows cols).det

protected lemma IsTotallyNonneg.submatrix (hM : M.IsTotallyNonneg) (hf : StrictMono f)
    (hg : StrictMono g) : (M.submatrix f g).IsTotallyNonneg :=
  fun n rows cols hrows hcols ↦ by simpa using hM (hf.comp hrows) (hg.comp hcols)

lemma IsTotallyNonneg.nonneg (hM : M.IsTotallyNonneg) (i j : ι) : 0 ≤ M i j := by
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
      have : Set.range rows ⊆ Set.range cols := by
        rintro _ ⟨i, rfl⟩
        exact hcon i
      have hcard_rows : (Set.range rows).toFinset.card = n := by
        rw [Set.toFinset_card, Set.card_range_of_injective hrows.injective, Fintype.card_fin]
      have hcard_cols : (Set.range cols).toFinset.card = n := by
        rw [Set.toFinset_card, Set.card_range_of_injective hcols.injective, Fintype.card_fin]
      have heq_set : Set.range rows = Set.range cols := by
        rw [← Set.toFinset_inj]
        refine Finset.eq_of_subset_of_card_le ?_ (by simp_all)
        intro x hx
        exact Set.mem_toFinset.mpr (this (Set.mem_toFinset.mp hx))
      simp_all
    rcases hnot with ⟨i, hi⟩
    have hrow : ∀ j : Fin n, ((1 : Matrix ℕ ℕ R).submatrix rows cols) i j = 0 := by
      intro j
      simp only [submatrix_apply, one_apply]
      split
      · exact (hi ⟨j, ‹rows i = cols j›.symm⟩).elim
      · rfl
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
  have key :
      M (rows 0) (cols 0) * N (rows 0) (cols 0) *
            (M (rows 1) (cols 1) * N (rows 1) (cols 1)) -
          M (rows 0) (cols 1) * N (rows 0) (cols 1) *
            (M (rows 1) (cols 0) * N (rows 1) (cols 0)) =
        (M (rows 0) (cols 0) * M (rows 1) (cols 1) -
              M (rows 0) (cols 1) * M (rows 1) (cols 0)) *
            (N (rows 0) (cols 0) * N (rows 1) (cols 1)) +
          M (rows 0) (cols 1) * M (rows 1) (cols 0) *
            (N (rows 0) (cols 0) * N (rows 1) (cols 1) -
              N (rows 0) (cols 1) * N (rows 1) (cols 0)) := by
    ring
  rw [key]
  exact add_nonneg h1 h2

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
  · have hlt : 2 < Nat.succ (Nat.succ (Nat.succ n)) :=
      Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.zero_lt_succ n))
    exact (not_lt_of_ge hn hlt).elim

end Matrix
