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

end Matrix
