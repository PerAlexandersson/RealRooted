import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Matrix.Rank
import RealRooted.Mathlib.LinearAlgebra.Matrix.SignRegularVariation

/-!
# Rank-deficient sign-consistent matrices

This file develops the rank-deficient induction in Karlin, *Total Positivity*,
Volume I, Chapter V, Section 1, Theorem 1.3. The first lemmas formalize the
selected-row kernel perturbation in equations (1.1) on printed pages 221--222.
-/

/-- A finite matrix of rank `r` has a nonzero `r`-minor with increasingly
ordered row and column selectors. -/
theorem Matrix.exists_ordered_minor_ne_zero_of_rank_eq
    {R : Type*} [Field R] {n m r : ℕ}
    (A : Matrix (Fin n) (Fin m) R) (hrank : A.rank = r) :
    ∃ rows : Fin r → Fin n, ∃ cols : Fin r → Fin m,
      StrictMono rows ∧ StrictMono cols ∧
        (A.submatrix rows cols).det ≠ 0 := by
  obtain ⟨κ, a, ha, hspan, hli⟩ :=
    exists_linearIndependent' R A.col
  letI : Finite κ := Finite.of_injective a ha
  letI : Fintype κ := Fintype.ofFinite κ
  have hcard : Fintype.card κ = r := by
    calc
      Fintype.card κ =
          Module.finrank R (Submodule.span R (Set.range (A.col ∘ a))) :=
        (finrank_span_eq_card hli).symm
      _ = Module.finrank R (Submodule.span R (Set.range A.col)) := by
        rw [hspan]
      _ = A.rank := (Matrix.rank_eq_finrank_span_cols A).symm
      _ = r := hrank
  let e : Fin r ≃ κ := (Fintype.equivFinOfCardEq hcard).symm
  let f : Fin r → Fin m := a ∘ e
  have hf : Function.Injective f := ha.comp e.injective
  have hli_f : LinearIndependent R (A.col ∘ f) := by
    simpa only [f, Function.comp_assoc] using hli.comp e e.injective
  let B : Matrix (Fin n) (Fin r) R := A.submatrix id f
  have hB : Function.Injective B.mulVec := by
    rw [Matrix.mulVec_injective_iff]
    change LinearIndependent R (A.col ∘ f)
    exact hli_f
  obtain ⟨rows, hrows, hdet⟩ :=
    Matrix.exists_ordered_minor_ne_zero_of_mulVec_injective
      B hB id strictMono_id
  have hdetf : (A.submatrix rows f).det ≠ 0 := by
    simpa only [B, Matrix.submatrix_submatrix, Function.id_comp,
      Function.comp_id] using hdet
  obtain ⟨s, p, hp⟩ :=
    Set.powersetCard.exists_orderEmb_comp_perm_eq_of_injective f hf
  let cols : Fin r ↪o Fin m := Set.powersetCard.ofFinEmbEquiv.symm s
  refine ⟨rows, cols, hrows, cols.strictMono, ?_⟩
  intro hzero
  apply hdetf
  have hmatrix :
      A.submatrix rows f =
        (A.submatrix rows cols).submatrix id p := by
    ext i j
    simp only [Matrix.submatrix_apply, id_eq]
    rw [hp j]
  rw [hmatrix, Matrix.det_permute', hzero, mul_zero]

/-- Perturbing coefficients along a vector annihilated by a selected-row
submatrix does not change the selected coordinates of the matrix-vector
product. -/
theorem Matrix.mulVec_add_smul_apply_eq_of_submatrix_mulVec_eq_zero
    {n m k : ℕ} (A : Matrix (Fin n) (Fin m) ℝ)
    (rows : Fin k → Fin n) (c z : Fin m → ℝ)
    (hz : (A.submatrix rows id).mulVec z = 0)
    (t : ℝ) (i : Fin k) :
    A.mulVec (c + t • z) (rows i) = A.mulVec c (rows i) := by
  have hzi : A.mulVec z (rows i) = 0 := by
    have hi := congrFun hz i
    simpa only [Matrix.mulVec, dotProduct, Matrix.submatrix_apply, id_eq,
      Pi.zero_apply] using hi
  rw [Matrix.mulVec_add, Matrix.mulVec_smul]
  simp [hzi]

/-- A selected alternating witness survives Karlin's kernel perturbation of
the coefficient vector. -/
theorem Fin.StrictlyAlternates.matrix_mulVec_add_smul
    {n m k : ℕ} {A : Matrix (Fin n) (Fin m) ℝ}
    {rows : Fin (k + 1) → Fin n} {c z : Fin m → ℝ}
    (h : StrictlyAlternates (fun i => A.mulVec c (rows i)))
    (hz : (A.submatrix rows id).mulVec z = 0)
    (t : ℝ) :
    StrictlyAlternates (fun i => A.mulVec (c + t • z) (rows i)) := by
  intro i
  change
    A.mulVec (c + t • z) (rows i.castSucc) *
      A.mulVec (c + t • z) (rows i.succ) < 0
  have heq (j : Fin (k + 1)) :=
    A.mulVec_add_smul_apply_eq_of_submatrix_mulVec_eq_zero rows c z hz t j
  rw [heq i.castSucc, heq i.succ]
  exact h i
