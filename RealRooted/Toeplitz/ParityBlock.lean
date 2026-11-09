module

import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
public import RealRooted.MatrixInterlacing.TotallyNonnegative
public import RealRooted.Toeplitz.HessenbergRows

/-!
# The block matrix of the parity lift

For a square matrix `A` of size `q = n + 1` whose upper triangle is constant down each column,
`A i j = c_j` for `i ≤ j`, the block matrix
`B = [[A, 𝟙 cᵀ], [0, A]]` of size `2 q` (`parityBlock A`, `c_j = A 0 j`) satisfies the same
hypotheses as `A`: nonnegative entries and ordered `2 × 2` minors (`Matrix.IsTP2`), weakly
decreasing columns, and `B i j = B j j` for `i ≤ j`. Its determinant polynomial is the square,
`det (I + X B) = det (I + X A) ^ 2` (`hessenbergDet_parityBlock`).
-/

@[expose] public section

open Polynomial Matrix

noncomputable section

namespace RealRooted

variable {n : ℕ}

/-- The block matrix `[[A, 𝟙 cᵀ], [0, A]]`, where `c_j = A 0 j`. -/
def parityBlock (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    Matrix (Fin (n + 1 + (n + 1))) (Fin (n + 1 + (n + 1))) ℝ :=
  Matrix.of fun i j => Fin.addCases
    (fun i' => Fin.addCases (fun j' => A i' j') (fun j' => A 0 j') j)
    (fun i' => Fin.addCases (fun _ => 0) (fun j' => A i' j') j) i

section Entries

variable (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (i j : Fin (n + 1))

@[simp] lemma parityBlock_castAdd_castAdd :
    parityBlock A (Fin.castAdd (n + 1) i) (Fin.castAdd (n + 1) j) = A i j := by
  simp only [parityBlock, Matrix.of_apply, Fin.addCases_left]

lemma parityBlock_castAdd_natAdd :
    parityBlock A (Fin.castAdd (n + 1) i) (Fin.natAdd (n + 1) j) = A 0 j := by
  simp only [parityBlock, Matrix.of_apply, Fin.addCases_left, Fin.addCases_right]

lemma parityBlock_natAdd_castAdd :
    parityBlock A (Fin.natAdd (n + 1) i) (Fin.castAdd (n + 1) j) = 0 := by
  simp only [parityBlock, Matrix.of_apply, Fin.addCases_left, Fin.addCases_right]

lemma parityBlock_natAdd_natAdd :
    parityBlock A (Fin.natAdd (n + 1) i) (Fin.natAdd (n + 1) j) = A i j := by
  simp only [parityBlock, Matrix.of_apply, Fin.addCases_right]

end Entries

section Properties

variable {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}

private lemma castAdd_le_castAdd_iff (i j : Fin (n + 1)) :
    Fin.castAdd (n + 1) i ≤ Fin.castAdd (n + 1) j ↔ i ≤ j := Iff.rfl

lemma castAdd_lt_natAdd (i j : Fin (n + 1)) :
    Fin.castAdd (n + 1) i < Fin.natAdd (n + 1) j := by
  rw [Fin.lt_def, Fin.val_castAdd, Fin.val_natAdd]
  lia [i.2]

lemma not_natAdd_le_castAdd (i j : Fin (n + 1)) :
    ¬ Fin.natAdd (n + 1) i ≤ Fin.castAdd (n + 1) j := by
  rw [Fin.le_def, Fin.val_castAdd, Fin.val_natAdd]
  lia [j.2]

/-- Nonnegative entries. -/
lemma parityBlock_nonneg (hnn : ∀ i j, 0 ≤ A i j) (i j : Fin (n + 1 + (n + 1))) :
    0 ≤ parityBlock A i j := by
  induction i using Fin.addCases <;> induction j using Fin.addCases <;>
    simp only [parityBlock_castAdd_castAdd, parityBlock_castAdd_natAdd,
      parityBlock_natAdd_castAdd, parityBlock_natAdd_natAdd, hnn, le_refl]

/-- The block matrix has constant upper-triangular columns. -/
lemma parityBlock_row_eq (hrow : ∀ ⦃i j : Fin (n + 1)⦄, i ≤ j → A i j = A j j)
    ⦃i j : Fin (n + 1 + (n + 1))⦄ (hij : i ≤ j) : parityBlock A i j = parityBlock A j j := by
  induction i using Fin.addCases with
  | left i =>
    induction j using Fin.addCases with
    | left j =>
      rw [parityBlock_castAdd_castAdd, parityBlock_castAdd_castAdd]
      exact hrow hij
    | right j =>
      rw [parityBlock_castAdd_natAdd, parityBlock_natAdd_natAdd]
      exact hrow (Fin.zero_le j)
  | right i =>
    induction j using Fin.addCases with
    | left j => exact absurd hij (not_natAdd_le_castAdd _ _)
    | right j =>
      rw [parityBlock_natAdd_natAdd, parityBlock_natAdd_natAdd]
      exact hrow ((Fin.natAdd_le_natAdd_iff _).mp hij)

/-- The columns of the block matrix weakly decrease. -/
lemma parityBlock_col_le (hnn : ∀ i j, 0 ≤ A i j)
    (hcol : ∀ ⦃i k j : Fin (n + 1)⦄, i ≤ k → A k j ≤ A i j)
    ⦃i k : Fin (n + 1 + (n + 1))⦄ (j : Fin (n + 1 + (n + 1))) (hik : i ≤ k) :
    parityBlock A k j ≤ parityBlock A i j := by
  induction i using Fin.addCases with
  | left i =>
    induction k using Fin.addCases with
    | left k =>
      induction j using Fin.addCases with
      | left j =>
        rw [parityBlock_castAdd_castAdd, parityBlock_castAdd_castAdd]
        exact hcol hik
      | right j => rw [parityBlock_castAdd_natAdd, parityBlock_castAdd_natAdd]
    | right k =>
      induction j using Fin.addCases with
      | left j =>
        rw [parityBlock_natAdd_castAdd, parityBlock_castAdd_castAdd]
        exact hnn i j
      | right j =>
        rw [parityBlock_natAdd_natAdd, parityBlock_castAdd_natAdd]
        exact hcol (Fin.zero_le k)
  | right i =>
    induction k using Fin.addCases with
    | left k => exact absurd hik (not_natAdd_le_castAdd _ _)
    | right k =>
      induction j using Fin.addCases with
      | left j => rw [parityBlock_natAdd_castAdd, parityBlock_natAdd_castAdd]
      | right j =>
        rw [parityBlock_natAdd_natAdd, parityBlock_natAdd_natAdd]
        exact hcol ((Fin.natAdd_le_natAdd_iff _).mp hik)

private lemma not_natAdd_lt_castAdd (i j : Fin (n + 1)) :
    ¬ Fin.natAdd (n + 1) i < Fin.castAdd (n + 1) j := fun h =>
  not_natAdd_le_castAdd i j h.le

/-- The block matrix is `TP2` when `A` is `TP2` with decreasing columns. -/
lemma parityBlock_isTP2 (hA : A.IsTP2)
    (hcol : ∀ ⦃i k j : Fin (n + 1)⦄, i ≤ k → A k j ≤ A i j) : (parityBlock A).IsTP2 := by
  refine ⟨parityBlock_nonneg hA.nonneg, fun i₁ i₂ j₁ j₂ hi hj => ?_⟩
  induction i₁ using Fin.addCases with
  | left i₁ =>
    induction i₂ using Fin.addCases with
    | left i₂ =>
      induction j₁ using Fin.addCases with
      | left j₁ =>
        induction j₂ using Fin.addCases with
        | left j₂ =>
          simp only [parityBlock_castAdd_castAdd]
          exact hA.minor_nonneg hi hj
        | right j₂ =>
          simp only [parityBlock_castAdd_castAdd, parityBlock_castAdd_natAdd]
          nlinarith [mul_nonneg (hA.nonneg 0 j₂) (sub_nonneg.mpr (hcol hi.le (j := j₁)))]
      | right j₁ =>
        induction j₂ using Fin.addCases with
        | left j₂ => exact absurd hj (not_natAdd_lt_castAdd _ _)
        | right j₂ =>
          simp only [parityBlock_castAdd_natAdd]
          nlinarith
    | right i₂ =>
      induction j₁ using Fin.addCases with
      | left j₁ =>
        induction j₂ using Fin.addCases with
        | left j₂ => simp only [parityBlock_natAdd_castAdd]; nlinarith
        | right j₂ =>
          simp only [parityBlock_castAdd_castAdd, parityBlock_natAdd_castAdd,
            parityBlock_natAdd_natAdd, parityBlock_castAdd_natAdd]
          nlinarith [mul_nonneg (hA.nonneg i₁ j₁) (hA.nonneg i₂ j₂)]
      | right j₁ =>
        induction j₂ using Fin.addCases with
        | left j₂ => exact absurd hj (not_natAdd_lt_castAdd _ _)
        | right j₂ =>
          simp only [parityBlock_castAdd_natAdd, parityBlock_natAdd_natAdd]
          have hj' : j₁ < j₂ := (Fin.natAdd_lt_natAdd_iff _).mp hj
          rcases eq_or_ne i₂ 0 with rfl | hi₂
          · nlinarith
          · have := hA.minor_nonneg (Fin.pos_iff_ne_zero.mpr hi₂) hj'
            linarith
  | right i₁ =>
    induction i₂ using Fin.addCases with
    | left i₂ => exact absurd hi (not_natAdd_lt_castAdd _ _)
    | right i₂ =>
      have hi' : i₁ < i₂ := (Fin.natAdd_lt_natAdd_iff _).mp hi
      induction j₁ using Fin.addCases with
      | left j₁ =>
        induction j₂ using Fin.addCases with
        | left j₂ => simp only [parityBlock_natAdd_castAdd]; nlinarith
        | right j₂ =>
          simp only [parityBlock_natAdd_castAdd, parityBlock_natAdd_natAdd]
          nlinarith
      | right j₁ =>
        induction j₂ using Fin.addCases with
        | left j₂ => exact absurd hj (not_natAdd_lt_castAdd _ _)
        | right j₂ =>
          simp only [parityBlock_natAdd_natAdd]
          exact hA.minor_nonneg hi' ((Fin.natAdd_lt_natAdd_iff _).mp hj)

end Properties

/-! ### The determinant polynomial -/

private lemma castAdd_eq_natAdd_iff (i j : Fin (n + 1)) :
    Fin.castAdd (n + 1) i = Fin.natAdd (n + 1) j ↔ False := by
  simp only [iff_false]
  exact (castAdd_lt_natAdd i j).ne

/-- The `2 q × 2 q` matrix `1 + X B` is block upper triangular with diagonal blocks `1 + X A`. -/
private lemma one_add_X_smul_parityBlock (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    (1 + (X : ℝ[X]) • (parityBlock A).map C) =
      Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks (1 + (X : ℝ[X]) • A.map C)
          (Matrix.of fun _ j => (X : ℝ[X]) * C (A 0 j)) 0 (1 + (X : ℝ[X]) • A.map C)) := by
  refine Matrix.ext fun i j => ?_
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
  induction i using Fin.addCases with
  | left i =>
    induction j using Fin.addCases with
    | left j =>
      simp only [finSumFinEquiv_symm_apply_castAdd, Matrix.fromBlocks_apply₁₁,
        Matrix.add_apply, Matrix.one_apply, Matrix.smul_apply, Matrix.map_apply,
        parityBlock_castAdd_castAdd, Fin.castAdd_inj, smul_eq_mul]
    | right j =>
      have := castAdd_eq_natAdd_iff i j
      simp only [finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd,
        Matrix.fromBlocks_apply₁₂, Matrix.add_apply, Matrix.one_apply, Matrix.smul_apply,
        Matrix.map_apply, parityBlock_castAdd_natAdd, this, ite_false, zero_add, smul_eq_mul,
        Matrix.of_apply]
  | right i =>
    induction j using Fin.addCases with
    | left j =>
      have := castAdd_eq_natAdd_iff j i
      simp only [finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd,
        Matrix.fromBlocks_apply₂₁, Matrix.add_apply, Matrix.one_apply, Matrix.smul_apply,
        Matrix.map_apply, parityBlock_natAdd_castAdd, eq_comm (a := Fin.natAdd (n + 1) i), this,
        ite_false, zero_add, smul_eq_mul, Matrix.zero_apply, map_zero, mul_zero]
    | right j =>
      simp only [finSumFinEquiv_symm_apply_natAdd, Matrix.fromBlocks_apply₂₂,
        Matrix.add_apply, Matrix.one_apply, Matrix.smul_apply, Matrix.map_apply,
        parityBlock_natAdd_natAdd, smul_eq_mul, Fin.natAdd_inj]

/-- **The determinant polynomial of the block matrix is a square**:
`det (I + X B) = det (I + X A) ^ 2`. -/
theorem hessenbergDet_parityBlock (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    hessenbergDet (n := n + 1 + n) (parityBlock A) = hessenbergDet A ^ 2 := by
  rw [hessenbergDet, one_add_X_smul_parityBlock, Matrix.det_reindex_self,
    Matrix.det_fromBlocks_zero₂₁, sq, hessenbergDet]

end RealRooted
