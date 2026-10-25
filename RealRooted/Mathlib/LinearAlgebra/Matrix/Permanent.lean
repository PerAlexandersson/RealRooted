/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.LinearAlgebra.Matrix.Permanent

/-!
# Laplace expansion of the permanent

This file supplies the permanent analogue of the first-column Laplace
expansion for determinants.
-/

@[expose] public section

open scoped BigOperators

namespace Matrix

/-- Expand the permanent of an `(n+1) × (n+1)` matrix along its first
column. -/
theorem permanent_succ_column_zero {n : ℕ} {R : Type*}
    [CommSemiring R] (M : Matrix (Fin (n + 1)) (Fin (n + 1)) R) :
    permanent M =
      ∑ i : Fin (n + 1),
        M i 0 * permanent (M.submatrix i.succAbove Fin.succ) := by
  classical
  rw [permanent, Finset.univ_perm_fin_succ,
    ← Finset.univ_product_univ]
  simp only [Finset.sum_map, Equiv.toEmbedding_apply,
    Finset.sum_product, Matrix.submatrix]
  apply Finset.sum_congr rfl
  intro i hi
  refine Fin.cases ?_ (fun i => ?_) i
  · simp only [Fin.prod_univ_succ, permanent, Finset.mul_sum,
      Equiv.Perm.decomposeFin_symm_apply_zero,
      Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_self,
      Fin.succAbove_zero]
    rfl
  · change
      (∑ σ : Equiv.Perm (Fin n),
        ∏ j, M (Equiv.Perm.decomposeFin.symm (i.succ, σ) j) j) =
        M i.succ 0 * permanent
          (fun r c => M (i.succ.succAbove r) c.succ)
    rw [← permanent_permute_cols (Fin.cycleRange i)
        (fun r c => M (i.succ.succAbove r) c.succ),
      permanent, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro σ hσ
    rw [Fin.prod_univ_succ]
    simp only [Equiv.Perm.decomposeFin_symm_apply_zero,
      Equiv.Perm.decomposeFin_symm_apply_succ,
      Fin.succAbove_cycleRange, Matrix.submatrix]
    rfl

/-- Expand the permanent of an `(n+1) × (n+1)` matrix along its first
row. -/
theorem permanent_succ_row_zero {n : ℕ} {R : Type*}
    [CommSemiring R] (M : Matrix (Fin (n + 1)) (Fin (n + 1)) R) :
    permanent M =
      ∑ j : Fin (n + 1),
        M 0 j * permanent (M.submatrix Fin.succ j.succAbove) := by
  rw [← permanent_transpose M, permanent_succ_column_zero]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← permanent_transpose]
  rfl

end Matrix
