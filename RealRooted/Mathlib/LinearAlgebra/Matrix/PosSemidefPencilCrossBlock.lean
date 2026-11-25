/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# A quadratic pencil that requires a nonsymmetric cross block

The pencil with coefficients `diag(1,4)`, `!![0,5;5,0]`, `diag(4,1)` is a Gram
matrix at every real parameter, but has no LMI certificate with symmetric cross block.

Source: unpublished manuscript, `full-operator-block-common-input-reduction.md`,
formula (5j) and its kernel argument; RealRooted #1991.
-/

public section

namespace Matrix

/-- The regression pencil is positive semidefinite even for negative parameters. -/
theorem posSemidef_quadratic_pencil_cross_block (t : ℝ) :
    ((!![1, 0; 0, 4] : Matrix (Fin 2) (Fin 2) ℝ) +
      t • !![0, 5; 5, 0] + t ^ 2 • !![4, 0; 0, 1]).PosSemidef := by
  have heq :
      (!![1, 0; 0, 4] : Matrix (Fin 2) (Fin 2) ℝ) +
        t • !![0, 5; 5, 0] + t ^ 2 • !![4, 0; 0, 1] =
        (!![1, t; 2 * t, 2])ᵀ * !![1, t; 2 * t, 2] := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  rw [heq, ← conjTranspose_eq_transpose_of_trivial]
  exact posSemidef_conjTranspose_mul_self _

/-- Requiring the cross block in the exact LMI to be symmetric is false. At parameter one,
the kernel vector `(1,-1)` forces incompatible first and second block equations. -/
theorem not_exists_symmetric_cross_block_quadratic_pencil :
    ¬ ∃ S Z : Matrix (Fin 2) (Fin 2) ℝ, Sᵀ = S ∧ Z.PosSemidef ∧
      (fromBlocks !![1, 0; 0, 4] S Sᵀ !![4, 0; 0, 1]).PosSemidef ∧
      !![0, 5; 5, 0] = S + Sᵀ + Z := by
  rintro ⟨S, Z, hS, hZ, hB, heq⟩
  let v : Fin 2 → ℝ := ![1, -1]
  let w : Fin 2 ⊕ Fin 2 → ℝ := Sum.elim v v
  have hz := hZ.dotProduct_mulVec_nonneg v
  have hb := hB.dotProduct_mulVec_nonneg w
  simp only [star_trivial] at hz hb
  have hmiddle := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => v ⬝ᵥ M *ᵥ v) heq
  have hsum : w ⬝ᵥ (fromBlocks !![1, 0; 0, 4] S Sᵀ !![4, 0; 0, 1]) *ᵥ w +
      v ⬝ᵥ Z *ᵥ v = 0 := by
    rw [fromBlocks_mulVec, sumElim_dotProduct_sumElim]
    norm_num [w, v, dotProduct, mulVec, Fin.sum_univ_two, add_mulVec,
      dotProduct_add, Matrix.add_apply, Matrix.transpose_apply] at hmiddle ⊢
    linarith
  have hbzero : star w ⬝ᵥ
      (fromBlocks !![1, 0; 0, 4] S Sᵀ !![4, 0; 0, 1]) *ᵥ w = 0 := by
    simp only [star_trivial]
    linarith
  have hker := hB.dotProduct_mulVec_zero_iff.mp hbzero
  have hleft := congrFun hker (Sum.inl 0)
  have hright := congrFun hker (Sum.inr 0)
  have hsym : S 1 0 = S 0 1 := congrArg (fun M => M 0 1) hS
  norm_num [w, v, fromBlocks_mulVec, mulVec, dotProduct, Fin.sum_univ_two] at hleft hright
  linarith

end Matrix
