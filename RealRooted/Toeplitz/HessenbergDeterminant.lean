module

import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# The determinant of a rank-one perturbation of a unipotent lower-triangular pencil

Over a commutative ring, let `L` be a matrix with `L i j = 0` for `i ≤ j` and let
`A' i j = c j + L i j`, that is `A' = 𝟙 cᵀ + L`. Then for every scalar `w`
`det (1 + w A') = 1 + w * cᵀ (1 + w L)⁻¹ 𝟙`.
This is the matrix determinant lemma for the unipotent matrix `1 + w L`.
-/

public section

open Matrix

namespace RealRooted

variable {R : Type*} [CommRing R] {n : ℕ}

/-- A matrix `1 + w L` with `L` having zero upper triangle and diagonal has determinant `1`. -/
lemma det_one_add_smul_of_lower (w : R) (L : Matrix (Fin n) (Fin n) R)
    (hL : ∀ i j, i ≤ j → L i j = 0) : (1 + w • L).det = 1 := by
  rw [Matrix.det_of_isLowerTriangular]
  · simp [hL _ _ le_rfl]
  · intro i j hij
    have hij' : i < j := OrderDual.toDual_lt_toDual.mp hij
    simp [Matrix.one_apply_ne hij'.ne, hL i j hij'.le]

/-- **Matrix determinant lemma** for `1 + w (𝟙 cᵀ + L)` with `L` strictly lower triangular. -/
theorem det_one_add_smul_eq_of_lower (w : R) (c : Fin n → R) (L A' : Matrix (Fin n) (Fin n) R)
    (hL : ∀ i j, i ≤ j → L i j = 0) (hA' : ∀ i j, A' i j = c j + L i j) :
    (1 + w • A').det = 1 + w * (c ⬝ᵥ ((1 + w • L)⁻¹ *ᵥ fun _ => 1)) := by
  have hB := det_one_add_smul_of_lower w L hL
  have hsum : 1 + w • A' =
      (1 + w • L) + Matrix.replicateCol Unit (fun _ => w) * Matrix.replicateRow Unit c := by
    ext i j
    simp [hA', mul_add, Matrix.mul_apply]
    ring
  rw [hsum, Matrix.det_add_replicateCol_mul_replicateRow (by simp [hB]), hB, one_mul,
    Matrix.det_unique]
  simp only [PUnit.default_eq_unit, Matrix.add_apply, one_apply_eq, Matrix.mul_apply,
    replicateRow_apply, replicateCol_apply, dotProduct, mulVec, mul_one, Finset.mul_sum,
    add_right_inj]
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [mul_comm]

end RealRooted
