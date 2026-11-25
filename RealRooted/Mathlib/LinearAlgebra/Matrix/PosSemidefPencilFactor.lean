/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.LinearAlgebra.Matrix.PosDef
import RealRooted.Mathlib.LinearAlgebra.Matrix.PosSemidefPencil
import Mathlib.Analysis.Matrix.Order

/-!
# Gram factors of quadratic positive-semidefinite pencils

A quadratic real symmetric matrix pencil is positive semidefinite on the nonnegative
half-line exactly when it is `(U + t • V)ᵀ * (U + t • V) + t • (Wᵀ * W)`.
The first two factors have row type `Fin n ⊕ Fin n`; the remainder has row type `Fin n`.
No invertibility or positive-dimension assumption is needed.

Source: unpublished manuscript, `full-operator-block-common-input-reduction.md`,
“Quadratic Bezout certificate on one input ray”, formulas (5f)–(5g); RealRooted #1991.
The finite LMI equivalence is already proved in `PosSemidefPencil`.
-/

public section

namespace Matrix

/-- Every real positive-semidefinite matrix has a square Gram factor, including singular
matrices and matrices indexed by an empty type. -/
theorem PosSemidef.exists_transpose_mul_self {ι : Type*} [Fintype ι]
    {H : Matrix ι ι ℝ} (hH : H.PosSemidef) :
    ∃ B : Matrix ι ι ℝ, Bᵀ * B = H := by
  classical
  open scoped MatrixOrder in
    refine ⟨CFC.sqrt H, ?_⟩
    rw [← conjTranspose_eq_transpose_of_trivial,
      (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg H)).isHermitian.eq]
    exact CFC.sqrt_mul_sqrt_self H hH.nonneg

/-- Split a block Gram factor into its two sets of columns. The cross block is arbitrary;
it need not be symmetric. -/
theorem PosSemidef.exists_gram_fromBlocks {ι : Type*} [Fintype ι]
    {H₀ S H₂ : Matrix ι ι ℝ} (hH : (fromBlocks H₀ S Sᵀ H₂).PosSemidef) :
    ∃ U V : Matrix (ι ⊕ ι) ι ℝ,
      Uᵀ * U = H₀ ∧ Uᵀ * V = S ∧ Vᵀ * V = H₂ := by
  obtain ⟨B, hB⟩ := hH.exists_transpose_mul_self
  refine ⟨B.submatrix id Sum.inl, B.submatrix id Sum.inr, ?_, ?_, ?_⟩
  · ext i j
    exact congrArg (fun M => M (Sum.inl i) (Sum.inl j)) hB
  · ext i j
    exact congrArg (fun M => M (Sum.inl i) (Sum.inr j)) hB
  · ext i j
    exact congrArg (fun M => M (Sum.inr i) (Sum.inr j)) hB

/-- Expanding a rectangular affine Gram factor gives a quadratic matrix pencil. -/
theorem affine_gram_eq_quadratic {ι κ : Type*} [Fintype κ]
    (U V : Matrix κ ι ℝ) (t : ℝ) :
    (U + t • V)ᵀ * (U + t • V) =
      Uᵀ * U + t • (Uᵀ * V + Vᵀ * U) + t ^ 2 • (Vᵀ * V) := by
  rw [transpose_add, transpose_smul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, pow_two]
  module

/-- The exact rectangular factor form for a quadratic pencil on the nonnegative half-line.
The row dimensions are fixed, so this also covers singular endpoints and `n = 0`. -/
theorem posSemidef_quadratic_pencil_iff_exists_gram {n : ℕ}
    (H₀ H₁ H₂ : Matrix (Fin n) (Fin n) ℝ)
    (h₀ : H₀.IsHermitian) (h₁ : H₁.IsHermitian) (h₂ : H₂.IsHermitian) :
    (∀ t : ℝ, 0 ≤ t → (H₀ + t • H₁ + t ^ 2 • H₂).PosSemidef) ↔
      ∃ U V : Matrix (Fin n ⊕ Fin n) (Fin n) ℝ,
      ∃ W : Matrix (Fin n) (Fin n) ℝ, ∀ t : ℝ,
        H₀ + t • H₁ + t ^ 2 • H₂ =
          (U + t • V)ᵀ * (U + t • V) + t • (Wᵀ * W) := by
  constructor
  · intro h
    obtain ⟨S, Z, hZ, hB, h₁eq⟩ :=
      (posSemidef_quadratic_pencil_iff H₀ H₁ H₂ h₀ h₁ h₂).mp h
    obtain ⟨U, V, hU, hUV, hV⟩ := hB.exists_gram_fromBlocks
    obtain ⟨W, hW⟩ := hZ.exists_transpose_mul_self
    refine ⟨U, V, W, fun t => ?_⟩
    have hVU : Vᵀ * U = Sᵀ := by rw [← hUV, transpose_mul, transpose_transpose]
    rw [affine_gram_eq_quadratic, hU, hUV, hVU, hV, hW, h₁eq]
    module
  · rintro ⟨U, V, W, h⟩ t ht
    rw [h t]
    have hUV : ((U + t • V)ᵀ * (U + t • V)).PosSemidef := by
      simpa only [conjTranspose_eq_transpose_of_trivial] using
        posSemidef_conjTranspose_mul_self (U + t • V)
    have hW : (Wᵀ * W).PosSemidef := by
      simpa only [conjTranspose_eq_transpose_of_trivial] using
        posSemidef_conjTranspose_mul_self W
    exact hUV.add (hW.smul ht)

end Matrix
