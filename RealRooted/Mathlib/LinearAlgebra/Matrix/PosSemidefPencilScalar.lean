/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Algebra.Order.Star.Real
import RealRooted.Mathlib.LinearAlgebra.Matrix.PosSemidefPencil
import RealRooted.Mathlib.Algebra.QuadraticDiscriminant

/-!
# Scalar recovery from the quadratic matrix certificate

The one-dimensional LMI recovers the square-root-free condition
`0 ≤ α ∧ 0 ≤ γ ∧ (0 ≤ β ∨ β² ≤ 4αγ)`, including zero endpoints.

Source: unpublished manuscript, `full-operator-block-common-input-reduction.md`,
formulas (5e)–(5f); RealRooted #1991. The scalar bound uses Mathlib’s quadratic
discriminant criterion.
-/

public section

namespace Matrix

/-- A scalar quadratic on the nonnegative half-line has the expected exact criterion,
obtained from the finite Gram LMI in the forward direction. Zero endpoints are allowed. -/
theorem posSemidef_quadratic_pencil_fin_one_iff (α β γ : ℝ) :
    (∀ t : ℝ, 0 ≤ t →
      ((Matrix.of fun _ _ : Fin 1 => γ) + t • (Matrix.of fun _ _ => β) +
        t ^ 2 • (Matrix.of fun _ _ => α)).PosSemidef) ↔
      0 ≤ α ∧ 0 ≤ γ ∧ (0 ≤ β ∨ β ^ 2 ≤ 4 * α * γ) := by
  constructor
  · intro h
    have herm (r : ℝ) : (Matrix.of fun _ _ : Fin 1 => r).IsHermitian :=
      by ext i j; rfl
    obtain ⟨S, Z, hZ, hB, heq⟩ :=
      (posSemidef_quadratic_pencil_iff _ _ _ (herm γ) (herm β) (herm α)).mp h
    have hα : 0 ≤ α := hB.diag_nonneg (i := Sum.inr 0)
    have hγ : 0 ≤ γ := hB.diag_nonneg (i := Sum.inl 0)
    have hz : 0 ≤ Z 0 0 := hZ.diag_nonneg
    have hb : β = S 0 0 + S 0 0 + Z 0 0 := congrArg (fun M => M 0 0) heq
    have hquad (x : ℝ) : 0 ≤ γ * (x * x) + (2 * S 0 0) * x + α := by
      have hx := hB.dotProduct_mulVec_nonneg
        (Sum.elim (fun _ : Fin 1 => x) (fun _ : Fin 1 => 1))
      simp only [star_trivial] at hx
      rw [fromBlocks_mulVec, sumElim_dotProduct_sumElim] at hx
      norm_num [dotProduct, mulVec, Fin.sum_univ_one] at hx
      nlinarith [hx]
    have hs' : S 0 0 ^ 2 ≤ γ * α := by
      have hd := discrim_le_zero hquad
      rw [discrim] at hd
      nlinarith
    refine ⟨hα, hγ, ?_⟩
    by_cases hβ : 0 ≤ β
    · exact Or.inl hβ
    · right
      have hβ' : β < 0 := lt_of_not_ge hβ
      have hsneg : S 0 0 ≤ 0 := by linarith
      nlinarith [mul_nonneg hz (neg_nonneg.mpr hsneg), sq_nonneg (Z 0 0)]
  · rintro ⟨hα, hγ, hβ⟩ t ht
    have hq : 0 ≤ γ + t * β + t ^ 2 * α := by
      rcases hβ with hβ | hβ
      · positivity
      · have hdisc : discrim α β γ ≤ 0 := by rw [discrim]; linarith
        have hq := Quadratic.nonneg_of_nonneg_of_discrim_nonpos hα hγ hdisc t
        nlinarith [hq]
    refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ (fun x => ?_)
    · ext i j
      rfl
    · simp only [star_trivial]
      simp only [dotProduct, mulVec, Fin.sum_univ_one, Matrix.add_apply, Matrix.smul_apply,
        Matrix.of_apply, smul_eq_mul]
      nlinarith [mul_nonneg hq (sq_nonneg (x 0))]

/-- In dimension one the existential Gram LMI is exactly the scalar quadratic criterion. -/
theorem exists_posSemidef_fromBlocks_fin_one_iff (α β γ : ℝ) :
    (∃ S Z : Matrix (Fin 1) (Fin 1) ℝ, Z.PosSemidef ∧
      (fromBlocks (Matrix.of fun _ _ => γ) S Sᵀ (Matrix.of fun _ _ => α)).PosSemidef ∧
      (Matrix.of fun _ _ => β) = S + Sᵀ + Z) ↔
      0 ≤ α ∧ 0 ≤ γ ∧ (0 ≤ β ∨ β ^ 2 ≤ 4 * α * γ) := by
  have herm (r : ℝ) : (Matrix.of fun _ _ : Fin 1 => r).IsHermitian :=
    by ext i j; rfl
  rw [← posSemidef_quadratic_pencil_iff _ _ _ (herm γ) (herm β) (herm α)]
  exact posSemidef_quadratic_pencil_fin_one_iff α β γ

end Matrix
