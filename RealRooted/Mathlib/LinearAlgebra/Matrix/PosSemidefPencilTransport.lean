/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic

/-!
# Division-free transport of quadratic Gram certificates

Nonnegative scalar boards act on the three coefficients of a quadratic pencil by
homogenization. The rational cross-block witness transports by block congruence plus a
positive block diagonal correction. No determinant or denominator is inverted, so zero
boards, zero rows and rank-one boards are included.

Source: unpublished manuscript, `full-operator-block-common-input-reduction.md`,
“Projective transport through a nonnegative board”, formulas (5l)–(5o); RealRooted #1991.
This is the base transport, not the sharpened functorial transport from (5q).
-/

public section

namespace Matrix

/-- The coefficient action of a scalar board is precisely homogeneous substitution.
This identity is valid even when the denominator of the projective substitution vanishes. -/
theorem quadratic_pencil_transform_eq {ι : Type*}
    (H₀ H₁ H₂ : Matrix ι ι ℝ) (a b c d t : ℝ) :
    (d ^ 2 • H₀ + (b * d) • H₁ + b ^ 2 • H₂) +
      t • ((2 * c * d) • H₀ + (a * d + b * c) • H₁ + (2 * a * b) • H₂) +
      t ^ 2 • (c ^ 2 • H₀ + (a * c) • H₁ + a ^ 2 • H₂) =
      (d + c * t) ^ 2 • H₀ + ((d + c * t) * (b + a * t)) • H₁ +
        (b + a * t) ^ 2 • H₂ := by
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

/-- The transported cross block satisfies the linear coefficient identity. -/
theorem quadratic_pencil_transform_linear_eq {ι : Type*}
    (H₀ H₂ S Z : Matrix ι ι ℝ) (h₀ : H₀ᵀ = H₀) (h₂ : H₂ᵀ = H₂)
    (a b c d : ℝ) :
    (2 * c * d) • H₀ + (a * d + b * c) • (S + Sᵀ + Z) + (2 * a * b) • H₂ =
      ((c * d) • H₀ + (a * d) • S + (b * c) • Sᵀ + (a * b) • H₂) +
      ((c * d) • H₀ + (a * d) • S + (b * c) • Sᵀ + (a * b) • H₂)ᵀ +
      (a * d + b * c) • Z := by
  simp only [transpose_add, transpose_smul, transpose_transpose, h₀, h₂]
  module

/-- The block-congruence identity for the rational transported witness. -/
theorem fromBlocks_quadratic_transform_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H₀ H₂ S Z : Matrix ι ι ℝ) (h₀ : H₀ᵀ = H₀) (h₂ : H₂ᵀ = H₂)
    (a b c d : ℝ) :
    fromBlocks
      (d ^ 2 • H₀ + (b * d) • (S + Sᵀ + Z) + b ^ 2 • H₂)
      ((c * d) • H₀ + (a * d) • S + (b * c) • Sᵀ + (a * b) • H₂)
      (((c * d) • H₀ + (a * d) • S + (b * c) • Sᵀ + (a * b) • H₂)ᵀ)
      (c ^ 2 • H₀ + (a * c) • (S + Sᵀ + Z) + a ^ 2 • H₂) =
      (fromBlocks (d • 1) (c • 1) (b • 1) (a • 1))ᵀ *
        fromBlocks H₀ S Sᵀ H₂ * fromBlocks (d • 1) (c • 1) (b • 1) (a • 1) +
        fromBlocks ((b * d) • Z) 0 0 ((a * c) • Z) := by
  rw [fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply, ← fromBlocks_add]
  simp only [transpose_smul, transpose_one, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.one_mul, Matrix.mul_one, smul_add, smul_smul,
    transpose_add, transpose_transpose, h₀, h₂]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp only [fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁,
      fromBlocks_apply₂₂, Matrix.add_apply, Matrix.smul_apply, Matrix.zero_apply, smul_eq_mul] <;>
    ring

/-- A block diagonal sum of positive-semidefinite matrices is positive semidefinite. -/
private theorem posSemidef_fromBlocks_zero {ι : Type*} [Finite ι]
    {A B : Matrix ι ι ℝ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    (fromBlocks A 0 0 B).PosSemidef := by
  have := Fintype.ofFinite ι
  refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ (fun x => ?_)
  · rw [IsHermitian, fromBlocks_conjTranspose]
    simp only [hA.isHermitian.eq, hB.isHermitian.eq, conjTranspose_zero]
  · have ha := hA.dotProduct_mulVec_nonneg (x ∘ Sum.inl)
    have hb := hB.dotProduct_mulVec_nonneg (x ∘ Sum.inr)
    simp only [star_trivial] at ha hb ⊢
    rw [fromBlocks_mulVec, ← Sum.elim_comp_inl_inr x, sumElim_dotProduct_sumElim]
    simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, zero_mulVec, add_zero, zero_add]
    exact add_nonneg ha hb

/-- A nonnegative board transports an actual LMI witness by the rational formulas (5n).
No nonsingularity or positive-dimension hypothesis is needed. -/
theorem posSemidef_quadratic_pencil_transport {ι : Type*} [Finite ι]
    {H₀ H₁ H₂ S Z : Matrix ι ι ℝ}
    (hZ : Z.PosSemidef) (hB : (fromBlocks H₀ S Sᵀ H₂).PosSemidef)
    (h₁ : H₁ = S + Sᵀ + Z)
    {a b c d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    ((a * d + b * c) • Z).PosSemidef ∧
      (fromBlocks
        (d ^ 2 • H₀ + (b * d) • H₁ + b ^ 2 • H₂)
        ((c * d) • H₀ + (a * d) • S + (b * c) • Sᵀ + (a * b) • H₂)
        (((c * d) • H₀ + (a * d) • S + (b * c) • Sᵀ + (a * b) • H₂)ᵀ)
        (c ^ 2 • H₀ + (a * c) • H₁ + a ^ 2 • H₂)).PosSemidef ∧
      (2 * c * d) • H₀ + (a * d + b * c) • H₁ + (2 * a * b) • H₂ =
        ((c * d) • H₀ + (a * d) • S + (b * c) • Sᵀ + (a * b) • H₂) +
        ((c * d) • H₀ + (a * d) • S + (b * c) • Sᵀ + (a * b) • H₂)ᵀ +
        (a * d + b * c) • Z := by
  have := Fintype.ofFinite ι
  classical
  have hsym : (fromBlocks H₀ S Sᵀ H₂)ᵀ = fromBlocks H₀ S Sᵀ H₂ := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using hB.isHermitian.eq
  have h₀ : H₀ᵀ = H₀ := by
    ext i j
    exact congrArg (fun M => M (Sum.inl i) (Sum.inl j)) hsym
  have h₂ : H₂ᵀ = H₂ := by
    ext i j
    exact congrArg (fun M => M (Sum.inr i) (Sum.inr j)) hsym
  refine ⟨hZ.smul (add_nonneg (mul_nonneg ha hd) (mul_nonneg hb hc)), ?_, ?_⟩
  · rw [h₁, fromBlocks_quadratic_transform_eq H₀ H₂ S Z h₀ h₂]
    have hcong := hB.conjTranspose_mul_mul_same
      (fromBlocks (d • 1) (c • 1) (b • 1) (a • 1) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ)
    rw [conjTranspose_eq_transpose_of_trivial] at hcong
    exact hcong.add (posSemidef_fromBlocks_zero
      (hZ.smul (mul_nonneg hb hd)) (hZ.smul (mul_nonneg ha hc)))
  · rw [h₁]
    exact quadratic_pencil_transform_linear_eq H₀ H₂ S Z h₀ h₂ a b c d

end Matrix
