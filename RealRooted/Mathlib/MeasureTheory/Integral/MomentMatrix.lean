/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic.Ring

/-!
# Positive semidefinite moment matrices

The quadratic form of a shifted Hankel moment matrix is the integral of a
square times a nonnegative power. This supplies the matrix form of the moment
inequalities used in the unpublished manuscript behind RealRooted issues
#2181 and #2185. No moment representation is assumed to exist by this file.
-/

public section

open Finset Matrix

namespace MeasureTheory

/-- Every shifted Hankel matrix of an integrable moment sequence on the
nonnegative half-line is positive semidefinite. -/
theorem posSemidef_integral_pow_add
    {μ : Measure ℝ} (hint : ∀ k : ℕ, Integrable (fun x : ℝ => x ^ k) μ)
    (hpos : ∀ᵐ x ∂μ, 0 ≤ x) (n r : ℕ) :
    Matrix.PosSemidef (fun i j : Fin n =>
      ∫ x : ℝ, x ^ (i.val + j.val + r) ∂μ) := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · apply Matrix.IsHermitian.ext
    intro i j
    change star (∫ x : ℝ, x ^ (j.val + i.val + r) ∂μ) =
      ∫ x : ℝ, x ^ (i.val + j.val + r) ∂μ
    simp [Nat.add_comm]
  · intro v
    have hsum :
        (star v ⬝ᵥ ((fun i j : Fin n =>
          ∫ x : ℝ, x ^ (i.val + j.val + r) ∂μ) *ᵥ v)) =
          ∫ x : ℝ, x ^ r * (∑ i : Fin n, v i * x ^ i.val) ^ 2 ∂μ := by
      have hij (i j : Fin n) :
          Integrable (fun x : ℝ => v i * (x ^ (i.val + j.val + r) * v j)) μ :=
        ((hint _).mul_const _).const_mul _
      calc
        _ = ∑ i : Fin n, ∑ j : Fin n,
            ∫ x : ℝ, v i * (x ^ (i.val + j.val + r) * v j) ∂μ := by
          simp only [dotProduct, mulVec, Pi.star_apply, star_trivial, mul_sum,
            integral_const_mul, integral_mul_const]
        _ = ∫ x : ℝ, ∑ i : Fin n, ∑ j : Fin n,
            v i * (x ^ (i.val + j.val + r) * v j) ∂μ := by
          rw [integral_finsetSum _
            (fun i _ => integrable_finsetSum _ (fun j _ => hij i j))]
          apply sum_congr rfl
          intro i hi
          exact (integral_finsetSum _ (fun j _ => hij i j)).symm
        _ = _ := by
          congr 1
          funext x
          simp only [pow_two, mul_sum, sum_mul, pow_add]
          apply sum_congr rfl
          intro i hi
          apply sum_congr rfl
          intro j hj
          ring
    rw [hsum]
    apply integral_nonneg_of_ae
    filter_upwards [hpos] with x hx
    exact mul_nonneg (pow_nonneg hx r) (sq_nonneg _)

end MeasureTheory
