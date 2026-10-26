/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Positivity

/-!
# An eigenvalue bound from weighted column sums

The finite weighted triangle-inequality argument applies over any normed field.
It is the finite-dimensional step in a polynomial root-disk argument.
-/

public section

namespace Matrix

/-- Strict positive weighted column bounds bound the norm of any scalar admitting
an explicit nonzero eigenvector. -/
theorem norm_lt_of_weighted_column_sum_lt
    {K ι : Type*} [NormedField K] [Fintype ι]
    (A : Matrix ι ι K) (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (r : ℝ) (hcol : ∀ j, ∑ i, w i * ‖A i j‖ < r * w j)
    (μ : K) (v : ι → K) (hv : ∃ j, v j ≠ 0)
    (heig : ∀ i, μ * v i = ∑ j, A i j * v j) : ‖μ‖ < r := by
  classical
  let V : ℝ := ∑ j, w j * ‖v j‖
  obtain ⟨j₀, hj₀⟩ := hv
  have hV : 0 < V := by
    apply Finset.sum_pos'
    · intro i _
      exact mul_nonneg (hw i).le (norm_nonneg _)
    · exact ⟨j₀, Finset.mem_univ _, mul_pos (hw _) (norm_pos_iff.mpr hj₀)⟩
  have hrow (i : ι) :
      ‖μ‖ * (w i * ‖v i‖) ≤ ∑ j, w i * ‖A i j‖ * ‖v j‖ := by
    calc
      ‖μ‖ * (w i * ‖v i‖) = w i * ‖μ * v i‖ := by rw [norm_mul]; ring
      _ = w i * ‖∑ j, A i j * v j‖ := by rw [heig]
      _ ≤ w i * ∑ j, ‖A i j * v j‖ :=
        mul_le_mul_of_nonneg_left (norm_sum_le _ _) (hw i).le
      _ = ∑ j, w i * ‖A i j‖ * ‖v j‖ := by
        simp only [Finset.mul_sum, norm_mul, mul_assoc]
  have hbound : ‖μ‖ * V < r * V := by
    calc
      ‖μ‖ * V ≤ ∑ i, ∑ j, w i * ‖A i j‖ * ‖v j‖ := by
        change ‖μ‖ * (∑ j, w j * ‖v j‖) ≤ _
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum fun i _ => hrow i
      _ = ∑ j, (∑ i, w i * ‖A i j‖) * ‖v j‖ := by
        rw [Finset.sum_comm]
        simp only [Finset.sum_mul]
      _ < ∑ j, (r * w j) * ‖v j‖ := by
        apply Finset.sum_lt_sum
        · intro j _
          exact mul_le_mul_of_nonneg_right (hcol j).le (norm_nonneg _)
        · exact ⟨j₀, Finset.mem_univ _,
            mul_lt_mul_of_pos_right (hcol j₀) (norm_pos_iff.mpr hj₀)⟩
      _ = r * V := by simp only [V, Finset.mul_sum, mul_assoc]
  exact (mul_lt_mul_iff_left₀ hV).mp hbound

end Matrix
