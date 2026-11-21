/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import RealRooted.IntervalDifferential.CenteredBasis
import RealRooted.IntervalDifferential.Degree
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic

/-!
# Coordinates in the centered zig-zag basis

Odd-grid evaluation gives a triangular matrix with positive diagonal. Hence
these polynomials form a basis of the polynomials of bounded degree. This is
the coefficient identification used for Cao--Fu, arXiv:2610.40496v1, Theorem 1.1.
-/

public section
noncomputable section
open Polynomial Finset
namespace RealRooted.IntervalDifferential

private abbrev coordinateMatrix (D : ℕ) : Matrix (Fin (D + 1)) (Fin (D + 1)) ℝ :=
  Matrix.of fun i j => (zigzagBasis j.val (D - j.val)).eval (2 * (i.val : ℝ) + 3)

private theorem coordinateMatrix_diagonal_pos (D : ℕ) (i : Fin (D + 1)) :
    0 < coordinateMatrix D i i := by
  dsimp [coordinateMatrix]
  rw [zigzagBasis, eval_mul, eval_prod, eval_prod]
  apply mul_pos
  · apply Finset.prod_pos
    intro k hk
    simp only [eval_sub, eval_X, eval_C]
    have hki := mem_range.mp hk
    have hcast : (k : ℝ) < i.val := by exact_mod_cast hki
    linarith
  · apply Finset.prod_pos
    intro k _
    simp only [eval_add, eval_X, eval_C]
    positivity

private theorem coordinateMatrix_isUnit (D : ℕ) : IsUnit (coordinateMatrix D) := by
  apply (coordinateMatrix D).isUnit_iff_isUnit_det.mpr
  apply isUnit_iff_ne_zero.mpr
  rw [Matrix.det_of_isLowerTriangular]
  · exact (Finset.prod_pos (fun i _ => coordinateMatrix_diagonal_pos D i)).ne'
  · intro i j hij
    apply zigzagBasis_eval_eq_zero_of_lt
    exact hij

/-- Every polynomial of degree at most `D` has coordinates in the centered basis. -/
theorem exists_centered_coordinates (D : ℕ) (Q : ℝ[X]) (hQ : Q.natDegree ≤ D) :
    ∃ g : Fin (D + 1) → ℝ,
      Q = ∑ i : Fin (D + 1), C (g i) * zigzagBasis i.val (D - i.val) := by
  obtain ⟨g, hg⟩ := Matrix.mulVec_surjective_iff_isUnit.mpr (coordinateMatrix_isUnit D)
    (fun i => Q.eval (2 * (i.val : ℝ) + 3))
  refine ⟨g, Polynomial.eq_of_natDegree_lt_card_of_eval_eq Q _
    (f := fun i : Fin (D + 1) => 2 * (i.val : ℝ) + 3) ?_ ?_ ?_⟩
  · intro i j h
    apply Fin.ext
    exact_mod_cast (show (i.val : ℝ) = j.val by linarith)
  · intro i
    have h := congrFun hg i
    simpa only [Matrix.mulVec, dotProduct, coordinateMatrix, Matrix.of_apply,
      eval_finsetSum, eval_mul, eval_C, mul_comm] using h.symm
  · have hs : (∑ i : Fin (D + 1), C (g i) * zigzagBasis i.val (D - i.val)).natDegree ≤ D := by
      apply natDegree_sum_le_of_forall_le
      intro i _
      exact (natDegree_C_mul_le _ _).trans (by
        rw [zigzagBasis_natDegree]
        exact le_of_eq (Nat.add_sub_of_le (by have := i.isLt; lia)))
    simpa only [Fintype.card_fin] using (max_le hQ hs).trans_lt (Nat.lt_succ_self D)

/-- The centered-basis coordinates are unique. -/
theorem centered_coordinates_eq (D : ℕ) (g h : Fin (D + 1) → ℝ)
    (heq : (∑ i : Fin (D + 1), C (g i) * zigzagBasis i.val (D - i.val)) =
      ∑ i : Fin (D + 1), C (h i) * zigzagBasis i.val (D - i.val)) : g = h := by
  apply Matrix.mulVec_injective_iff_isUnit.mpr (coordinateMatrix_isUnit D)
  funext i
  have hv := congrArg (Polynomial.eval (2 * (i.val : ℝ) + 3)) heq
  simpa only [Matrix.mulVec, dotProduct, coordinateMatrix, Matrix.of_apply,
    eval_finsetSum, eval_mul, eval_C, mul_comm] using hv

end RealRooted.IntervalDifferential
