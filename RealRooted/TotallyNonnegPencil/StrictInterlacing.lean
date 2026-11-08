/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import RealRooted.Basic.ProperPosition
public import RealRooted.Mathlib.LinearAlgebra.Matrix.Checkerboard
public import RealRooted.Mathlib.LinearAlgebra.Matrix.TotallyNonneg
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import RealRooted.OscillatoryInterlacing
import RealRooted.Mathlib.LinearAlgebra.Matrix.CheckerboardAdjacent
import RealRooted.Mathlib.LinearAlgebra.Matrix.TotallyNonneg.Mul
import Mathlib.Tactic

/-! # Strict principal interlacing of checkerboard inverse products -/

public section

namespace Matrix

/-- The classical oscillatory endpoint applies to a checkerboard inverse
product under the elementary adjacent-entry conditions above. -/
theorem IsLowerTriangular.checkerboard_inv_mul_leading_charpoly_strictInterlaces
    {n : ℕ} {L M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hLtri : L.IsLowerTriangular) (hL : L.IsTotallyNonneg)
    (hdet : 0 < L.det) (hM : M.IsTotallyNonneg) (hMdet : M.det ≠ 0)
    (hsuper : ∀ i : Fin n, 0 < M i.castSucc i.succ)
    (hsub : ∀ i : Fin n, 0 < M i.succ i.castSucc ∨
      (0 < L i.succ i.castSucc ∧ 0 < M i.castSucc i.castSucc)) :
    let H := (checkerboard L)⁻¹ * M
    RealRooted.Interlaces
        (H.submatrix Fin.castSucc Fin.castSucc).charpoly H.charpoly ∧
      (∀ x : ℝ, H.charpoly.IsRoot x → H.charpoly.rootMultiplicity x = 1) ∧
      (∀ x : ℝ, (H.submatrix Fin.castSucc Fin.castSucc).charpoly.IsRoot x →
        (H.submatrix Fin.castSucc Fin.castSucc).charpoly.rootMultiplicity x = 1) ∧
      (∀ x : ℝ, ¬(H.charpoly.IsRoot x ∧
        (H.submatrix Fin.castSucc Fin.castSucc).charpoly.IsRoot x)) ∧
      ∀ x ∈ H.charpoly.roots, 0 < x := by
  have hRTN := hL.checkerboard_nonsing_inv hdet
  have hRdet := det_checkerboard_nonsing_inv_ne_zero L hdet.ne'.isUnit
  have hHdet : ((checkerboard L)⁻¹ * M).det ≠ 0 := by
    rw [Matrix.det_mul]
    exact mul_ne_zero hRdet hMdet
  obtain ⟨hHsuper, hHsub⟩ :=
    hLtri.checkerboard_inv_mul_adjacent_pos hL hdet hM hsuper hsub
  exact (hRTN.mul hM).leading_charpoly_strictInterlaces hHdet hHsuper hHsub

end Matrix
