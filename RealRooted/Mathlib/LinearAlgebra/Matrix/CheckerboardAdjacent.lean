/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import RealRooted.Mathlib.LinearAlgebra.Matrix.Checkerboard
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.Basic.Real.Basic
public import RealRooted.Mathlib.LinearAlgebra.Matrix.TotallyNonneg
import RealRooted.Mathlib.LinearAlgebra.Matrix.JacobiComplementaryMinor
import RealRooted.Mathlib.LinearAlgebra.Matrix.OscillatoryInterlacing.Core
import Mathlib.Tactic

/-! # Positive adjacent entries of checkerboard inverse products -/

public section

namespace Matrix

/-- Only two summands contribute immediately below the diagonal in a product
of lower triangular matrices. -/
theorem IsLowerTriangular.mul_apply_succ_castSucc
    {R : Type*} [NonUnitalNonAssocSemiring R] {n : ℕ}
    {A B : Matrix (Fin (n + 1)) (Fin (n + 1)) R}
    (hA : A.IsLowerTriangular) (hB : B.IsLowerTriangular) (i : Fin n) :
    (A * B) i.succ i.castSucc =
      A i.succ i.castSucc * B i.castSucc i.castSucc +
        A i.succ i.succ * B i.succ i.castSucc := by
  rw [Matrix.mul_apply, Fintype.sum_eq_add i.castSucc i.succ i.castSucc_lt_succ.ne]
  intro k hk
  change A i.succ k * B k i.castSucc = 0
  by_cases hki : k < i.castSucc
  · exact (congrArg (fun x : R => A i.succ k * x) (hB hki)).trans (mul_zero _)
  · have hik : i.succ < k := by
      have hk₀ := hk.1
      have hk₁ := hk.2
      have hk₀ : k.val ≠ i.val := fun h => hk₀ (Fin.ext h)
      have hk₁ : k.val ≠ i.val + 1 := fun h => hk₁ (Fin.ext h)
      simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_succ] at hki ⊢
      lia
    exact (congrArg (fun x : R => x * B k i.castSucc) (hA hik)).trans (zero_mul _)

/-- Checkerboard signs fix diagonal entries. -/
@[simp] theorem checkerboard_apply_diag {R : Type*} [CommRing R] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) R) (i : Fin n) : checkerboard A i i = A i i := by
  simp [checkerboard, ← mul_assoc, ← mul_pow]

/-- Checkerboard signs negate the first subdiagonal. -/
@[simp] theorem checkerboard_apply_succ_castSucc {R : Type*} [CommRing R] {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (i : Fin n) :
    checkerboard A i.succ i.castSucc = -A i.succ i.castSucc := by
  simp only [checkerboard, Fin.val_succ, Fin.val_castSucc, pow_succ]
  have hi : ((-1 : R) ^ i.val) * ((-1 : R) ^ i.val) = 1 := by
    rw [← mul_pow]
    simp
  calc
    _ = -((((-1 : R) ^ i.val) * ((-1 : R) ^ i.val)) * A i.succ i.castSucc) := by
      ring
    _ = _ := by rw [hi, one_mul]

/-- A positive summand in a product of nonnegative matrices gives a positive
entry of the product. -/
theorem mul_apply_pos_of_pos_summand
    {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ i j, 0 ≤ A i j) (hB : ∀ i j, 0 ≤ B i j)
    (i j k : Fin n) (hAk : 0 < A i k) (hBk : 0 < B k j) :
    0 < (A * B) i j := by
  apply lt_of_lt_of_le (mul_pos hAk hBk)
  exact Finset.single_le_sum (fun t _ => mul_nonneg (hA i t) (hB t j))
    (Finset.mem_univ k)

/-- A TN lower triangular matrix with positive determinant has a
checkerboard inverse with positive adjacent subdiagonal wherever its own
adjacent subdiagonal is positive. -/
theorem IsLowerTriangular.checkerboard_inv_subdiag_pos
    {n : ℕ} {L : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hLtri : L.IsLowerTriangular) (hL : L.IsTotallyNonneg)
    (hdet : 0 < L.det) (i : Fin n) (hsub : 0 < L i.succ i.castSucc) :
    0 < (checkerboard L)⁻¹ i.succ i.castSucc := by
  have hunit : IsUnit L.det := isUnit_iff_ne_zero.mpr hdet.ne'
  have hLI : L * L⁻¹ = 1 := L.mul_nonsing_inv hunit
  have hAI : checkerboard L * checkerboard L⁻¹ = 1 := by
    rw [← checkerboard_mul, hLI, checkerboard_one]
  have hAunit : IsUnit (checkerboard L).det := isUnit_det_of_right_inverse hAI
  have hAtri : (checkerboard L).IsLowerTriangular := by
    intro a b hab
    simp [checkerboard, hLtri hab]
  have hR : (checkerboard L)⁻¹ = checkerboard L⁻¹ := inv_eq_right_inv hAI
  have hRTN : (checkerboard L)⁻¹.IsTotallyNonneg := by
    rw [hR]
    exact IsTotallyNonneg.checkerboard_inverse L L⁻¹ hLI hdet hL
  let : Invertible (checkerboard L) := (checkerboard L).invertibleOfIsUnitDet hAunit
  have hRtri : (checkerboard L)⁻¹.IsLowerTriangular :=
    blockTriangular_inv_of_blockTriangular hAtri
  have hAR : checkerboard L * (checkerboard L)⁻¹ = 1 :=
    (checkerboard L).mul_nonsing_inv hAunit
  have hRdet : ((checkerboard L)⁻¹).det ≠ 0 := det_ne_zero_of_left_inverse hAR
  have hRdiag := hRTN.diagonal_pos_of_det_ne_zero hRdet i.castSucc
  have hLdiag := hL.diagonal_pos_of_det_ne_zero hdet.ne' i.succ
  have heq := congrArg (fun A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ =>
    A i.succ i.castSucc) hAR
  rw [hAtri.mul_apply_succ_castSucc hRtri i] at heq
  simp only [checkerboard_apply_succ_castSucc, checkerboard_apply_diag,
    Matrix.one_apply_ne (ne_of_gt i.castSucc_lt_succ)] at heq
  have hprod : 0 < L i.succ i.castSucc * (checkerboard L)⁻¹ i.castSucc i.castSucc :=
    mul_pos hsub hRdiag
  have hmul : 0 < L i.succ i.succ * (checkerboard L)⁻¹ i.succ i.castSucc := by
    nlinarith only [heq, hprod]
  exact pos_of_mul_pos_right hmul hLdiag.le

/-- Positive adjacent entries of the TN product `(checkerboard L)⁻¹ M` follow
from the superdiagonal of `M` and either its subdiagonal or the subdiagonal of
`L` together with the diagonal of `M`. -/
theorem IsLowerTriangular.checkerboard_inv_mul_adjacent_pos
    {n : ℕ} {L M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hLtri : L.IsLowerTriangular) (hL : L.IsTotallyNonneg)
    (hdet : 0 < L.det) (hM : M.IsTotallyNonneg)
    (hsuper : ∀ i : Fin n, 0 < M i.castSucc i.succ)
    (hsub : ∀ i : Fin n, 0 < M i.succ i.castSucc ∨
      (0 < L i.succ i.castSucc ∧ 0 < M i.castSucc i.castSucc)) :
    (∀ i : Fin n, 0 < ((checkerboard L)⁻¹ * M) i.castSucc i.succ) ∧
      ∀ i : Fin n, 0 < ((checkerboard L)⁻¹ * M) i.succ i.castSucc := by
  have hunit : IsUnit L.det := isUnit_iff_ne_zero.mpr hdet.ne'
  have hLI : L * L⁻¹ = 1 := L.mul_nonsing_inv hunit
  have hAI : checkerboard L * checkerboard L⁻¹ = 1 := by
    rw [← checkerboard_mul, hLI, checkerboard_one]
  have hAunit : IsUnit (checkerboard L).det := isUnit_det_of_right_inverse hAI
  have hR : (checkerboard L)⁻¹ = checkerboard L⁻¹ := inv_eq_right_inv hAI
  have hRTN : (checkerboard L)⁻¹.IsTotallyNonneg := by
    rw [hR]
    exact IsTotallyNonneg.checkerboard_inverse L L⁻¹ hLI hdet hL
  have hAR : checkerboard L * (checkerboard L)⁻¹ = 1 :=
    (checkerboard L).mul_nonsing_inv hAunit
  have hRdet : ((checkerboard L)⁻¹).det ≠ 0 := det_ne_zero_of_left_inverse hAR
  have hRdiag := hRTN.diagonal_pos_of_det_ne_zero hRdet
  constructor
  · intro i
    exact mul_apply_pos_of_pos_summand hRTN.nonneg hM.nonneg
      i.castSucc i.succ i.castSucc (hRdiag i.castSucc) (hsuper i)
  · intro i
    rcases hsub i with hMi | ⟨hLi, hMd⟩
    · exact mul_apply_pos_of_pos_summand hRTN.nonneg hM.nonneg
        i.succ i.castSucc i.succ (hRdiag i.succ) hMi
    · exact mul_apply_pos_of_pos_summand hRTN.nonneg hM.nonneg
        i.succ i.castSucc i.castSucc
          (hLtri.checkerboard_inv_subdiag_pos hL hdet i hLi) hMd

end Matrix
