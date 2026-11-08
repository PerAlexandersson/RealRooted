module

public import RealRooted.BrandenLeite.WeightedDerivativeKernel.Basic
public import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Tactic

/-! Weighted kernels of constant polynomials. -/

public section

open Matrix

namespace RealRooted.BrandenLeite

/-- A constant-polynomial weighted kernel is a weighted one-step shift. -/
theorem weightedDerivativeKernel_C_fin (c κ : ℝ) (n : ℕ) :
    (weightedDerivativeKernel κ (Polynomial.C c).coeff).submatrix
      (Fin.val : Fin (n + 1) → ℕ) (Fin.val : Fin (n + 1) → ℕ) =
    (weightedIncidence (fun i : Fin (n + 1) ↦ i.succ)
      (fun i ↦ (i.val + 1 : ℕ) * c)).submatrix id Fin.castSucc := by
  ext i j
  simp only [Matrix.submatrix_apply, weightedDerivativeKernel,
    Polynomial.coeff_C, weightedIncidence_apply, id_eq]
  by_cases he : j.val = i.val + 1
  · have he' : i.succ = j.castSucc := by apply Fin.ext; simpa using he.symm
    have hle : j.val ≤ i.val + 1 := by lia
    have hsub : i.val + 1 - j.val = 0 := by lia
    simp only [hle, ite_true, hsub, Nat.cast_zero, mul_zero, add_zero, he']
    rw [he]
  · have he' : i.succ ≠ j.castSucc := by
      intro h
      have hv := congrArg Fin.val h
      exact he (by simpa using hv.symm)
    rw [ite_eq_right he']
    by_cases hle : j.val ≤ i.val + 1
    · have hsub : i.val + 1 - j.val ≠ 0 := by lia
      simp [hle, hsub]
    · simp [hle]

/-- Nonnegative constants have totally nonnegative finite weighted kernels. -/
theorem weightedDerivativeKernel_C_fin_isTotallyNonneg (c κ : ℝ) (hc : 0 ≤ c)
    (n : ℕ) :
    ((weightedDerivativeKernel κ (Polynomial.C c).coeff).submatrix
      (Fin.val : Fin (n + 1) → ℕ) (Fin.val : Fin (n + 1) → ℕ)).IsTotallyNonneg := by
  rw [weightedDerivativeKernel_C_fin]
  have hinc := isTotallyNonnegRect_monotoneWeightedIncidence
    (fun i : Fin (n + 1) ↦ i.succ) (fun _ _ hij ↦ by simpa using hij)
    (fun i ↦ (i.val + 1 : ℕ) * c) (fun i ↦ mul_nonneg (Nat.cast_nonneg _) hc)
  exact (hinc.submatrix (rows := id) (cols := Fin.castSucc)
    strictMono_id (fun _ _ hij ↦ hij)).toSquare

end RealRooted.BrandenLeite
