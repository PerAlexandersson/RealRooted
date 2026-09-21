import Mathlib.Basic.Real.Basic
import RealRooted.CombinatorialExamples.JacobiStirling.FirstKind
import RealRooted.Mathlib.LinearAlgebra.Matrix.TotallyNonneg.ElementarySymmetric

/-!
# Total nonnegativity of the first-kind Jacobi--Stirling triangle

The whole triangle is an elementary-symmetric triangle whose initial weight is
zero. Thus its leading entry and zero first column are part of the same generic
bidiagonal certificate; no separate block argument or LGV machinery is needed.
-/

namespace RealRooted.JacobiStirling

noncomputable section

/-- The weights of the whole first-kind triangle, including its initial zero. -/
def firstKindTriangleWeight (z : ℝ) (i : ℕ) : ℝ :=
  i * (i + z)

/-- The first-kind Jacobi--Stirling triangle as an infinite matrix. -/
def firstKindMatrix (z : ℝ) : Matrix ℕ ℕ ℝ :=
  fun n k => firstKind z n k

/-- Removing row and column zero identifies the positive-index block with the
elementary-symmetric triangle on the usual weights. -/
theorem firstKind_succ_succ_eq_elementarySymmetricTriangle
    (z : ℝ) (n k : ℕ) :
    firstKind z (n + 1) (k + 1) =
      Matrix.elementarySymmetricTriangle (firstKindWeight z) n k := by
  rw [firstKind_eq_ite_esym]
  by_cases hk : k ≤ n
  · rw [ite_eq_left (by lia), Matrix.elementarySymmetricTriangle_apply, ite_eq_left hk]
    rw [show n + 1 - (k + 1) = n - k by lia]
    unfold RealRooted.CoefficientDominance.Symmetric.esym
      Matrix.elementarySymmetricPrefix
    rw [Finset.range_val]
    rfl
  · rw [ite_eq_right (by lia), Matrix.elementarySymmetricTriangle_apply, ite_eq_right hk]

private theorem firstKindTriangleWeight_zero_column (z : ℝ) (n : ℕ) :
    Matrix.elementarySymmetricTriangle (firstKindTriangleWeight z) (n + 1) 0 = 0 := by
  rw [Matrix.elementarySymmetricTriangle_apply, ite_eq_left (Nat.zero_le _)]
  simp only [Nat.sub_zero, Matrix.elementarySymmetricPrefix]
  let s := (Multiset.range (n + 1)).map (firstKindTriangleWeight z)
  change s.esymm (n + 1) = 0
  have hcard : s.card = n + 1 := by simp [s]
  rw [← hcard]
  unfold Multiset.esymm
  rw [Multiset.powersetCard_self]
  simp only [Multiset.map_singleton, Multiset.sum_singleton]
  rw [Multiset.prod_eq_zero_iff]
  apply Multiset.mem_map.mpr
  exact ⟨0, by rw [Multiset.mem_range]; lia,
    by simp [firstKindTriangleWeight]⟩

/-- The literal first-kind triangle is exactly the generic
elementary-symmetric triangle with weights `i * (i + z)`, starting at `i = 0`.
-/
theorem firstKindMatrix_eq_elementarySymmetricTriangle (z : ℝ) :
    firstKindMatrix z =
      Matrix.elementarySymmetricTriangle (firstKindTriangleWeight z) := by
  ext n k
  induction n generalizing k with
  | zero =>
      cases k with
      | zero => simp [firstKindMatrix, Matrix.elementarySymmetricTriangle]
      | succ k => simp [firstKindMatrix, Matrix.elementarySymmetricTriangle]
  | succ n ih =>
      cases k with
      | zero =>
          rw [firstKindMatrix, firstKind_succ_zero,
            firstKindTriangleWeight_zero_column]
      | succ k =>
          rw [firstKindMatrix, firstKind_succ_succ,
            Matrix.elementarySymmetricTriangle_succ_succ, ← ih k, ← ih (k + 1)]
          rfl

private theorem firstKindTriangleWeight_nonneg {z : ℝ} (hz : -1 ≤ z) (i : ℕ) :
    0 ≤ firstKindTriangleWeight z i := by
  rw [firstKindTriangleWeight]
  have hi : 0 ≤ (i : ℝ) := Nat.cast_nonneg i
  by_cases hi0 : i = 0
  · simp [hi0]
  · have hi1 : 1 ≤ (i : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hi0
    exact mul_nonneg hi (by linarith)

/-- For `z ≥ -1`, the whole first-kind Jacobi--Stirling triangle is totally
nonnegative. -/
theorem firstKindMatrix_isTotallyNonneg {z : ℝ} (hz : -1 ≤ z) :
    (firstKindMatrix z).IsTotallyNonneg := by
  rw [firstKindMatrix_eq_elementarySymmetricTriangle]
  exact Matrix.elementarySymmetricTriangle_isTotallyNonneg
    (firstKindTriangleWeight_nonneg hz)

/-- The Legendre--Stirling first-kind triangle (`z = 0`) is totally
nonnegative. -/
theorem legendreStirlingFirstMatrix_isTotallyNonneg :
    (firstKindMatrix 0).IsTotallyNonneg :=
  firstKindMatrix_isTotallyNonneg (by norm_num)

end

end RealRooted.JacobiStirling
