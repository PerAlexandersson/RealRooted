import RealRooted.BrandenLeite.Network
import RealRooted.BrandenLeite.ResolvableTotallyNonneg

/-!
# Total nonnegativity of triangular-network path matrices

This opt-in endpoint combines the literal triangular-network resolution with
the existing resolution-to-total-nonnegativity theorem.  The direct
Lindström--Gessel--Viennot determinant proof remains separate work.
-/

namespace RealRooted.BrandenLeite

/-- A nonnegative weighted triangular-network path matrix is totally
nonnegative. -/
theorem isTotallyNonneg_networkMatrix (weights : ℕ → ℕ → ℝ)
    (hweights : ∀ n k, 0 ≤ weights n k) :
    Matrix.IsTotallyNonneg (networkMatrix weights) :=
  isTotallyNonneg_of_isResolvable (isResolvable_networkMatrix weights hweights)

/-- Nonnegativity on the relevant triangular edge weights suffices for total
nonnegativity of the literal path matrix. -/
theorem isTotallyNonneg_networkMatrix_of_nonneg_le (weights : ℕ → ℕ → ℝ)
    (hweights : ∀ n k, k ≤ n → 0 ≤ weights n k) :
    Matrix.IsTotallyNonneg (networkMatrix weights) := by
  let extend : ℕ → ℕ → ℝ := fun n k => if k ≤ n then weights n k else 0
  have hextend : ∀ n k, 0 ≤ extend n k := by
    intro n k
    simp only [extend]
    split
    · exact hweights _ _ ‹_›
    · exact le_rfl
  have hmatrix : networkMatrix extend = networkMatrix weights := by
    ext n k
    exact networkPathSum_congr_of_le_lt extend weights n k fun i j hji _ => by
      simp [extend, hji]
  rw [← hmatrix]
  exact isTotallyNonneg_networkMatrix extend hextend

end RealRooted.BrandenLeite
