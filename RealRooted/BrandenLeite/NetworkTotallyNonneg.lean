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

end RealRooted.BrandenLeite
