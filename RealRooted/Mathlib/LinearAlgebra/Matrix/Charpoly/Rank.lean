import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Matrix rank and zero roots of the characteristic polynomial

This file records the general relationship between matrix nullity and the
geometric and algebraic multiplicities of the zero eigenvalue.
-/

namespace Matrix

open scoped Classical in
/-- The geometric multiplicity of the zero eigenvalue is the nullity of a
finite square matrix. -/
theorem finrank_eigenspace_zero_eq_card_sub_rank
    {K : Type*} [Field K] {n : Type*} [Fintype n] (A : Matrix n n K) :
    Module.finrank K (Module.End.eigenspace A.mulVecLin 0) =
      Fintype.card n - A.rank := by
  rw [Module.End.eigenspace_zero]
  have hnull := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
  have hrank :
      A.rank = Module.finrank K (LinearMap.range A.mulVecLin) := by
    rw [Matrix.rank_eq_finrank_span_cols, ← Matrix.range_mulVecLin]
  have hdim : Module.finrank K (n → K) = Fintype.card n := by simp
  rw [← hrank, hdim] at hnull
  lia

open scoped Classical in
/-- The nullity of a finite square matrix is at most the algebraic
multiplicity of zero in its characteristic polynomial. Equality need not hold
for a matrix with a nontrivial nilpotent Jordan block. -/
theorem card_sub_rank_le_rootMultiplicity_charpoly_zero
    {K : Type*} [Field K] {n : Type*} [Fintype n] (A : Matrix n n K) :
    Fintype.card n - A.rank ≤ A.charpoly.rootMultiplicity 0 := by
  rw [← A.finrank_eigenspace_zero_eq_card_sub_rank,
    ← Matrix.charpoly_mulVecLin]
  exact LinearMap.finrank_eigenspace_le A.mulVecLin 0

end Matrix
