import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

/-!
# Characteristic matrices of principal submatrices

This file records that forming the characteristic matrix commutes with taking
a principal submatrix along an injective index map.
-/

namespace Matrix

/-- The characteristic matrix of a principal submatrix is the corresponding
principal submatrix of the characteristic matrix. -/
theorem charmatrix_submatrix_self {R : Type*} [CommRing R]
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix n n R) (f : m → n) (hf : Function.Injective f) :
    A.charmatrix.submatrix f f = (A.submatrix f f).charmatrix := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [Matrix.submatrix_apply, Matrix.charmatrix_apply_eq]
  · rw [Matrix.submatrix_apply,
      Matrix.charmatrix_apply_ne _ _ _ (fun h => hij (hf h)),
      Matrix.charmatrix_apply_ne _ _ _ hij, Matrix.submatrix_apply]

end Matrix
