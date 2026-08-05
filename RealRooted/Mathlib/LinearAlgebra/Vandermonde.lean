import Mathlib.LinearAlgebra.Vandermonde

/-!
# Ordered Vandermonde determinants

This file adds the strict positivity consequence of the Vandermonde
determinant formula for a strictly increasing family.
-/

public section

namespace Matrix

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

/-- A Vandermonde determinant on a strictly increasing family is positive. -/
theorem det_vandermonde_pos_of_strictMono {q : ℕ}
    {y : Fin q → R} (hy : StrictMono y) :
    0 < (vandermonde y).det := by
  rw [det_vandermonde]
  apply Finset.prod_pos
  intro i hi
  apply Finset.prod_pos
  intro j hj
  exact sub_pos.mpr (hy (Finset.mem_Ioi.mp hj))

end Matrix
