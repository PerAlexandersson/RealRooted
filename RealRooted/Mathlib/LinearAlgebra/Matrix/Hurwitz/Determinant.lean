import RealRooted.Mathlib.LinearAlgebra.Matrix.Hurwitz
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Low-order Hurwitz determinants

This file gives the first leading-principal determinant formulas for the
classical Hurwitz matrix. They are kept separate from the entry-definition
module so consumers of the matrix itself do not inherit determinant imports.
-/

namespace Matrix

variable {R : Type*} [CommRing R]

theorem hurwitzLeadingPrincipal_det_zero (c : ℕ → R) :
    (hurwitzLeadingPrincipal c 0).det = 1 := by
  simp

theorem hurwitzLeadingPrincipal_det_one (c : ℕ → R) :
    (hurwitzLeadingPrincipal c 1).det = c 0 := by
  simp [hurwitzLeadingPrincipal, hurwitz]

@[simp]
theorem hurwitzLeadingPrincipal_det_two (c : ℕ → R) :
    (hurwitzLeadingPrincipal c 2).det = c 0 * c 1 := by
  rw [Matrix.det_fin_two]
  simp [hurwitzLeadingPrincipal, hurwitz]

@[simp]
theorem hurwitzLeadingPrincipal_det_three (c : ℕ → R) :
    (hurwitzLeadingPrincipal c 3).det =
      c 0 * (c 1 * c 2 - c 0 * c 3) := by
  rw [Matrix.det_fin_three]
  simp [hurwitzLeadingPrincipal, hurwitz]
  ring

end Matrix
