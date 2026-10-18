/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
import Mathlib.Algebra.Polynomial.Degree.Lemmas

/-!
# Coefficients and degree of `p.comp (-X)`

Companions of `Polynomial.degree_comp_neg_X`: the coefficients of `p.comp (-X)` are those of
`p` with alternating signs, and the natural degree is unchanged.
-/

namespace Polynomial

variable {R : Type*} [CommRing R]

/-- The coefficients of `p.comp (-X)` are those of `p` with alternating signs. -/
theorem coeff_comp_neg_X (p : R[X]) (n : ℕ) :
    (p.comp (-X)).coeff n = p.coeff n * (-1) ^ n := by
  simpa using comp_C_mul_X_coeff (p := p) (r := (-1 : R)) (n := n)

/-- `p.comp (-X)` has the natural degree of `p`. -/
@[simp] theorem natDegree_comp_neg_X (p : R[X]) : (p.comp (-X)).natDegree = p.natDegree :=
  natDegree_eq_of_degree_eq degree_comp_neg_X

end Polynomial
