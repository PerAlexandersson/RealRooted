/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.Ring

/-!
# Four-variable alternants at a common power

The elementary determinant calculation used in Lemma 2 of the unpublished manuscript
*Real limiting spectra for balanced five-diagonal Toeplitz matrices* (2026-10-29),
tracked in RealRooted issue #2157. This is an identity over any commutative ring.
-/

public section

namespace Matrix

/-- If the last two variables have the same `m`th power, the four-variable alternant
with row exponents `(m + 1, m, 1, 0)` factors into four elementary factors. -/
theorem det_alternant_four_of_pow_eq {R : Type*} [CommRing R]
    (a c z w ε : R) (m : ℕ) (hz : z ^ m = ε) (hw : w ^ m = ε) :
    Matrix.det !![a ^ (m + 1), c ^ (m + 1), z ^ (m + 1), w ^ (m + 1);
      a ^ m, c ^ m, z ^ m, w ^ m; a, c, z, w; 1, 1, 1, 1] =
      (a - c) * (a ^ m - ε) * (c ^ m - ε) * (z - w) := by
  simp only [pow_succ, hz, hw]
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring

/-- The descending four-variable Vandermonde determinant in factored form. -/
theorem det_vandermonde_four {R : Type*} [CommRing R] (a c z w : R) :
    Matrix.det !![a ^ 3, c ^ 3, z ^ 3, w ^ 3;
      a ^ 2, c ^ 2, z ^ 2, w ^ 2; a, c, z, w; 1, 1, 1, 1] =
      (a - c) * (a - z) * (a - w) * (c - z) * (c - w) * (z - w) := by
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring

end Matrix
