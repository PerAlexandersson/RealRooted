module

public import Mathlib.Algebra.Polynomial.Degree.SmallDegree

public section

namespace Polynomial

/-- A polynomial of degree at most two is its three-term coefficient expansion.

This is the degree-two analogue of `Polynomial.eq_X_add_C_of_natDegree_le_one`. -/
theorem eq_X_sq_add_X_add_C_of_natDegree_le_two {R : Type*} [Semiring R] {p : R[X]}
    (h : p.natDegree ≤ 2) :
    p = C (p.coeff 2) * X ^ 2 + C (p.coeff 1) * X + C (p.coeff 0) := by
  ext n
  match n with
  | 0 => simp
  | 1 => simp
  | 2 => simp
  | m + 3 => simp [coeff_eq_zero_of_natDegree_lt (show p.natDegree < m + 3 by lia)]

end Polynomial
