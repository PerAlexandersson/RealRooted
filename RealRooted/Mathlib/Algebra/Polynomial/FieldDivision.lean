import Mathlib.Algebra.Polynomial.FieldDivision

/-!
# Dividing out a linear factor at a root

At a root `r` of `p`, write `p = (X - C r) * q` with `q = p /ₘ (X - C r)`. This file records
that the roots of `q` are those of `p` with one copy of `r` removed, and that
`p''(r) = 2 q'(r)`.
-/

namespace Polynomial

/-- Dividing out the linear factor at a root removes one copy of that root. -/
theorem roots_divByMonic_X_sub_C {R : Type*} [CommRing R] [IsDomain R] [DecidableEq R]
    {p : R[X]} {r : R} (hr : p.IsRoot r) : (p /ₘ (X - C r)).roots = p.roots.erase r := by
  by_cases hq : p /ₘ (X - C r) = 0
  · have hp : p = 0 := by rw [← mul_divByMonic_eq_iff_isRoot.mpr hr, hq, mul_zero]
    simp [hp]
  · conv_rhs => rw [← mul_divByMonic_eq_iff_isRoot.mpr hr]
    rw [roots_mul (mul_ne_zero (X_sub_C_ne_zero r) hq), roots_X_sub_C, Multiset.singleton_add,
      Multiset.erase_cons_head]

/-- At a root `r` of `p`, the second derivative of `p` at `r` is twice the derivative at `r`
of the cofactor `p /ₘ (X - C r)`. -/
theorem eval_derivative_derivative_of_isRoot {R : Type*} [CommRing R] {p : R[X]} {r : R}
    (hr : p.IsRoot r) :
    p.derivative.derivative.eval r = 2 * (p /ₘ (X - C r)).derivative.eval r := by
  conv_lhs => rw [← mul_divByMonic_eq_iff_isRoot.mpr hr]
  simp only [derivative_mul, derivative_sub, derivative_X, derivative_C, sub_zero, one_mul,
    derivative_add, zero_mul, eval_add, eval_mul, eval_sub, eval_X, eval_C, sub_self]
  ring

end Polynomial
