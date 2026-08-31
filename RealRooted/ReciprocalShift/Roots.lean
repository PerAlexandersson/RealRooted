import RealRooted.Mathlib.Algebra.Polynomial.Reverse
import RealRooted.PFPolynomial

/-!
# Roots of degree-padded reciprocal shifts

The root multiset of `reciprocalShift D p` consists of padding zeros and the
inverses of the nonzero roots of `p`.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- At a degree bound, a reciprocal shift contributes padding zeros and
inverts every nonzero root, with multiplicity. -/
theorem roots_reciprocalShift_eq
    {D : ℕ} {p : ℝ[X]} (hp_ne : p ≠ 0) (hp_splits : p.Splits)
    (hdegree : p.natDegree ≤ D) :
    (reciprocalShift D p).roots =
      Multiset.replicate (D - p.natDegree) 0
        + (p.roots.filter fun r ↦ r ≠ 0).map (·⁻¹) := by
  rw [reciprocalShift_eq_X_pow_mul_reverse hdegree]
  have hpow : (X ^ (D - p.natDegree) : ℝ[X]) ≠ 0 :=
    pow_ne_zero _ X_ne_zero
  have hreverse : p.reverse ≠ 0 := by
    rw [Ne, Polynomial.reverse_eq_zero]
    exact hp_ne
  rw [Polynomial.roots_mul (mul_ne_zero hpow hreverse), Polynomial.roots_X_pow,
    Multiset.nsmul_singleton, Polynomial.roots_reverse_eq_filter_map_inv hp_ne hp_splits]

end RealRooted
