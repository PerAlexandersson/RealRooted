import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.Reverse

/-!
# Chow polynomial operator

This module packages the quotient operator occurring in the defining recursion
for Chow and Chow-derangement polynomials.  It is stated over a commutative
ring, independently of any matrix or positivity assumptions.
-/

open Polynomial

namespace Polynomial

noncomputable section

/-- The Chow operator `Sₙ(p) = (reflect n p - p) / (X - 1)`.

For `p.natDegree ≤ n`, the numerator vanishes at one, so the quotient is exact;
see `X_sub_one_mul_chowS`. -/
def chowS {R : Type*} [CommRing R] (n : ℕ) (p : R[X]) : R[X] :=
  (p.reflect n - p) /ₘ (X - 1)

/-- The defining quotient for `chowS` is exact at every reflection bound at
least the degree of the input. -/
theorem X_sub_one_mul_chowS {R : Type*} [CommRing R]
    (n : ℕ) (p : R[X]) (hdegree : p.natDegree ≤ n) :
    (X - 1) * chowS n p = p.reflect n - p := by
  let _ := invertibleOne (α := R)
  have heval : (p.reflect n).eval 1 = p.eval 1 := by
    simpa using eval₂_reflect_mul_pow (RingHom.id R) (1 : R) n p hdegree
  have hmod : (p.reflect n - p) %ₘ (X - 1) = 0 := by
    change (p.reflect n - p) %ₘ (X - C (1 : R)) = 0
    rw [modByMonic_X_sub_C_eq_C_eval]
    simp [heval]
  change (X - 1) * ((p.reflect n - p) /ₘ (X - 1)) = p.reflect n - p
  calc
    (X - 1) * ((p.reflect n - p) /ₘ (X - 1)) =
        (p.reflect n - p) %ₘ (X - 1) + (X - 1) * ((p.reflect n - p) /ₘ (X - 1)) := by
      rw [hmod, zero_add]
    _ = p.reflect n - p := modByMonic_add_div _ _

end

end Polynomial
