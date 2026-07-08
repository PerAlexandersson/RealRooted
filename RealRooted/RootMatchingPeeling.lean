import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Tactic

/-!
# Root-Matching Peeling

This file records coefficient-control lemmas for the issue #42
multiplicity-preserving root-matching route.  The intended induction peels one
nearby monic linear factor at a time; these lemmas isolate the exact
synthetic-division recurrences needed after such a peel.
-/

open Polynomial

namespace RealRooted
namespace RootMatchingPeeling

/--
Synthetic-division coefficient recursion for dividing by a monic linear factor.

If `f = (X - C r) * fTail`, then the quotient coefficients satisfy
`fTail.coeff k = f.coeff (k + 1) + r * fTail.coeff (k + 1)`.
-/
theorem coeff_tail_of_eq_linear_mul {f fTail : ℝ[X]} {r : ℝ}
    (hf : f = (X - C r) * fTail) (k : ℕ) :
    fTail.coeff k = f.coeff (k + 1) + r * fTail.coeff (k + 1) := by
  rw [hf, sub_mul, Polynomial.coeff_sub, Polynomial.coeff_X_mul,
    Polynomial.coeff_C_mul]
  ring

/--
One-step recursion for the coefficient difference of two quotients by nearby
monic linear factors.
-/
theorem coeff_sub_recursion {f fTail p pTail : ℝ[X]} {r q : ℝ}
    (hf : f = (X - C r) * fTail) (hp : p = (X - C q) * pTail) (k : ℕ) :
    pTail.coeff k - fTail.coeff k =
      (p.coeff (k + 1) - f.coeff (k + 1)) +
        q * (pTail.coeff (k + 1) - fTail.coeff (k + 1)) +
          (q - r) * fTail.coeff (k + 1) := by
  rw [coeff_tail_of_eq_linear_mul hf k, coeff_tail_of_eq_linear_mul hp k]
  ring

end RootMatchingPeeling
end RealRooted
