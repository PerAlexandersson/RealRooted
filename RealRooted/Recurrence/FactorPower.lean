module

public import Mathlib.Tactic.Ring

/-!
# Fixed-factor deflation for three-term recurrences

A recurrence whose two multipliers contain successive powers of one fixed factor can be
deflated to an ordinary three-term recurrence.  This module contains only the algebraic
identity; tactic recognition and certificate construction live under `RealRooted.Tactic`.
-/

@[expose] public section

namespace RealRooted

/-- A factored three-term recurrence is its reduced recurrence multiplied by successive
powers of the fixed factor. -/
theorem eq_pow_mul_of_factoredThreeTerm {R : Type*} [CommSemiring R]
    {P Q : ℕ → R} (q : R) (a b : ℕ → R) (h0 : P 0 = Q 0)
    (h1 : P 1 = q * Q 1)
    (hP : ∀ n, P (n + 2) = q * a n * P (n + 1) + q ^ 2 * b n * P n)
    (hQ : ∀ n, Q (n + 2) = a n * Q (n + 1) + b n * Q n) :
    ∀ n, P n = q ^ n * Q n := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero => simpa only [pow_zero, one_mul] using h0
  | one => simpa only [pow_one] using h1
  | more n ih ih_succ =>
      rw [hP n, hQ n, ih, ih_succ, pow_add, pow_succ]
      ring

end RealRooted
