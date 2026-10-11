import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic

/-!
# Powers of the sign minus one

Elementary parity identities used by polynomial transformations.
-/

/-- Multiplying two powers of minus one cancels the bounded exponent. -/
theorem neg_one_pow_mul_eq_neg_one_pow_sub {R : Type*} [Ring R]
    {n j : ℕ} (hj : j ≤ n) :
    (-1 : R) ^ n * (-1 : R) ^ j = (-1 : R) ^ (n - j) := by
  nth_rw 1 [← Nat.sub_add_cancel hj]
  rw [pow_add, mul_assoc, ← mul_pow]
  norm_num

/-- Every square of a power of minus one is one. -/
theorem neg_one_pow_sq {R : Type*} [Ring R] (k : ℕ) :
    ((-1 : R) ^ k) ^ 2 = 1 := by
  rw [← pow_mul]
  norm_num
