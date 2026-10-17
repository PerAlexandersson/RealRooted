import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic

/-!
# Powers of the sign minus one

Elementary parity identities used by polynomial transformations.
-/

namespace Parity

/-- Multiplying two powers of minus one cancels the bounded exponent. -/
theorem neg_one_pow_mul_eq_neg_one_pow_sub {R : Type*} [Ring R]
    {n j : ℕ} (hj : j ≤ n) :
    (-1 : R) ^ n * (-1 : R) ^ j = (-1 : R) ^ (n - j) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hj
  rw [Nat.add_sub_cancel_left, ← pow_add, show j + k + j = k + 2 * j by ring, pow_add, pow_mul]
  norm_num

/-- Every square of a power of minus one is one. -/
theorem neg_one_pow_sq {R : Type*} [Ring R] (k : ℕ) :
    ((-1 : R) ^ k) ^ 2 = 1 := by
  rw [← pow_mul, mul_comm, pow_mul]
  norm_num

end Parity
