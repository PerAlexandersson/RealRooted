import Mathlib.Data.Nat.Choose.Cast

/-!
# Extra lemmas about casts of binomial coefficients

This file contains small compatibility lemmas for `Mathlib.Data.Nat.Choose.Cast`.
-/

namespace Nat

/-- A binomial coefficient remains nonzero after casting to a characteristic-zero
target. -/
theorem cast_choose_ne_zero {R : Type*} [AddMonoidWithOne R] [CharZero R]
    {n k : ℕ} (h : k ≤ n) : (Nat.choose n k : R) ≠ 0 :=
  Nat.cast_ne_zero.mpr (Nat.choose_ne_zero h)

end Nat
