import Mathlib.Data.Nat.Cast.Basic

/-!
# Extra lemmas about casts of natural numbers

This file contains small compatibility lemmas for `Mathlib.Data.Nat.Cast.Basic`.
-/

namespace Nat

/-- A positive natural number remains nonzero after casting to a
characteristic-zero target. -/
theorem cast_ne_zero_of_pos {R : Type*} [AddMonoidWithOne R] [CharZero R]
    {n : ℕ} (h : 0 < n) : (n : R) ≠ 0 :=
  Nat.cast_ne_zero.mpr (Nat.ne_of_gt h)

end Nat
