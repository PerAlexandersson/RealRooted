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

/-- Casted form of `Nat.choose_succ_right_eq`. -/
theorem cast_choose_succ_right_eq {R : Type*} [NonAssocSemiring R] (n k : ℕ) :
    (Nat.choose n (k + 1) : R) * (k + 1 : R) =
      (Nat.choose n k : R) * (n - k : R) := by
  simpa [Nat.cast_mul] using
    congrArg (fun m : ℕ => (m : R)) (Nat.choose_succ_right_eq n k)

end Nat
