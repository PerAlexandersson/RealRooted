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

/-- Casted form of `Nat.add_one_mul_choose_eq`, rewritten with Pascal's identity. -/
theorem cast_add_one_mul_choose_eq {R : Type*} [CommSemiring R] (n k : ℕ) :
    ((n + 1 : ℕ) : R) * (Nat.choose n k : R) =
      ((k + 1 : ℕ) : R) *
        ((Nat.choose n k : R) + (Nat.choose n (k + 1) : R)) := by
  simpa [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.choose_succ_succ,
    mul_comm] using
    congrArg (fun m : ℕ => (m : R)) (Nat.add_one_mul_choose_eq n k)

end Nat
