import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Tactic

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

/-- Casted descending factorial of length three. -/
theorem cast_descFactorial_three {R : Type*} [CommRing R] (n : ℕ) :
    (n.descFactorial 3 : R) = n * (n - 1) * (n - 2) := by
  rw [descFactorial]
  cases n with
  | zero => simp
  | succ n =>
      cases n with
      | zero => simp
      | succ n =>
          cases n with
          | zero => simp
          | succ n =>
              rw [Nat.cast_mul, Nat.cast_descFactorial_two]
              have hsub : n + 1 + 1 + 1 - 2 = n + 1 := by lia
              rw [hsub]
              norm_num [Nat.cast_add]
              ring

/-- Casted form of `Nat.choose n 3`. -/
theorem cast_choose_three {R : Type*} [Field R] [CharZero R] (n : ℕ) :
    (Nat.choose n 3 : R) = n * (n - 1) * (n - 2) / 6 := by
  rw [← cast_descFactorial_three, descFactorial_eq_factorial_mul_choose]
  norm_num [factorial]

end Nat
