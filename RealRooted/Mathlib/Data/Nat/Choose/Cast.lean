/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.Tactic

/-!
# Extra lemmas about casts of binomial coefficients

This file contains small compatibility lemmas for `Mathlib.Data.Nat.Choose.Cast`.
-/

public section

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

/-- Casted adjacent binomial determinant identity. -/
theorem cast_choose_sq_sub_choose_pred_mul_choose_succ_eq
    {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [CharZero R]
    {n k : ℕ} (hkpos : 0 < k) (hkn : k ≤ n) :
    (Nat.choose n k : R) ^ 2 -
        (Nat.choose n (k - 1) : R) * (Nat.choose n (k + 1) : R) =
      (Nat.choose n k : R) * (Nat.choose (n + 1) k : R) / (k + 1 : R) := by
  have hpred : k - 1 + 1 = k := by lia
  have hcast : ((k - 1 : ℕ) : R) + 1 = k := by exact_mod_cast hpred
  have hsub : n - (k - 1) = n - k + 1 := by lia
  have hprev := cast_choose_succ_right_eq (R := R) n (k - 1)
  rw [hpred, hcast, hsub, Nat.cast_add, Nat.cast_one] at hprev
  have hnext := cast_choose_succ_right_eq (R := R) n k
  have hpascal : (Nat.choose (n + 1) k : R) =
      (Nat.choose n (k - 1) : R) + Nat.choose n k := by
    exact_mod_cast (show Nat.choose (n + 1) k =
      Nat.choose n (k - 1) + Nat.choose n k by
        simpa only [Nat.succ_eq_add_one, hpred] using Nat.choose_succ_succ n (k - 1))
  rw [hpascal, eq_div_iff (by positivity : (k + 1 : R) ≠ 0)]
  linear_combination (Nat.choose n k : R) * hprev -
    (Nat.choose n (k - 1) : R) * hnext

/-- Casted descending factorial of length three. -/
theorem cast_descFactorial_three {R : Type*} [CommRing R] (n : ℕ) :
    (n.descFactorial 3 : R) = n * (n - 1) * (n - 2) := by
  rcases n with (_ | _ | _ | n) <;>
    simp [descFactorial]
  ring

/-- Casted form of `Nat.choose n 3`. -/
theorem cast_choose_three {R : Type*} [Field R] [CharZero R] (n : ℕ) :
    (Nat.choose n 3 : R) = n * (n - 1) * (n - 2) / 6 := by
  rw [← cast_descFactorial_three, descFactorial_eq_factorial_mul_choose]
  norm_num [factorial]

end Nat
