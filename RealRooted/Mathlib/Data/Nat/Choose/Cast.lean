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

/-- Casted adjacent binomial determinant identity. -/
theorem cast_choose_sq_sub_choose_pred_mul_choose_succ_eq
    {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [CharZero R]
    {n k : ℕ} (hkpos : 0 < k) (hkn : k ≤ n) :
    (Nat.choose n k : R) ^ 2 -
        (Nat.choose n (k - 1) : R) * (Nat.choose n (k + 1) : R) =
      (Nat.choose n k : R) * (Nat.choose (n + 1) k : R) / (k + 1 : R) := by
  have hk_pred_succ : k - 1 + 1 = k := Nat.sub_add_cancel (Nat.succ_le_of_lt hkpos)
  have hk_pred_succ_cast : ((k - 1 : ℕ) : R) + 1 = (k : R) := by
    exact_mod_cast hk_pred_succ
  have hden_prev_nat : n - (k - 1) = n + 1 - k := by lia
  have hden_prev_pos : 0 < n - (k - 1) := by lia
  have hden_succ_pos : 0 < n + 1 - k := by lia
  have hk_succ_ne : (k + 1 : R) ≠ 0 := by positivity
  have hden_prev_ne : ((n - (k - 1) : ℕ) : R) ≠ 0 := by
    exact_mod_cast (ne_of_gt hden_prev_pos)
  have hden_succ_ne : ((n + 1 - k : ℕ) : R) ≠ 0 := by
    exact_mod_cast (ne_of_gt hden_succ_pos)
  have hD_pos : 0 < (n : R) + 1 - (k : R) := by
    have hknR : (k : R) ≤ (n : R) := by exact_mod_cast hkn
    linarith
  have hD_ne : (n : R) + 1 - (k : R) ≠ 0 := by
    intro h
    linarith
  have hprev_raw := Nat.cast_choose_succ_right_eq (R := R) n (k - 1)
  rw [hk_pred_succ, hk_pred_succ_cast] at hprev_raw
  have hnext_raw := Nat.cast_choose_succ_right_eq (R := R) n k
  have hsucc_raw :
      (Nat.choose n k : R) * ((n + 1 : ℕ) : R) =
        (Nat.choose (n + 1) k : R) * ((n + 1 - k : ℕ) : R) := by
    exact_mod_cast Nat.choose_mul_succ_eq n k
  have hprev :
      (Nat.choose n (k - 1) : R) =
        (Nat.choose n k : R) * (k : R) / ((n + 1 - k : ℕ) : R) := by
    rw [← hden_prev_nat]
    field_simp [hden_prev_ne]
    nlinarith [hprev_raw]
  have hnext :
      (Nat.choose n (k + 1) : R) =
        (Nat.choose n k : R) * ((n - k : ℕ) : R) / (k + 1 : R) := by
    field_simp [hk_succ_ne]
    nlinarith [hnext_raw]
  have hsucc :
      (Nat.choose (n + 1) k : R) =
        (Nat.choose n k : R) * ((n + 1 : ℕ) : R) /
          ((n + 1 - k : ℕ) : R) := by
    field_simp [hden_succ_ne]
    nlinarith [hsucc_raw]
  have hnk_cast : ((n - k : ℕ) : R) = (n : R) - (k : R) := by
    rw [Nat.cast_sub hkn]
  have hnkp1_cast : ((n + 1 - k : ℕ) : R) = (n : R) + 1 - (k : R) := by
    rw [Nat.cast_sub (by lia : k ≤ n + 1)]
    norm_num [Nat.cast_add]
  rw [hprev, hnext, hsucc]
  rw [hnk_cast, hnkp1_cast]
  norm_num [Nat.cast_add]
  field_simp [hk_succ_ne, hD_ne]
  ring_nf

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
