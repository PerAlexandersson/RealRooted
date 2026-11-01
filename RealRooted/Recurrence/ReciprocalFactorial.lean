module

public import Mathlib.RingTheory.Polynomial.Pochhammer
public import Mathlib.Data.Nat.Choose.Basic

import Mathlib.Tactic

/-!
# Reciprocal factorials with integer arguments

This file extends reciprocal factorials by zero to negative integer arguments.  The extension
makes shifts uniform at support boundaries and factors finite sums of shifted terms without
cancelling a possibly zero common factor.
-/

@[expose] public section

namespace RealRooted

open scoped BigOperators

/-- The reciprocal factorial of an integer, extended by zero at negative arguments. -/
def reciprocalFactorial (a : ℤ) : ℚ :=
  if 0 ≤ a then ((a.toNat.factorial : ℚ)⁻¹) else 0

/-- At a nonnegative integer, `reciprocalFactorial` is the reciprocal of the usual factorial. -/
@[simp]
theorem reciprocalFactorial_of_nonneg {a : ℤ} (ha : 0 ≤ a) :
    reciprocalFactorial a = (a.toNat.factorial : ℚ)⁻¹ := by
  simp [reciprocalFactorial, ha]

/-- At a negative integer, `reciprocalFactorial` vanishes. -/
@[simp]
theorem reciprocalFactorial_of_neg {a : ℤ} (ha : a < 0) :
    reciprocalFactorial a = 0 := by
  simp [reciprocalFactorial, not_le.mpr ha]

/-- On natural-number arguments, `reciprocalFactorial` is the reciprocal factorial. -/
theorem reciprocalFactorial_natCast (n : ℕ) :
    reciprocalFactorial (n : ℤ) = (n.factorial : ℚ)⁻¹ := by
  simp [reciprocalFactorial]

private theorem reciprocalFactorial_sub_one (a : ℤ) :
    reciprocalFactorial (a - 1) = (a : ℚ) * reciprocalFactorial a := by
  rcases a with (n | n)
  · rcases n with (_ | n)
    · norm_num [reciprocalFactorial]
    · have hnonneg : (0 : ℤ) ≤ n + 1 := by positivity
      simp [reciprocalFactorial, Nat.factorial_succ, mul_inv_rev, hnonneg]
      field_simp
  · simp [reciprocalFactorial]

/-- Shifting a reciprocal factorial down by `d` extracts the descending Pochhammer factor. -/
theorem reciprocalFactorial_sub_nat (a : ℤ) (d : ℕ) :
    reciprocalFactorial (a - d) =
      (descPochhammer ℚ d).eval (a : ℚ) * reciprocalFactorial a := by
  induction d with
  | zero => simp
  | succ d ih =>
      rw [Nat.cast_succ, sub_add_eq_sub_sub, reciprocalFactorial_sub_one, ih,
        descPochhammer_succ_right, Polynomial.eval_mul, Polynomial.eval_sub,
        Polynomial.eval_X, Polynomial.eval_natCast]
      push_cast
      ring

/-- The binomial coefficient whose lower argument is an integer, extended by zero below zero. -/
def extendedChoose (m : ℕ) (k : ℤ) : ℕ :=
  if 0 ≤ k then m.choose k.toNat else 0

/-- The extended binomial coefficient is a product of three factorial or reciprocal-factorial
terms, including when the lower argument lies outside the usual support. -/
theorem extendedChoose_eq_factorial_mul_reciprocalFactorial (m : ℕ) (k : ℤ) :
    (extendedChoose m k : ℚ) =
      (m.factorial : ℚ) * reciprocalFactorial k *
        reciprocalFactorial ((m : ℤ) - k) := by
  rcases k with (k | k)
  · by_cases hkm : k ≤ m
    · rw [show extendedChoose m (Int.ofNat k) = m.choose k by simp [extendedChoose]]
      change (m.choose k : ℚ) =
        (m.factorial : ℚ) * reciprocalFactorial (k : ℤ) *
          reciprocalFactorial ((m : ℤ) - (k : ℤ))
      rw [reciprocalFactorial_natCast, ← Int.ofNat_sub hkm,
        reciprocalFactorial_natCast]
      have h := congrArg (fun n : ℕ ↦ (n : ℚ))
        (Nat.choose_mul_factorial_mul_factorial hkm)
      push_cast at h
      field_simp
      exact h
    · have hmk : m < k := Nat.lt_of_not_ge hkm
      have hmkInt : (m : ℤ) < k := by exact_mod_cast hmk
      have hneg : (m : ℤ) - k < 0 := by lia
      rw [show extendedChoose m (Int.ofNat k) = m.choose k by simp [extendedChoose],
        Nat.choose_eq_zero_of_lt hmk]
      change (0 : ℚ) =
        (m.factorial : ℚ) * reciprocalFactorial (k : ℤ) *
          reciprocalFactorial ((m : ℤ) - (k : ℤ))
      rw [reciprocalFactorial_of_neg hneg]
      simp
  · rw [show extendedChoose m (Int.negSucc k) = 0 by simp [extendedChoose],
      reciprocalFactorial_of_neg (Int.negSucc_lt_zero k)]
    simp

/-- A finite sum of products of shifted reciprocal factorials factors into an unshifted common
factor and a finite sum of descending Pochhammer products. -/
theorem sum_mul_prod_reciprocalFactorial_sub_eq {S I : Type*}
    (s : Finset S) (indices : Finset I) (A : ℚ) (p : S → ℚ) (M : I → ℤ)
    (d : S → I → ℕ) :
    (∑ x ∈ s, A * p x * ∏ i ∈ indices, reciprocalFactorial (M i - d x i)) =
      A * (∏ i ∈ indices, reciprocalFactorial (M i)) *
        ∑ x ∈ s, p x *
          ∏ i ∈ indices, (descPochhammer ℚ (d x i)).eval (M i : ℚ) := by
  simp_rw [reciprocalFactorial_sub_nat]
  calc
    _ = ∑ x ∈ s, A * p x *
        ((∏ i ∈ indices, (descPochhammer ℚ (d x i)).eval (M i : ℚ)) *
          ∏ i ∈ indices, reciprocalFactorial (M i)) := by
      congr 1
      funext x
      rw [Finset.prod_mul_distrib]
    _ = ∑ x ∈ s, (A * ∏ i ∈ indices, reciprocalFactorial (M i)) *
        (p x * ∏ i ∈ indices,
          (descPochhammer ℚ (d x i)).eval (M i : ℚ)) := by
      congr 1
      funext x
      ring
    _ = _ := by rw [Finset.mul_sum]

end RealRooted
