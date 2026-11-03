module

import RealRooted.Linear
import RealRooted.SequenceClosure
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Polynomial.Splits

/-!
# Product factor certificates

Real-rootedness certificates for scalar, monomial, affine, and powered affine
factors, together with the sequence-valued certificates shared by the product
recurrence layers.
-/

public section

open Polynomial
open scoped BigOperators

namespace RealRooted

/-- The affine polynomial `C s * X + C t` is nonzero and splits when `s ≠ 0`. -/
lemma isRealRooted_C_mul_X_add_C {s t : ℝ} (hs : s ≠ 0) :
    ((C s * X + C t) ≠ 0 ∧ (C s * X + C t).Splits) := by
  have hd : (C s * X + C t : ℝ[X]).degree = 1 := degree_linear hs
  exact ⟨fun h => by simp [h] at hd, Splits.of_degree_le_one hd.le⟩

/-- Nonzero constant polynomials are real-rooted. -/
lemma isRealRooted_C {a : ℝ} (ha : a ≠ 0) :
    ((C a : ℝ[X]) ≠ 0 ∧ (C a : ℝ[X]).Splits) :=
  ⟨C_ne_zero.mpr ha, Polynomial.Splits.C (R := ℝ) a⟩

/-- Unit-slope real linear factors are real-rooted. -/
theorem isRealRooted_X_add_C (t : ℝ) :
    (X + C t : ℝ[X]) ≠ 0 ∧ (X + C t : ℝ[X]).Splits := by
  simpa using isRealRooted_C_mul_X_add_C (s := 1) (t := t) (by norm_num)

/-- Powers of a unit-slope real linear factor are real-rooted. -/
theorem isRealRooted_X_add_C_pow (t : ℝ) (n : Nat) :
    ((X + C t : ℝ[X]) ^ n ≠ 0 ∧ ((X + C t : ℝ[X]) ^ n).Splits) :=
  isRealRooted_pow_of_isRealRooted (isRealRooted_X_add_C t) n

/-- Powers of a nonzero-slope real linear factor are real-rooted. -/
theorem isRealRooted_C_mul_X_add_C_pow {s t : ℝ} (hs : s ≠ 0) (n : Nat) :
    ((C s * X + C t : ℝ[X]) ^ n ≠ 0 ∧
      ((C s * X + C t : ℝ[X]) ^ n).Splits) :=
  isRealRooted_pow_of_isRealRooted (isRealRooted_C_mul_X_add_C hs) n

namespace ProductSequence

theorem isRealRooted_X_add_C_one_sequence (t : Nat → ℝ) :
    ∀ n : Nat, (X + C (t n) : ℝ[X]) ≠ 0 ∧ (X + C (t n) : ℝ[X]).Splits :=
  fun n => by simpa using isRealRooted_X_add_C_pow (t n) 1

theorem isRealRooted_X_sequence :
    ∀ _ : Nat, (X : ℝ[X]) ≠ 0 ∧ (X : ℝ[X]).Splits :=
  fun _ => isRealRooted_X

theorem isRealRooted_C_mul_X_sequence {a : Nat → ℝ}
    (ha : ∀ n : Nat, a n ≠ 0) :
    ∀ n : Nat, (C (a n) * X : ℝ[X]) ≠ 0 ∧
      (C (a n) * X : ℝ[X]).Splits :=
  fun n => isRealRooted_C_mul_of_isRealRooted isRealRooted_X (ha n)

theorem isRealRooted_of_even_odd_sequence {P : Nat → ℝ[X]}
    (heven : ∀ n : Nat, P (2 * n) ≠ 0 ∧ (P (2 * n)).Splits)
    (hodd : ∀ n : Nat, P (2 * n + 1) ≠ 0 ∧ (P (2 * n + 1)).Splits) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  intro n
  rcases Nat.mod_two_eq_zero_or_one n with hmod | hmod
  · have hn : n = 2 * (n / 2) := by simpa [hmod] using (Nat.div_add_mod n 2).symm
    rw [hn]
    exact heven (n / 2)
  · have hn : n = 2 * (n / 2) + 1 := by simpa [hmod] using (Nat.div_add_mod n 2).symm
    rw [hn]
    exact hodd (n / 2)

theorem isRealRooted_C_sequence {c : Nat → ℝ} (hc : ∀ n : Nat, c n ≠ 0) :
    ∀ n : Nat, (C (c n) : ℝ[X]) ≠ 0 ∧ (C (c n) : ℝ[X]).Splits :=
  fun n => isRealRooted_C (hc n)

theorem isRealRooted_one_sequence :
    ∀ _ : Nat, (1 : ℝ[X]) ≠ 0 ∧ (1 : ℝ[X]).Splits :=
  isRealRooted_C_sequence (c := fun _ => 1) (fun _ => by norm_num)

theorem isRealRooted_C_mul_X_add_C_sequence {s t : Nat → ℝ}
    (hs : ∀ n : Nat, s n ≠ 0) :
    ∀ n : Nat, (C (s n) * X + C (t n) : ℝ[X]) ≠ 0 ∧
      (C (s n) * X + C (t n) : ℝ[X]).Splits :=
  fun n => isRealRooted_C_mul_X_add_C (hs n)

theorem isRealRooted_fixed_X_add_C_pow_sequence (t : ℝ) (m : Nat → Nat) :
    ∀ n : Nat, (X + C t : ℝ[X]) ^ (m n) ≠ 0 ∧
      ((X + C t : ℝ[X]) ^ (m n)).Splits :=
  fun n => isRealRooted_X_add_C_pow t (m n)

theorem isRealRooted_X_add_C_pow_sequence (t : Nat → ℝ) (m : Nat → Nat) :
    ∀ n : Nat, (X + C (t n) : ℝ[X]) ^ (m n) ≠ 0 ∧
      ((X + C (t n) : ℝ[X]) ^ (m n)).Splits :=
  fun n => isRealRooted_X_add_C_pow (t n) (m n)

end ProductSequence

/-- Powers of the root-at-zero factor are real-rooted. -/
theorem isRealRooted_X_pow (n : Nat) :
    ((X : ℝ[X]) ^ n ≠ 0 ∧ (((X : ℝ[X]) ^ n).Splits)) :=
  isRealRooted_pow_of_isRealRooted isRealRooted_X n

end RealRooted
