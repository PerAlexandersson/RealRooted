import RealRooted.Linear
import RealRooted.SequenceClosure

/-!
# Product factor certificates

Real-rootedness certificates for scalar, monomial, affine, and powered affine
factors, together with the sequence-valued certificates shared by the product
recurrence layers.
-/

open Polynomial
open scoped BigOperators

namespace RealRooted

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

/-- Constant-first spelling of `isRealRooted_X_add_C`. -/
theorem isRealRooted_C_add_X (t : ℝ) :
    (C t + X : ℝ[X]) ≠ 0 ∧ (C t + X : ℝ[X]).Splits := by
  simpa [add_comm] using isRealRooted_X_add_C t

/-- Constant-first spelling of `isRealRooted_C_mul_X_add_C`. -/
theorem isRealRooted_C_add_C_mul_X {s t : ℝ} (hs : s ≠ 0) :
    (C t + C s * X : ℝ[X]) ≠ 0 ∧ (C t + C s * X : ℝ[X]).Splits := by
  simpa [add_comm] using isRealRooted_C_mul_X_add_C (s := s) (t := t) hs

theorem isRealRooted_C_mul_X_add_C_mul {p : ℝ[X]} {s t : ℝ}
    (hp : p ≠ 0 ∧ p.Splits) (hs : s ≠ 0) :
    ((C s * X + C t) * p ≠ 0 ∧ ((C s * X + C t) * p).Splits) :=
  isRealRooted_mul_of_isRealRooted (isRealRooted_C_mul_X_add_C hs) hp

theorem isRealRooted_mul_C_mul_X_add_C {p : ℝ[X]} {s t : ℝ}
    (hp : p ≠ 0 ∧ p.Splits) (hs : s ≠ 0) :
    (p * (C s * X + C t) ≠ 0 ∧ (p * (C s * X + C t)).Splits) :=
  isRealRooted_mul_of_isRealRooted hp (isRealRooted_C_mul_X_add_C hs)

theorem isRealRooted_C_add_C_mul_X_mul {p : ℝ[X]} {s t : ℝ}
    (hp : p ≠ 0 ∧ p.Splits) (hs : s ≠ 0) :
    ((C t + C s * X) * p ≠ 0 ∧ ((C t + C s * X) * p).Splits) := by
  simpa [add_comm] using isRealRooted_C_mul_X_add_C_mul (p := p) (s := s) (t := t) hp hs

theorem isRealRooted_mul_C_add_C_mul_X {p : ℝ[X]} {s t : ℝ}
    (hp : p ≠ 0 ∧ p.Splits) (hs : s ≠ 0) :
    (p * (C t + C s * X) ≠ 0 ∧ (p * (C t + C s * X)).Splits) := by
  simpa [add_comm] using isRealRooted_mul_C_mul_X_add_C (p := p) (s := s) (t := t) hp hs

theorem isRealRooted_X_add_C_mul {p : ℝ[X]} {t : ℝ}
    (hp : p ≠ 0 ∧ p.Splits) :
    ((X + C t) * p ≠ 0 ∧ ((X + C t) * p).Splits) := by
  simpa using
    (isRealRooted_C_mul_X_add_C_mul (p := p) (s := 1) (t := t) hp (by norm_num))

theorem isRealRooted_mul_X_add_C {p : ℝ[X]} {t : ℝ}
    (hp : p ≠ 0 ∧ p.Splits) :
    (p * (X + C t) ≠ 0 ∧ (p * (X + C t)).Splits) := by
  simpa using
    (isRealRooted_mul_C_mul_X_add_C (p := p) (s := 1) (t := t) hp (by norm_num))

/-- Constant-first spelling of `isRealRooted_X_add_C_mul`. -/
theorem isRealRooted_C_add_X_mul {p : ℝ[X]} {t : ℝ}
    (hp : p ≠ 0 ∧ p.Splits) :
    ((C t + X) * p ≠ 0 ∧ ((C t + X) * p).Splits) := by
  simpa [add_comm] using isRealRooted_X_add_C_mul (p := p) (t := t) hp

/-- Right-factor variant of `isRealRooted_C_add_X_mul`. -/
theorem isRealRooted_mul_C_add_X {p : ℝ[X]} {t : ℝ}
    (hp : p ≠ 0 ∧ p.Splits) :
    (p * (C t + X) ≠ 0 ∧ (p * (C t + X)).Splits) := by
  simpa [add_comm] using isRealRooted_mul_X_add_C (p := p) (t := t) hp

/-- Powers of a unit-slope real linear factor are real-rooted. -/
theorem isRealRooted_X_add_C_pow (t : ℝ) (n : Nat) :
    ((X + C t : ℝ[X]) ^ n ≠ 0 ∧ ((X + C t : ℝ[X]) ^ n).Splits) :=
  isRealRooted_pow_of_isRealRooted (isRealRooted_X_add_C t) n

/-- Constant-first spelling of `isRealRooted_X_add_C_pow`. -/
theorem isRealRooted_C_add_X_pow (t : ℝ) (n : Nat) :
    ((C t + X : ℝ[X]) ^ n ≠ 0 ∧ ((C t + X : ℝ[X]) ^ n).Splits) :=
  isRealRooted_pow_of_isRealRooted (isRealRooted_C_add_X t) n

/-- Powers of a nonzero-slope real linear factor are real-rooted. -/
theorem isRealRooted_C_mul_X_add_C_pow {s t : ℝ} (hs : s ≠ 0) (n : Nat) :
    ((C s * X + C t : ℝ[X]) ^ n ≠ 0 ∧
      ((C s * X + C t : ℝ[X]) ^ n).Splits) :=
  isRealRooted_pow_of_isRealRooted (isRealRooted_C_mul_X_add_C hs) n

/-- Constant-first spelling of `isRealRooted_C_mul_X_add_C_pow`. -/
theorem isRealRooted_C_add_C_mul_X_pow {s t : ℝ} (hs : s ≠ 0) (n : Nat) :
    ((C t + C s * X : ℝ[X]) ^ n ≠ 0 ∧
      ((C t + C s * X : ℝ[X]) ^ n).Splits) := by
  simpa [add_comm] using isRealRooted_C_mul_X_add_C_pow (s := s) (t := t) hs n


namespace ProductSequenceInternal

theorem isRealRooted_X_add_C_one_sequence (t : Nat → ℝ) :
    ∀ n : Nat, (X + C (t n) : ℝ[X]) ≠ 0 ∧ (X + C (t n) : ℝ[X]).Splits :=
  fun n => by simpa using isRealRooted_X_add_C_pow (t n) 1

theorem isRealRooted_C_add_X_one_sequence (t : Nat → ℝ) :
    ∀ n : Nat, (C (t n) + X : ℝ[X]) ≠ 0 ∧ (C (t n) + X : ℝ[X]).Splits :=
  fun n => by simpa using isRealRooted_C_add_X_pow (t n) 1

theorem isRealRooted_C_add_C_mul_X_one_sequence {s t : Nat → ℝ}
    (hs : ∀ n : Nat, s n ≠ 0) :
    ∀ n : Nat, (C (t n) + C (s n) * X : ℝ[X]) ≠ 0 ∧
      (C (t n) + C (s n) * X : ℝ[X]).Splits :=
  fun n => by simpa using isRealRooted_C_add_C_mul_X_pow (hs n) 1

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

theorem isRealRooted_C_add_X_pow_sequence (t : Nat → ℝ) (m : Nat → Nat) :
    ∀ n : Nat, (C (t n) + X : ℝ[X]) ^ (m n) ≠ 0 ∧
      ((C (t n) + X : ℝ[X]) ^ (m n)).Splits :=
  fun n => isRealRooted_C_add_X_pow (t n) (m n)

theorem isRealRooted_C_mul_X_add_C_pow_sequence {s t : Nat → ℝ}
    (hs : ∀ n : Nat, s n ≠ 0) (m : Nat → Nat) :
    ∀ n : Nat, (C (s n) * X + C (t n) : ℝ[X]) ^ (m n) ≠ 0 ∧
      ((C (s n) * X + C (t n) : ℝ[X]) ^ (m n)).Splits :=
  fun n => isRealRooted_C_mul_X_add_C_pow (hs n) (m n)

theorem isRealRooted_C_add_C_mul_X_pow_sequence {s t : Nat → ℝ}
    (hs : ∀ n : Nat, s n ≠ 0) (m : Nat → Nat) :
    ∀ n : Nat, (C (t n) + C (s n) * X : ℝ[X]) ^ (m n) ≠ 0 ∧
      ((C (t n) + C (s n) * X : ℝ[X]) ^ (m n)).Splits :=
  fun n => isRealRooted_C_add_C_mul_X_pow (hs n) (m n)


end ProductSequenceInternal

/-- Powers of the root-at-zero factor are real-rooted. -/
theorem isRealRooted_X_pow (n : Nat) :
    ((X : ℝ[X]) ^ n ≠ 0 ∧ (((X : ℝ[X]) ^ n).Splits)) :=
  isRealRooted_pow_of_isRealRooted isRealRooted_X n

/-- Powers of a nonzero scalar constant are real-rooted. -/
theorem isRealRooted_C_pow {a : ℝ} (ha : a ≠ 0) (n : Nat) :
    ((C a : ℝ[X]) ^ n ≠ 0 ∧ (((C a : ℝ[X]) ^ n).Splits)) :=
  isRealRooted_pow_of_isRealRooted (isRealRooted_C ha) n

namespace ProductSequenceInternal

theorem isRealRooted_C_pow_sequence {c : Nat → ℝ}
    (hc : ∀ n : Nat, c n ≠ 0) (m : Nat → Nat) :
    ∀ n : Nat, (C (c n) : ℝ[X]) ^ (m n) ≠ 0 ∧
      ((C (c n) : ℝ[X]) ^ (m n)).Splits :=
  fun n => isRealRooted_C_pow (hc n) (m n)

theorem isRealRooted_X_pow_sequence (m : Nat → Nat) :
    ∀ n : Nat, (X : ℝ[X]) ^ (m n) ≠ 0 ∧ ((X : ℝ[X]) ^ (m n)).Splits :=
  fun n => isRealRooted_X_pow (m n)

end ProductSequenceInternal

end RealRooted
