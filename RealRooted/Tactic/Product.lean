import RealRooted.Linear
import RealRooted.PosCombo
import RealRooted.Tactic.Finish

/-!
# Product-factor tactic

Small wrappers for recurrence steps where a row is obtained by multiplying the
previous row by a real linear factor.
-/

open Polynomial

namespace RealRooted

lemma isRealRooted_C_mul_X_add_C {s t : ℝ} (hs : s ≠ 0) :
    ((C s * X + C t) ≠ 0 ∧ (C s * X + C t).Splits) := by
  have hEq : C s * (X - C (-t / s)) = C s * X + C t := by
    calc
      C s * (X - C (-t / s))
          = C s * X - C s * C (-t / s) := by grind
      _ = C s * X - C (s * (-t / s)) := by simp
      _ = C s * X - C (-t) := by grind
      _ = C s * X + C t := by simp
  rw [← hEq]
  exact isRealRooted_C_mul
    (isRealRooted_X_sub_C (-t / s)).1 (isRealRooted_X_sub_C (-t / s)).2 hs

/-- Nonzero constant polynomials are real-rooted. -/
lemma isRealRooted_C {a : ℝ} (ha : a ≠ 0) :
    ((C a : ℝ[X]) ≠ 0 ∧ (C a : ℝ[X]).Splits) :=
  ⟨C_ne_zero.mpr ha, Polynomial.Splits.C (R := ℝ) a⟩

theorem isRealRooted_C_mul_X_add_C_mul {p : ℝ[X]} {s t : ℝ}
    (hp : p ≠ 0 ∧ p.Splits) (hs : s ≠ 0) :
    ((C s * X + C t) * p ≠ 0 ∧ ((C s * X + C t) * p).Splits) :=
  isRealRooted_mul
    (isRealRooted_C_mul_X_add_C hs).1 (isRealRooted_C_mul_X_add_C hs).2 hp.1 hp.2

theorem isRealRooted_mul_C_mul_X_add_C {p : ℝ[X]} {s t : ℝ}
    (hp : p ≠ 0 ∧ p.Splits) (hs : s ≠ 0) :
    (p * (C s * X + C t) ≠ 0 ∧ (p * (C s * X + C t)).Splits) :=
  isRealRooted_mul hp.1 hp.2
    (isRealRooted_C_mul_X_add_C hs).1 (isRealRooted_C_mul_X_add_C hs).2

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
    ((X + C t : ℝ[X]) ^ n ≠ 0 ∧ ((X + C t : ℝ[X]) ^ n).Splits) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      simpa [pow_succ, mul_comm, mul_left_comm, mul_assoc] using
        isRealRooted_X_add_C_mul (p := (X + C t : ℝ[X]) ^ n) (t := t) ih

/-- Constant-first spelling of `isRealRooted_X_add_C_pow`. -/
theorem isRealRooted_C_add_X_pow (t : ℝ) (n : Nat) :
    ((C t + X : ℝ[X]) ^ n ≠ 0 ∧ ((C t + X : ℝ[X]) ^ n).Splits) := by
  simpa [add_comm] using isRealRooted_X_add_C_pow t n

/-- Powers of a nonzero-slope real linear factor are real-rooted. -/
theorem isRealRooted_C_mul_X_add_C_pow {s t : ℝ} (hs : s ≠ 0) (n : Nat) :
    ((C s * X + C t : ℝ[X]) ^ n ≠ 0 ∧
      ((C s * X + C t : ℝ[X]) ^ n).Splits) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [pow_succ]
      exact isRealRooted_mul ih.1 ih.2
        (isRealRooted_C_mul_X_add_C hs).1
        (isRealRooted_C_mul_X_add_C hs).2

/-- Constant-first spelling of `isRealRooted_C_mul_X_add_C_pow`. -/
theorem isRealRooted_C_add_C_mul_X_pow {s t : ℝ} (hs : s ≠ 0) (n : Nat) :
    ((C t + C s * X : ℝ[X]) ^ n ≠ 0 ∧
      ((C t + C s * X : ℝ[X]) ^ n).Splits) := by
  simpa [add_comm] using isRealRooted_C_mul_X_add_C_pow (s := s) (t := t) hs n

private theorem isRealRooted_X_add_C_one_sequence (t : Nat → ℝ) :
    ∀ n : Nat, (X + C (t n) : ℝ[X]) ≠ 0 ∧ (X + C (t n) : ℝ[X]).Splits :=
  fun n => by simpa using isRealRooted_X_add_C_pow (t n) 1

private theorem isRealRooted_C_add_X_one_sequence (t : Nat → ℝ) :
    ∀ n : Nat, (C (t n) + X : ℝ[X]) ≠ 0 ∧ (C (t n) + X : ℝ[X]).Splits :=
  fun n => by simpa using isRealRooted_C_add_X_pow (t n) 1

private theorem isRealRooted_C_add_C_mul_X_one_sequence {s t : Nat → ℝ}
    (hs : ∀ n : Nat, s n ≠ 0) :
    ∀ n : Nat, (C (t n) + C (s n) * X : ℝ[X]) ≠ 0 ∧
      (C (t n) + C (s n) * X : ℝ[X]).Splits :=
  fun n => by simpa using isRealRooted_C_add_C_mul_X_pow (hs n) 1

private theorem isRealRooted_X_sequence :
    ∀ _ : Nat, (X : ℝ[X]) ≠ 0 ∧ (X : ℝ[X]).Splits :=
  fun _ => isRealRooted_X

private theorem isRealRooted_C_sequence {c : Nat → ℝ} (hc : ∀ n : Nat, c n ≠ 0) :
    ∀ n : Nat, (C (c n) : ℝ[X]) ≠ 0 ∧ (C (c n) : ℝ[X]).Splits :=
  fun n => isRealRooted_C (hc n)

private theorem isRealRooted_C_mul_X_add_C_sequence {s t : Nat → ℝ}
    (hs : ∀ n : Nat, s n ≠ 0) :
    ∀ n : Nat, (C (s n) * X + C (t n) : ℝ[X]) ≠ 0 ∧
      (C (s n) * X + C (t n) : ℝ[X]).Splits :=
  fun n => isRealRooted_C_mul_X_add_C (hs n)

private theorem isRealRooted_fixed_X_add_C_pow_sequence (t : ℝ) (m : Nat → Nat) :
    ∀ n : Nat, (X + C t : ℝ[X]) ^ (m n) ≠ 0 ∧
      ((X + C t : ℝ[X]) ^ (m n)).Splits :=
  fun n => isRealRooted_X_add_C_pow t (m n)

private theorem isRealRooted_X_add_C_pow_sequence (t : Nat → ℝ) (m : Nat → Nat) :
    ∀ n : Nat, (X + C (t n) : ℝ[X]) ^ (m n) ≠ 0 ∧
      ((X + C (t n) : ℝ[X]) ^ (m n)).Splits :=
  fun n => isRealRooted_X_add_C_pow (t n) (m n)

private theorem isRealRooted_C_add_X_pow_sequence (t : Nat → ℝ) (m : Nat → Nat) :
    ∀ n : Nat, (C (t n) + X : ℝ[X]) ^ (m n) ≠ 0 ∧
      ((C (t n) + X : ℝ[X]) ^ (m n)).Splits :=
  fun n => isRealRooted_C_add_X_pow (t n) (m n)

private theorem isRealRooted_C_mul_X_add_C_pow_sequence {s t : Nat → ℝ}
    (hs : ∀ n : Nat, s n ≠ 0) (m : Nat → Nat) :
    ∀ n : Nat, (C (s n) * X + C (t n) : ℝ[X]) ^ (m n) ≠ 0 ∧
      ((C (s n) * X + C (t n) : ℝ[X]) ^ (m n)).Splits :=
  fun n => isRealRooted_C_mul_X_add_C_pow (hs n) (m n)

private theorem isRealRooted_C_add_C_mul_X_pow_sequence {s t : Nat → ℝ}
    (hs : ∀ n : Nat, s n ≠ 0) (m : Nat → Nat) :
    ∀ n : Nat, (C (t n) + C (s n) * X : ℝ[X]) ^ (m n) ≠ 0 ∧
      ((C (t n) + C (s n) * X : ℝ[X]) ^ (m n)).Splits :=
  fun n => isRealRooted_C_add_C_mul_X_pow (hs n) (m n)

/-- Sequence shell for first-order product recurrences with a supplied factor certificate. -/
theorem isRealRooted_of_product_factor_sequence
    {P F : Nat → ℝ[X]}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hfactor : ∀ n : Nat, F n ≠ 0 ∧ (F n).Splits)
    (hstep : ∀ n : Nat, P (n + 1) = F n * P n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  intro n
  induction n with
  | zero =>
      simpa using hbase
  | succ n ih =>
      have hnext : F n * P n ≠ 0 ∧ (F n * P n).Splits :=
        isRealRooted_mul (hfactor n).1 (hfactor n).2 ih.1 ih.2
      simpa [Nat.succ_eq_add_one, hstep n] using hnext

/-- Right-factor variant of `isRealRooted_of_product_factor_sequence`. -/
theorem isRealRooted_of_product_factor_right_sequence
    {P F : Nat → ℝ[X]}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hfactor : ∀ n : Nat, F n ≠ 0 ∧ (F n).Splits)
    (hstep : ∀ n : Nat, P (n + 1) = P n * F n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  exact isRealRooted_of_product_factor_sequence hbase hfactor
    (fun n => by rw [hstep n, mul_comm])

/-- Sequence shell for identity product recurrences. -/
theorem isRealRooted_of_product_identity_sequence
    {P : Nat → ℝ[X]}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hstep : ∀ n : Nat, P (n + 1) = P n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  intro n
  induction n with
  | zero =>
      simpa using hbase
  | succ n ih =>
      simpa [Nat.succ_eq_add_one, hstep n] using ih

/-- Sequence shell for recurrences that multiply each row by `X`. -/
theorem isRealRooted_of_product_root_zero_sequence
    {P : Nat → ℝ[X]}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hstep : ∀ n : Nat, P (n + 1) = X * P n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_factor_sequence hbase isRealRooted_X_sequence hstep

/-- Right-factor variant of `isRealRooted_of_product_root_zero_sequence`. -/
theorem isRealRooted_of_product_root_zero_right_sequence
    {P : Nat → ℝ[X]}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hstep : ∀ n : Nat, P (n + 1) = P n * X) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_factor_right_sequence hbase isRealRooted_X_sequence hstep

/-- Sequence shell for period-two product recurrences. -/
theorem isRealRooted_of_product_period_two_sequence
    {P : Nat → ℝ[X]}
    (hbase_zero : P 0 ≠ 0 ∧ (P 0).Splits)
    (hbase_one : P 1 ≠ 0 ∧ (P 1).Splits)
    (hstep : ∀ n : Nat, P (n + 2) = P n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  intro n
  refine Nat.strong_induction_on n ?_
  intro n ih
  cases n with
  | zero =>
      simpa using hbase_zero
  | succ n =>
      cases n with
      | zero =>
          simpa using hbase_one
      | succ n =>
          have hprev := ih n (Nat.lt_succ_of_lt (Nat.lt_succ_self n))
          change P (n + 2) ≠ 0 ∧ (P (n + 2)).Splits
          simpa [hstep n] using hprev

/-- Lift real-rootedness from a quotient sequence through row-wise real-rooted
left factors. -/
theorem isRealRooted_of_product_lift_sequence
    {P Q F : Nat → ℝ[X]}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hfactor : ∀ n : Nat, F n ≠ 0 ∧ (F n).Splits)
    (hrow : ∀ n : Nat, P n = F n * Q n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  intro n
  have hnext : F n * Q n ≠ 0 ∧ (F n * Q n).Splits :=
    isRealRooted_mul (hfactor n).1 (hfactor n).2 (hquot n).1 (hquot n).2
  simpa [hrow n] using hnext

/-- Right-factor variant of `isRealRooted_of_product_lift_sequence`. -/
theorem isRealRooted_of_product_lift_right_sequence
    {P Q F : Nat → ℝ[X]}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hfactor : ∀ n : Nat, F n ≠ 0 ∧ (F n).Splits)
    (hrow : ∀ n : Nat, P n = Q n * F n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  exact isRealRooted_of_product_lift_sequence hquot hfactor
    (fun n => by rw [hrow n, mul_comm])

/-- Lift through a row-wise factor `X`, used for product reductions with a
persistent root at the origin. -/
theorem isRealRooted_of_X_lift_sequence
    {P Q : Nat → ℝ[X]}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, P n = X * Q n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_lift_sequence hquot isRealRooted_X_sequence hrow

/-- Right-factor variant of `isRealRooted_of_X_lift_sequence`. -/
theorem isRealRooted_of_X_lift_right_sequence
    {P Q : Nat → ℝ[X]}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, P n = Q n * X) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_lift_right_sequence hquot isRealRooted_X_sequence hrow

/-- Lift through row-wise unit-slope real linear factors. -/
theorem isRealRooted_of_X_add_C_lift_sequence
    {P Q : Nat → ℝ[X]} {t : Nat → ℝ}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, P n = (X + C (t n)) * Q n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_lift_sequence hquot
    (isRealRooted_X_add_C_one_sequence t) hrow

/-- Right-factor variant of `isRealRooted_of_X_add_C_lift_sequence`. -/
theorem isRealRooted_of_X_add_C_lift_right_sequence
    {P Q : Nat → ℝ[X]} {t : Nat → ℝ}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, P n = Q n * (X + C (t n))) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_lift_right_sequence hquot
    (isRealRooted_X_add_C_one_sequence t) hrow

/-- Constant-first spelling of `isRealRooted_of_X_add_C_lift_sequence`. -/
theorem isRealRooted_of_C_add_X_lift_sequence
    {P Q : Nat → ℝ[X]} {t : Nat → ℝ}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, P n = (C (t n) + X) * Q n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_lift_sequence hquot
    (isRealRooted_C_add_X_one_sequence t) hrow

/-- Right-factor variant of `isRealRooted_of_C_add_X_lift_sequence`. -/
theorem isRealRooted_of_C_add_X_lift_right_sequence
    {P Q : Nat → ℝ[X]} {t : Nat → ℝ}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, P n = Q n * (C (t n) + X)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_lift_right_sequence hquot
    (isRealRooted_C_add_X_one_sequence t) hrow

/-- Lift through row-wise nonzero scalar constants. -/
theorem isRealRooted_of_C_lift_sequence
    {P Q : Nat → ℝ[X]} {c : Nat → ℝ}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hc : ∀ n : Nat, c n ≠ 0)
    (hrow : ∀ n : Nat, P n = C (c n) * Q n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_lift_sequence hquot (isRealRooted_C_sequence hc) hrow

/-- Right-factor variant of `isRealRooted_of_C_lift_sequence`. -/
theorem isRealRooted_of_C_lift_right_sequence
    {P Q : Nat → ℝ[X]} {c : Nat → ℝ}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hc : ∀ n : Nat, c n ≠ 0)
    (hrow : ∀ n : Nat, P n = Q n * C (c n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_lift_right_sequence hquot
    (isRealRooted_C_sequence hc) hrow

/-- Lift through row-wise nonzero-slope real linear factors. -/
theorem isRealRooted_of_C_mul_X_add_C_lift_sequence
    {P Q : Nat → ℝ[X]} {s t : Nat → ℝ}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hs : ∀ n : Nat, s n ≠ 0)
    (hrow : ∀ n : Nat, P n = (C (s n) * X + C (t n)) * Q n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_lift_sequence hquot
    (isRealRooted_C_mul_X_add_C_sequence hs) hrow

/-- Right-factor variant of `isRealRooted_of_C_mul_X_add_C_lift_sequence`. -/
theorem isRealRooted_of_C_mul_X_add_C_lift_right_sequence
    {P Q : Nat → ℝ[X]} {s t : Nat → ℝ}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hs : ∀ n : Nat, s n ≠ 0)
    (hrow : ∀ n : Nat, P n = Q n * (C (s n) * X + C (t n))) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_lift_right_sequence hquot
    (isRealRooted_C_mul_X_add_C_sequence hs) hrow

/-- Constant-first spelling of `isRealRooted_of_C_mul_X_add_C_lift_sequence`. -/
theorem isRealRooted_of_C_add_C_mul_X_lift_sequence
    {P Q : Nat → ℝ[X]} {s t : Nat → ℝ}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hs : ∀ n : Nat, s n ≠ 0)
    (hrow : ∀ n : Nat, P n = (C (t n) + C (s n) * X) * Q n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_lift_sequence hquot
    (isRealRooted_C_add_C_mul_X_one_sequence hs) hrow

/-- Right-factor variant of `isRealRooted_of_C_add_C_mul_X_lift_sequence`. -/
theorem isRealRooted_of_C_add_C_mul_X_lift_right_sequence
    {P Q : Nat → ℝ[X]} {s t : Nat → ℝ}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hs : ∀ n : Nat, s n ≠ 0)
    (hrow : ∀ n : Nat, P n = Q n * (C (t n) + C (s n) * X)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_lift_right_sequence hquot
    (isRealRooted_C_add_C_mul_X_one_sequence hs) hrow

/-- Powers of the root-at-zero factor are real-rooted. -/
theorem isRealRooted_X_pow (n : Nat) :
    ((X : ℝ[X]) ^ n ≠ 0 ∧ (((X : ℝ[X]) ^ n).Splits)) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [pow_succ]
      exact isRealRooted_mul ih.1 ih.2 isRealRooted_X.1 isRealRooted_X.2

/-- Powers of a nonzero scalar constant are real-rooted. -/
theorem isRealRooted_C_pow {a : ℝ} (ha : a ≠ 0) (n : Nat) :
    ((C a : ℝ[X]) ^ n ≠ 0 ∧ (((C a : ℝ[X]) ^ n).Splits)) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [pow_succ]
      exact isRealRooted_mul ih.1 ih.2 (isRealRooted_C ha).1 (isRealRooted_C ha).2

private theorem isRealRooted_C_pow_sequence {c : Nat → ℝ}
    (hc : ∀ n : Nat, c n ≠ 0) (m : Nat → Nat) :
    ∀ n : Nat, (C (c n) : ℝ[X]) ^ (m n) ≠ 0 ∧
      ((C (c n) : ℝ[X]) ^ (m n)).Splits :=
  fun n => isRealRooted_C_pow (hc n) (m n)

private theorem isRealRooted_X_pow_sequence (m : Nat → Nat) :
    ∀ n : Nat, (X : ℝ[X]) ^ (m n) ≠ 0 ∧ ((X : ℝ[X]) ^ (m n)).Splits :=
  fun n => isRealRooted_X_pow (m n)

/-- Lift through row-wise powers of nonzero scalar constants. -/
theorem isRealRooted_of_C_pow_lift_sequence
    {P Q : Nat → ℝ[X]} {c : Nat → ℝ} {m : Nat → Nat}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hc : ∀ n : Nat, c n ≠ 0)
    (hrow : ∀ n : Nat, P n = (C (c n) : ℝ[X]) ^ (m n) * Q n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_lift_sequence hquot
    (isRealRooted_C_pow_sequence hc m) hrow

/-- Right-factor variant of `isRealRooted_of_C_pow_lift_sequence`. -/
theorem isRealRooted_of_C_pow_lift_right_sequence
    {P Q : Nat → ℝ[X]} {c : Nat → ℝ} {m : Nat → Nat}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hc : ∀ n : Nat, c n ≠ 0)
    (hrow : ∀ n : Nat, P n = Q n * (C (c n) : ℝ[X]) ^ (m n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_lift_right_sequence hquot
    (isRealRooted_C_pow_sequence hc m) hrow

/-- Lift through row-wise powers of `X`. -/
theorem isRealRooted_of_X_pow_lift_sequence
    {P Q : Nat → ℝ[X]} {m : Nat → Nat}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, P n = X ^ (m n) * Q n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_lift_sequence hquot
    (isRealRooted_X_pow_sequence m) hrow

/-- Right-factor variant of `isRealRooted_of_X_pow_lift_sequence`. -/
theorem isRealRooted_of_X_pow_lift_right_sequence
    {P Q : Nat → ℝ[X]} {m : Nat → Nat}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, P n = Q n * X ^ (m n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_lift_right_sequence hquot
    (isRealRooted_X_pow_sequence m) hrow

/-- Lift through row-wise powers of a fixed unit-slope real linear factor. -/
theorem isRealRooted_of_X_add_C_pow_lift_sequence
    {P Q : Nat → ℝ[X]} {t : ℝ} {m : Nat → Nat}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, P n = (X + C t) ^ (m n) * Q n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_lift_sequence hquot
    (isRealRooted_fixed_X_add_C_pow_sequence t m) hrow

/-- Right-factor variant of `isRealRooted_of_X_add_C_pow_lift_sequence`. -/
theorem isRealRooted_of_X_add_C_pow_lift_right_sequence
    {P Q : Nat → ℝ[X]} {t : ℝ} {m : Nat → Nat}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, P n = Q n * (X + C t) ^ (m n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_lift_right_sequence hquot
    (isRealRooted_fixed_X_add_C_pow_sequence t m) hrow

/-- Lift through row-wise powers of unit-slope real linear factors. -/
theorem isRealRooted_of_X_add_C_row_pow_lift_sequence
    {P Q : Nat → ℝ[X]} {t : Nat → ℝ} {m : Nat → Nat}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, P n = (X + C (t n)) ^ (m n) * Q n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_lift_sequence hquot
    (isRealRooted_X_add_C_pow_sequence t m) hrow

/-- Right-factor variant of `isRealRooted_of_X_add_C_row_pow_lift_sequence`. -/
theorem isRealRooted_of_X_add_C_row_pow_lift_right_sequence
    {P Q : Nat → ℝ[X]} {t : Nat → ℝ} {m : Nat → Nat}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, P n = Q n * (X + C (t n)) ^ (m n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_lift_right_sequence hquot
    (isRealRooted_X_add_C_pow_sequence t m) hrow

/-- Constant-first spelling of
`isRealRooted_of_X_add_C_row_pow_lift_sequence`. -/
theorem isRealRooted_of_C_add_X_pow_lift_sequence
    {P Q : Nat → ℝ[X]} {t : Nat → ℝ} {m : Nat → Nat}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, P n = (C (t n) + X) ^ (m n) * Q n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_lift_sequence hquot
    (isRealRooted_C_add_X_pow_sequence t m) hrow

/-- Right-factor variant of `isRealRooted_of_C_add_X_pow_lift_sequence`. -/
theorem isRealRooted_of_C_add_X_pow_lift_right_sequence
    {P Q : Nat → ℝ[X]} {t : Nat → ℝ} {m : Nat → Nat}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, P n = Q n * (C (t n) + X) ^ (m n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_lift_right_sequence hquot
    (isRealRooted_C_add_X_pow_sequence t m) hrow

/-- Lift through row-wise powers of a nonzero-slope real linear factor. -/
theorem isRealRooted_of_C_mul_X_add_C_pow_lift_sequence
    {P Q : Nat → ℝ[X]} {s t : Nat → ℝ} {m : Nat → Nat}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hs : ∀ n : Nat, s n ≠ 0)
    (hrow : ∀ n : Nat, P n = (C (s n) * X + C (t n)) ^ (m n) * Q n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_lift_sequence hquot
    (isRealRooted_C_mul_X_add_C_pow_sequence hs m) hrow

/-- Right-factor variant of `isRealRooted_of_C_mul_X_add_C_pow_lift_sequence`. -/
theorem isRealRooted_of_C_mul_X_add_C_pow_lift_right_sequence
    {P Q : Nat → ℝ[X]} {s t : Nat → ℝ} {m : Nat → Nat}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hs : ∀ n : Nat, s n ≠ 0)
    (hrow : ∀ n : Nat, P n = Q n * (C (s n) * X + C (t n)) ^ (m n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_lift_right_sequence hquot
    (isRealRooted_C_mul_X_add_C_pow_sequence hs m) hrow

/-- Constant-first spelling of
`isRealRooted_of_C_mul_X_add_C_pow_lift_sequence`. -/
theorem isRealRooted_of_C_add_C_mul_X_pow_lift_sequence
    {P Q : Nat → ℝ[X]} {s t : Nat → ℝ} {m : Nat → Nat}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hs : ∀ n : Nat, s n ≠ 0)
    (hrow : ∀ n : Nat, P n = (C (t n) + C (s n) * X) ^ (m n) * Q n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_lift_sequence hquot
    (isRealRooted_C_add_C_mul_X_pow_sequence hs m) hrow

/-- Right-factor variant of `isRealRooted_of_C_add_C_mul_X_pow_lift_sequence`. -/
theorem isRealRooted_of_C_add_C_mul_X_pow_lift_right_sequence
    {P Q : Nat → ℝ[X]} {s t : Nat → ℝ} {m : Nat → Nat}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hs : ∀ n : Nat, s n ≠ 0)
    (hrow : ∀ n : Nat, P n = Q n * (C (t n) + C (s n) * X) ^ (m n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_lift_right_sequence hquot
    (isRealRooted_C_add_C_mul_X_pow_sequence hs m) hrow

/-- Parity lift for product-form rows whose odd rows are a nonzero scalar
times `X` times the corresponding even quotient row.

This is the final bookkeeping step for product exits such as A137477 after the
even quotient sequence has been proved real-rooted by a product-factor shell. -/
theorem isRealRooted_of_even_product_odd_X_scalar_sequence
    {P Q : Nat → ℝ[X]} {a : Nat → ℝ}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (ha : ∀ n : Nat, a n ≠ 0)
    (heven : ∀ n : Nat, P (2 * n) = Q n)
    (hodd : ∀ n : Nat, P (2 * n + 1) = C (a n) * X * Q n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  have heven_realrooted : ∀ n : Nat, P (2 * n) ≠ 0 ∧ (P (2 * n)).Splits := by
    intro n
    simpa [heven n] using hquot n
  have hodd_realrooted :
      ∀ n : Nat, P (2 * n + 1) ≠ 0 ∧ (P (2 * n + 1)).Splits := by
    intro n
    have hfactor : C (a n) * X ≠ 0 ∧ (C (a n) * X).Splits :=
      isRealRooted_C_mul isRealRooted_X.1 isRealRooted_X.2 (ha n)
    have hrow : (C (a n) * X) * Q n ≠ 0 ∧ ((C (a n) * X) * Q n).Splits :=
      isRealRooted_mul hfactor.1 hfactor.2 (hquot n).1 (hquot n).2
    simpa [hodd n, mul_assoc] using hrow
  intro n
  rcases Nat.mod_two_eq_zero_or_one n with hmod | hmod
  · have hn : n = 2 * (n / 2) := by
      simpa [hmod] using (Nat.div_add_mod n 2).symm
    rw [hn]
    exact heven_realrooted (n / 2)
  · have hn : n = 2 * (n / 2) + 1 := by
      simpa [hmod] using (Nat.div_add_mod n 2).symm
    rw [hn]
    exact hodd_realrooted (n / 2)

/-- One endpoint-quotient transition: first form `a+b`, then the next row is
`b+X(a+b)`. -/
theorem prec_endpoint_sum_then_X_step {a b : ℝ[X]}
    (hab : Prec a b)
    (ha_nonneg : HasNonnegCoeffs a) (hb_nonneg : HasNonnegCoeffs b)
    (hcop : IsCoprime b (X * (a + b))) :
    Prec (a + b) (b + X * (a + b)) := by
  have ha_pos : HasPosLeadingCoeff a :=
    ha_nonneg.pos_leadingCoeff (left_ne_zero_of_prec hab)
  have hb_pos : HasPosLeadingCoeff b :=
    hb_nonneg.pos_leadingCoeff (right_ne_zero_of_prec hab)
  have hsum_prec_raw : Prec (C (1 : ℝ) * a + C (1 : ℝ) * b) b :=
    prec_nonneg_combo_right hab ha_pos hb_pos zero_le_one zero_le_one (Or.inl zero_lt_one)
  have hsum_prec : Prec (a + b) b := by
    simpa using hsum_prec_raw
  have hsum_nonneg : HasNonnegCoeffs (a + b) :=
    ha_nonneg.add hb_nonneg
  have hsum_pos : HasPosLeadingCoeff (a + b) :=
    hsum_nonneg.pos_leadingCoeff (left_ne_zero_of_prec hsum_prec)
  have hXsum_prec : Prec (a + b) (X * (a + b)) :=
    prec_mul_X_of_prec_of_nonneg
      (prec_refl (left_ne_zero_of_prec hsum_prec) (left_splits_of_prec hsum_prec))
      hsum_nonneg hsum_nonneg
  have hXsum_pos : HasPosLeadingCoeff (X * (a + b)) :=
    hsum_pos.X_mul
  have hcombo : PosComboRealRooted b (X * (a + b)) :=
    PosComboRealRooted.of_commonLeftInterleaver
      hsum_prec hXsum_prec hb_pos hXsum_pos
  have hrr : b + X * (a + b) ≠ 0 ∧ (b + X * (a + b)).Splits :=
    PosComboRealRooted.isRealRooted_add hcombo
  exact
    prec_add_of_prec_left
      hsum_prec hXsum_prec hb_pos hXsum_pos hrr.1 hrr.2 hcop

/-- One endpoint-quotient transition with the parity reversed: first form
`b+Xa`, then the next row is `a+(b+Xa)`. -/
theorem prec_endpoint_X_then_sum_step {a b : ℝ[X]}
    (hab : Prec a b)
    (ha_nonneg : HasNonnegCoeffs a) (hb_nonneg : HasNonnegCoeffs b)
    (hcop : IsCoprime b (X * a)) :
    Prec (a + (b + X * a)) (b + X * a) := by
  have ha_pos : HasPosLeadingCoeff a :=
    ha_nonneg.pos_leadingCoeff (left_ne_zero_of_prec hab)
  have hb_pos : HasPosLeadingCoeff b :=
    hb_nonneg.pos_leadingCoeff (right_ne_zero_of_prec hab)
  have hXa_prec : Prec a (X * a) :=
    prec_mul_X_of_prec_of_nonneg
      (prec_refl (left_ne_zero_of_prec hab) (left_splits_of_prec hab))
      ha_nonneg ha_nonneg
  have hXa_pos : HasPosLeadingCoeff (X * a) :=
    ha_pos.X_mul
  have hcombo : PosComboRealRooted b (X * a) :=
    PosComboRealRooted.of_commonLeftInterleaver hab hXa_prec hb_pos hXa_pos
  have hrr : b + X * a ≠ 0 ∧ (b + X * a).Splits :=
    PosComboRealRooted.isRealRooted_add hcombo
  have ha_sum_prec : Prec a (b + X * a) :=
    prec_add_of_prec_left hab hXa_prec hb_pos hXa_pos hrr.1 hrr.2 hcop
  have hsum_nonneg : HasNonnegCoeffs (b + X * a) :=
    hb_nonneg.add ha_nonneg.X_mul
  have hsum_pos : HasPosLeadingCoeff (b + X * a) :=
    hsum_nonneg.pos_leadingCoeff (right_ne_zero_of_prec ha_sum_prec)
  have hnext_raw :
      Prec (C (1 : ℝ) * a + C (1 : ℝ) * (b + X * a)) (b + X * a) :=
    prec_nonneg_combo_right ha_sum_prec ha_pos hsum_pos
      zero_le_one zero_le_one (Or.inl zero_lt_one)
  simpa [add_assoc] using hnext_raw

/-- Pair-sequence endpoint quotient shell.

This is the quotient recurrence after removing endpoint powers when the
transition first forms `A_{n+1}=A_n+B_n` and then
`B_{n+1}=B_n+X A_{n+1}`. -/
theorem prec_endpoint_sum_then_X_pair_sequence
    {A B : Nat → ℝ[X]}
    (hbase : Prec (A 0) (B 0))
    (hA0_nonneg : HasNonnegCoeffs (A 0))
    (hB0_nonneg : HasNonnegCoeffs (B 0))
    (hstepA : ∀ n : Nat, A (n + 1) = A n + B n)
    (hstepB : ∀ n : Nat, B (n + 1) = B n + X * A (n + 1))
    (hcop : ∀ n : Nat, IsCoprime (B n) (X * A (n + 1))) :
    ∀ n : Nat, Prec (A n) (B n) := by
  have hpack :
      ∀ n : Nat,
        Prec (A n) (B n) ∧ HasNonnegCoeffs (A n) ∧ HasNonnegCoeffs (B n) := by
    intro n
    induction n with
    | zero =>
        exact ⟨hbase, hA0_nonneg, hB0_nonneg⟩
    | succ n ih =>
        rcases ih with ⟨hprec, hA_nonneg, hB_nonneg⟩
        have hcop' : IsCoprime (B n) (X * (A n + B n)) := by
          simpa [hstepA n] using hcop n
        have hprec_next :
            Prec (A (n + 1)) (B (n + 1)) := by
          simpa [hstepA n, hstepB n] using
            prec_endpoint_sum_then_X_step hprec hA_nonneg hB_nonneg hcop'
        have hA_nonneg_next : HasNonnegCoeffs (A (n + 1)) := by
          simpa [hstepA n] using hA_nonneg.add hB_nonneg
        have hB_nonneg_next : HasNonnegCoeffs (B (n + 1)) := by
          simpa [hstepB n] using hB_nonneg.add hA_nonneg_next.X_mul
        exact ⟨hprec_next, hA_nonneg_next, hB_nonneg_next⟩
  exact fun n => (hpack n).1

/-- Real-rootedness corollary for
`prec_endpoint_sum_then_X_pair_sequence`. -/
theorem isRealRooted_of_endpoint_sum_then_X_pair_sequence
    {A B : Nat → ℝ[X]}
    (hbase : Prec (A 0) (B 0))
    (hA0_nonneg : HasNonnegCoeffs (A 0))
    (hB0_nonneg : HasNonnegCoeffs (B 0))
    (hstepA : ∀ n : Nat, A (n + 1) = A n + B n)
    (hstepB : ∀ n : Nat, B (n + 1) = B n + X * A (n + 1))
    (hcop : ∀ n : Nat, IsCoprime (B n) (X * A (n + 1))) :
    ∀ n : Nat, (A n ≠ 0 ∧ (A n).Splits) ∧ (B n ≠ 0 ∧ (B n).Splits) := by
  intro n
  have hprec :=
    prec_endpoint_sum_then_X_pair_sequence
      hbase hA0_nonneg hB0_nonneg hstepA hstepB hcop n
  exact ⟨hprec.1, hprec.2.1⟩

/-- Pair-sequence endpoint quotient shell with the parity reversed.

Here the transition first forms `B_{n+1}=B_n+X A_n` and then
`A_{n+1}=A_n+B_{n+1}`. -/
theorem prec_endpoint_X_then_sum_pair_sequence
    {A B : Nat → ℝ[X]}
    (hbase : Prec (A 0) (B 0))
    (hA0_nonneg : HasNonnegCoeffs (A 0))
    (hB0_nonneg : HasNonnegCoeffs (B 0))
    (hstepB : ∀ n : Nat, B (n + 1) = B n + X * A n)
    (hstepA : ∀ n : Nat, A (n + 1) = A n + B (n + 1))
    (hcop : ∀ n : Nat, IsCoprime (B n) (X * A n)) :
    ∀ n : Nat, Prec (A n) (B n) := by
  have hpack :
      ∀ n : Nat,
        Prec (A n) (B n) ∧ HasNonnegCoeffs (A n) ∧ HasNonnegCoeffs (B n) := by
    intro n
    induction n with
    | zero =>
        exact ⟨hbase, hA0_nonneg, hB0_nonneg⟩
    | succ n ih =>
        rcases ih with ⟨hprec, hA_nonneg, hB_nonneg⟩
        have hprec_next :
            Prec (A (n + 1)) (B (n + 1)) := by
          simpa [hstepB n, hstepA n] using
            prec_endpoint_X_then_sum_step hprec hA_nonneg hB_nonneg (hcop n)
        have hB_nonneg_next : HasNonnegCoeffs (B (n + 1)) := by
          simpa [hstepB n] using hB_nonneg.add hA_nonneg.X_mul
        have hA_nonneg_next : HasNonnegCoeffs (A (n + 1)) := by
          simpa [hstepA n] using hA_nonneg.add hB_nonneg_next
        exact ⟨hprec_next, hA_nonneg_next, hB_nonneg_next⟩
  exact fun n => (hpack n).1

/-- Real-rootedness corollary for
`prec_endpoint_X_then_sum_pair_sequence`. -/
theorem isRealRooted_of_endpoint_X_then_sum_pair_sequence
    {A B : Nat → ℝ[X]}
    (hbase : Prec (A 0) (B 0))
    (hA0_nonneg : HasNonnegCoeffs (A 0))
    (hB0_nonneg : HasNonnegCoeffs (B 0))
    (hstepB : ∀ n : Nat, B (n + 1) = B n + X * A n)
    (hstepA : ∀ n : Nat, A (n + 1) = A n + B (n + 1))
    (hcop : ∀ n : Nat, IsCoprime (B n) (X * A n)) :
    ∀ n : Nat, (A n ≠ 0 ∧ (A n).Splits) ∧ (B n ≠ 0 ∧ (B n).Splits) := by
  intro n
  have hprec :=
    prec_endpoint_X_then_sum_pair_sequence
      hbase hA0_nonneg hB0_nonneg hstepB hstepA hcop n
  exact ⟨hprec.1, hprec.2.1⟩

/-- Endpoint quotient plus endpoint-power lift for a single row sequence.

The even rows are endpoint powers times `A_n`, while the odd rows are endpoint
powers times `B_n`.  The quotient pair uses the sum-then-`X` parity. -/
theorem isRealRooted_of_endpoint_sum_then_X_pair_lift_sequence
    {P A B : Nat → ℝ[X]} {t : ℝ} {mA mB : Nat → Nat}
    (hbase : Prec (A 0) (B 0))
    (hA0_nonneg : HasNonnegCoeffs (A 0))
    (hB0_nonneg : HasNonnegCoeffs (B 0))
    (hstepA : ∀ n : Nat, A (n + 1) = A n + B n)
    (hstepB : ∀ n : Nat, B (n + 1) = B n + X * A (n + 1))
    (hcop : ∀ n : Nat, IsCoprime (B n) (X * A (n + 1)))
    (hrowA : ∀ n : Nat, P (2 * n) = (X + C t) ^ (mA n) * A n)
    (hrowB : ∀ n : Nat, P (2 * n + 1) = (X + C t) ^ (mB n) * B n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  have hquot :
      ∀ n : Nat, (A n ≠ 0 ∧ (A n).Splits) ∧ (B n ≠ 0 ∧ (B n).Splits) :=
    isRealRooted_of_endpoint_sum_then_X_pair_sequence
      hbase hA0_nonneg hB0_nonneg hstepA hstepB hcop
  have heven : ∀ n : Nat, P (2 * n) ≠ 0 ∧ (P (2 * n)).Splits := by
    intro n
    have hfactor : (X + C t) ^ (mA n) ≠ 0 ∧ ((X + C t) ^ (mA n)).Splits :=
      isRealRooted_X_add_C_pow t (mA n)
    have hrow :
        (X + C t) ^ (mA n) * A n ≠ 0 ∧
          ((X + C t) ^ (mA n) * A n).Splits :=
      isRealRooted_mul hfactor.1 hfactor.2
        (left_ne_zero_of_isRealRooted_pair_sequence hquot n)
        (left_splits_of_isRealRooted_pair_sequence hquot n)
    simpa [hrowA n] using hrow
  have hodd : ∀ n : Nat, P (2 * n + 1) ≠ 0 ∧ (P (2 * n + 1)).Splits := by
    intro n
    have hfactor : (X + C t) ^ (mB n) ≠ 0 ∧ ((X + C t) ^ (mB n)).Splits :=
      isRealRooted_X_add_C_pow t (mB n)
    have hrow :
        (X + C t) ^ (mB n) * B n ≠ 0 ∧
          ((X + C t) ^ (mB n) * B n).Splits :=
      isRealRooted_mul hfactor.1 hfactor.2
        (right_ne_zero_of_isRealRooted_pair_sequence hquot n)
        (right_splits_of_isRealRooted_pair_sequence hquot n)
    simpa [hrowB n] using hrow
  intro n
  rcases Nat.mod_two_eq_zero_or_one n with hmod | hmod
  · have hn : n = 2 * (n / 2) := by
      simpa [hmod] using (Nat.div_add_mod n 2).symm
    rw [hn]
    exact heven (n / 2)
  · have hn : n = 2 * (n / 2) + 1 := by
      simpa [hmod] using (Nat.div_add_mod n 2).symm
    rw [hn]
    exact hodd (n / 2)

/-- Endpoint quotient plus endpoint-power lift for the reversed quotient
parity. -/
theorem isRealRooted_of_endpoint_X_then_sum_pair_lift_sequence
    {P A B : Nat → ℝ[X]} {t : ℝ} {mA mB : Nat → Nat}
    (hbase : Prec (A 0) (B 0))
    (hA0_nonneg : HasNonnegCoeffs (A 0))
    (hB0_nonneg : HasNonnegCoeffs (B 0))
    (hstepB : ∀ n : Nat, B (n + 1) = B n + X * A n)
    (hstepA : ∀ n : Nat, A (n + 1) = A n + B (n + 1))
    (hcop : ∀ n : Nat, IsCoprime (B n) (X * A n))
    (hrowA : ∀ n : Nat, P (2 * n) = (X + C t) ^ (mA n) * A n)
    (hrowB : ∀ n : Nat, P (2 * n + 1) = (X + C t) ^ (mB n) * B n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  have hquot :
      ∀ n : Nat, (A n ≠ 0 ∧ (A n).Splits) ∧ (B n ≠ 0 ∧ (B n).Splits) :=
    isRealRooted_of_endpoint_X_then_sum_pair_sequence
      hbase hA0_nonneg hB0_nonneg hstepB hstepA hcop
  have heven : ∀ n : Nat, P (2 * n) ≠ 0 ∧ (P (2 * n)).Splits := by
    intro n
    have hfactor : (X + C t) ^ (mA n) ≠ 0 ∧ ((X + C t) ^ (mA n)).Splits :=
      isRealRooted_X_add_C_pow t (mA n)
    have hrow :
        (X + C t) ^ (mA n) * A n ≠ 0 ∧
          ((X + C t) ^ (mA n) * A n).Splits :=
      isRealRooted_mul hfactor.1 hfactor.2
        (left_ne_zero_of_isRealRooted_pair_sequence hquot n)
        (left_splits_of_isRealRooted_pair_sequence hquot n)
    simpa [hrowA n] using hrow
  have hodd : ∀ n : Nat, P (2 * n + 1) ≠ 0 ∧ (P (2 * n + 1)).Splits := by
    intro n
    have hfactor : (X + C t) ^ (mB n) ≠ 0 ∧ ((X + C t) ^ (mB n)).Splits :=
      isRealRooted_X_add_C_pow t (mB n)
    have hrow :
        (X + C t) ^ (mB n) * B n ≠ 0 ∧
          ((X + C t) ^ (mB n) * B n).Splits :=
      isRealRooted_mul hfactor.1 hfactor.2
        (right_ne_zero_of_isRealRooted_pair_sequence hquot n)
        (right_splits_of_isRealRooted_pair_sequence hquot n)
    simpa [hrowB n] using hrow
  intro n
  rcases Nat.mod_two_eq_zero_or_one n with hmod | hmod
  · have hn : n = 2 * (n / 2) := by
      simpa [hmod] using (Nat.div_add_mod n 2).symm
    rw [hn]
    exact heven (n / 2)
  · have hn : n = 2 * (n / 2) + 1 := by
      simpa [hmod] using (Nat.div_add_mod n 2).symm
    rw [hn]
    exact hodd (n / 2)

/-- Endpoint quotient plus endpoint-power lift for the reversed quotient
parity, with the single row sequence using the opposite even/odd assignment.

This is the shape for endpoint recurrences where the quotient pair satisfies
`B_{n+1}=B_n+X A_n`, `A_{n+1}=A_n+B_{n+1}`, but the original even rows are
endpoint powers times `B_n` and the original odd rows are endpoint powers
times `A_n`. -/
theorem isRealRooted_of_endpoint_X_then_sum_pair_lift_swapped_sequence
    {P A B : Nat → ℝ[X]} {t : ℝ} {mA mB : Nat → Nat}
    (hbase : Prec (A 0) (B 0))
    (hA0_nonneg : HasNonnegCoeffs (A 0))
    (hB0_nonneg : HasNonnegCoeffs (B 0))
    (hstepB : ∀ n : Nat, B (n + 1) = B n + X * A n)
    (hstepA : ∀ n : Nat, A (n + 1) = A n + B (n + 1))
    (hcop : ∀ n : Nat, IsCoprime (B n) (X * A n))
    (hrowB : ∀ n : Nat, P (2 * n) = (X + C t) ^ (mB n) * B n)
    (hrowA : ∀ n : Nat, P (2 * n + 1) = (X + C t) ^ (mA n) * A n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  have hquot :
      ∀ n : Nat, (A n ≠ 0 ∧ (A n).Splits) ∧ (B n ≠ 0 ∧ (B n).Splits) :=
    isRealRooted_of_endpoint_X_then_sum_pair_sequence
      hbase hA0_nonneg hB0_nonneg hstepB hstepA hcop
  have heven : ∀ n : Nat, P (2 * n) ≠ 0 ∧ (P (2 * n)).Splits := by
    intro n
    have hfactor : (X + C t) ^ (mB n) ≠ 0 ∧ ((X + C t) ^ (mB n)).Splits :=
      isRealRooted_X_add_C_pow t (mB n)
    have hrow :
        (X + C t) ^ (mB n) * B n ≠ 0 ∧
          ((X + C t) ^ (mB n) * B n).Splits :=
      isRealRooted_mul hfactor.1 hfactor.2
        (right_ne_zero_of_isRealRooted_pair_sequence hquot n)
        (right_splits_of_isRealRooted_pair_sequence hquot n)
    simpa [hrowB n] using hrow
  have hodd : ∀ n : Nat, P (2 * n + 1) ≠ 0 ∧ (P (2 * n + 1)).Splits := by
    intro n
    have hfactor : (X + C t) ^ (mA n) ≠ 0 ∧ ((X + C t) ^ (mA n)).Splits :=
      isRealRooted_X_add_C_pow t (mA n)
    have hrow :
        (X + C t) ^ (mA n) * A n ≠ 0 ∧
          ((X + C t) ^ (mA n) * A n).Splits :=
      isRealRooted_mul hfactor.1 hfactor.2
        (left_ne_zero_of_isRealRooted_pair_sequence hquot n)
        (left_splits_of_isRealRooted_pair_sequence hquot n)
    simpa [hrowA n] using hrow
  intro n
  rcases Nat.mod_two_eq_zero_or_one n with hmod | hmod
  · have hn : n = 2 * (n / 2) := by
      simpa [hmod] using (Nat.div_add_mod n 2).symm
    rw [hn]
    exact heven (n / 2)
  · have hn : n = 2 * (n / 2) + 1 := by
      simpa [hmod] using (Nat.div_add_mod n 2).symm
    rw [hn]
    exact hodd (n / 2)

/-- Sequence shell for first-order affine-product recurrences. -/
theorem isRealRooted_of_product_affine_sequence
    {P : Nat → ℝ[X]} {s t : Nat → ℝ}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hs : ∀ n : Nat, s n ≠ 0)
    (hstep : ∀ n : Nat, P (n + 1) = (C (s n) * X + C (t n)) * P n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  intro n
  induction n with
  | zero =>
      simpa using hbase
  | succ n ih =>
      have hnext :
          ((C (s n) * X + C (t n)) * P n ≠ 0 ∧
            ((C (s n) * X + C (t n)) * P n).Splits) :=
        isRealRooted_C_mul_X_add_C_mul ih (hs n)
      simpa [Nat.succ_eq_add_one, hstep n] using hnext

/-- Right-factor variant of `isRealRooted_of_product_affine_sequence`. -/
theorem isRealRooted_of_product_affine_right_sequence
    {P : Nat → ℝ[X]} {s t : Nat → ℝ}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hs : ∀ n : Nat, s n ≠ 0)
    (hstep : ∀ n : Nat, P (n + 1) = P n * (C (s n) * X + C (t n))) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  intro n
  induction n with
  | zero =>
      simpa using hbase
  | succ n ih =>
      have hnext :
          (P n * (C (s n) * X + C (t n)) ≠ 0 ∧
            (P n * (C (s n) * X + C (t n))).Splits) :=
        isRealRooted_mul_C_mul_X_add_C ih (hs n)
      simpa [Nat.succ_eq_add_one, hstep n] using hnext

/-- Sequence shell for report-order affine factors `C t + C s * X`. -/
theorem isRealRooted_of_product_const_first_affine_sequence
    {P : Nat → ℝ[X]} {s t : Nat → ℝ}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hs : ∀ n : Nat, s n ≠ 0)
    (hstep : ∀ n : Nat, P (n + 1) = (C (t n) + C (s n) * X) * P n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  intro n
  induction n with
  | zero =>
      simpa using hbase
  | succ n ih =>
      have hnext :
          ((C (t n) + C (s n) * X) * P n ≠ 0 ∧
            ((C (t n) + C (s n) * X) * P n).Splits) :=
        isRealRooted_C_add_C_mul_X_mul ih (hs n)
      simpa [Nat.succ_eq_add_one, hstep n] using hnext

/-- Right-factor variant of `isRealRooted_of_product_const_first_affine_sequence`. -/
theorem isRealRooted_of_product_const_first_affine_right_sequence
    {P : Nat → ℝ[X]} {s t : Nat → ℝ}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hs : ∀ n : Nat, s n ≠ 0)
    (hstep : ∀ n : Nat, P (n + 1) = P n * (C (t n) + C (s n) * X)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  intro n
  induction n with
  | zero =>
      simpa using hbase
  | succ n ih =>
      have hnext :
          (P n * (C (t n) + C (s n) * X) ≠ 0 ∧
            (P n * (C (t n) + C (s n) * X)).Splits) :=
        isRealRooted_mul_C_add_C_mul_X ih (hs n)
      simpa [Nat.succ_eq_add_one, hstep n] using hnext

/-- Sequence shell for unit-slope factors `X + C t`. -/
theorem isRealRooted_of_product_X_add_C_sequence
    {P : Nat → ℝ[X]} {t : Nat → ℝ}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hstep : ∀ n : Nat, P (n + 1) = (X + C (t n)) * P n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  intro n
  induction n with
  | zero =>
      simpa using hbase
  | succ n ih =>
      have hnext :
          ((X + C (t n)) * P n ≠ 0 ∧ ((X + C (t n)) * P n).Splits) :=
        isRealRooted_X_add_C_mul ih
      simpa [Nat.succ_eq_add_one, hstep n] using hnext

/-- Right-factor variant of `isRealRooted_of_product_X_add_C_sequence`. -/
theorem isRealRooted_of_product_X_add_C_right_sequence
    {P : Nat → ℝ[X]} {t : Nat → ℝ}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hstep : ∀ n : Nat, P (n + 1) = P n * (X + C (t n))) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  intro n
  induction n with
  | zero =>
      simpa using hbase
  | succ n ih =>
      have hnext :
          (P n * (X + C (t n)) ≠ 0 ∧ (P n * (X + C (t n))).Splits) :=
        isRealRooted_mul_X_add_C ih
      simpa [Nat.succ_eq_add_one, hstep n] using hnext

/-- Sequence shell for constant-first unit-slope factors `C t + X`. -/
theorem isRealRooted_of_product_C_add_X_sequence
    {P : Nat → ℝ[X]} {t : Nat → ℝ}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hstep : ∀ n : Nat, P (n + 1) = (C (t n) + X) * P n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_factor_sequence hbase
    (isRealRooted_C_add_X_one_sequence t) hstep

/-- Right-factor variant of `isRealRooted_of_product_C_add_X_sequence`. -/
theorem isRealRooted_of_product_C_add_X_right_sequence
    {P : Nat → ℝ[X]} {t : Nat → ℝ}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hstep : ∀ n : Nat, P (n + 1) = P n * (C (t n) + X)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_factor_right_sequence hbase
    (isRealRooted_C_add_X_one_sequence t) hstep

/-- Sequence shell for product recurrences with factors `X ^ m_n`. -/
theorem isRealRooted_of_product_X_pow_sequence
    {P : Nat → ℝ[X]} {m : Nat → Nat}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hstep : ∀ n : Nat, P (n + 1) = X ^ (m n) * P n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_factor_sequence hbase
    (isRealRooted_X_pow_sequence m) hstep

/-- Right-factor variant of `isRealRooted_of_product_X_pow_sequence`. -/
theorem isRealRooted_of_product_X_pow_right_sequence
    {P : Nat → ℝ[X]} {m : Nat → Nat}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hstep : ∀ n : Nat, P (n + 1) = P n * X ^ (m n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_factor_right_sequence hbase
    (isRealRooted_X_pow_sequence m) hstep

/-- Sequence shell for product recurrences with nonzero scalar-power factors. -/
theorem isRealRooted_of_product_C_pow_sequence
    {P : Nat → ℝ[X]} {c : Nat → ℝ} {m : Nat → Nat}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hc : ∀ n : Nat, c n ≠ 0)
    (hstep : ∀ n : Nat, P (n + 1) = (C (c n) : ℝ[X]) ^ (m n) * P n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_factor_sequence hbase
    (isRealRooted_C_pow_sequence hc m) hstep

/-- Right-factor variant of `isRealRooted_of_product_C_pow_sequence`. -/
theorem isRealRooted_of_product_C_pow_right_sequence
    {P : Nat → ℝ[X]} {c : Nat → ℝ} {m : Nat → Nat}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hc : ∀ n : Nat, c n ≠ 0)
    (hstep : ∀ n : Nat, P (n + 1) = P n * (C (c n) : ℝ[X]) ^ (m n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_factor_right_sequence hbase
    (isRealRooted_C_pow_sequence hc m) hstep

/-- Sequence shell for product recurrences with factors `(X + C t_n) ^ m_n`. -/
theorem isRealRooted_of_product_X_add_C_pow_sequence
    {P : Nat → ℝ[X]} {t : Nat → ℝ} {m : Nat → Nat}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hstep : ∀ n : Nat, P (n + 1) = (X + C (t n)) ^ (m n) * P n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_factor_sequence hbase
    (isRealRooted_X_add_C_pow_sequence t m) hstep

/-- Right-factor variant of `isRealRooted_of_product_X_add_C_pow_sequence`. -/
theorem isRealRooted_of_product_X_add_C_pow_right_sequence
    {P : Nat → ℝ[X]} {t : Nat → ℝ} {m : Nat → Nat}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hstep : ∀ n : Nat, P (n + 1) = P n * (X + C (t n)) ^ (m n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_factor_right_sequence hbase
    (isRealRooted_X_add_C_pow_sequence t m) hstep

/-- Sequence shell for product recurrences with factors `(C t_n + X) ^ m_n`. -/
theorem isRealRooted_of_product_C_add_X_pow_sequence
    {P : Nat → ℝ[X]} {t : Nat → ℝ} {m : Nat → Nat}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hstep : ∀ n : Nat, P (n + 1) = (C (t n) + X) ^ (m n) * P n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_factor_sequence hbase
    (isRealRooted_C_add_X_pow_sequence t m) hstep

/-- Right-factor variant of `isRealRooted_of_product_C_add_X_pow_sequence`. -/
theorem isRealRooted_of_product_C_add_X_pow_right_sequence
    {P : Nat → ℝ[X]} {t : Nat → ℝ} {m : Nat → Nat}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hstep : ∀ n : Nat, P (n + 1) = P n * (C (t n) + X) ^ (m n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_factor_right_sequence hbase
    (isRealRooted_C_add_X_pow_sequence t m) hstep

/-- Sequence shell for product recurrences with powered affine factors. -/
theorem isRealRooted_of_product_C_mul_X_add_C_pow_sequence
    {P : Nat → ℝ[X]} {s t : Nat → ℝ} {m : Nat → Nat}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hs : ∀ n : Nat, s n ≠ 0)
    (hstep :
      ∀ n : Nat, P (n + 1) = (C (s n) * X + C (t n)) ^ (m n) * P n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_factor_sequence hbase
    (isRealRooted_C_mul_X_add_C_pow_sequence hs m) hstep

/-- Right-factor variant of
`isRealRooted_of_product_C_mul_X_add_C_pow_sequence`. -/
theorem isRealRooted_of_product_C_mul_X_add_C_pow_right_sequence
    {P : Nat → ℝ[X]} {s t : Nat → ℝ} {m : Nat → Nat}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hs : ∀ n : Nat, s n ≠ 0)
    (hstep :
      ∀ n : Nat, P (n + 1) = P n * (C (s n) * X + C (t n)) ^ (m n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_factor_right_sequence hbase
    (isRealRooted_C_mul_X_add_C_pow_sequence hs m) hstep

/-- Constant-first spelling of
`isRealRooted_of_product_C_mul_X_add_C_pow_sequence`. -/
theorem isRealRooted_of_product_C_add_C_mul_X_pow_sequence
    {P : Nat → ℝ[X]} {s t : Nat → ℝ} {m : Nat → Nat}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hs : ∀ n : Nat, s n ≠ 0)
    (hstep :
      ∀ n : Nat, P (n + 1) = (C (t n) + C (s n) * X) ^ (m n) * P n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_factor_sequence hbase
    (isRealRooted_C_add_C_mul_X_pow_sequence hs m) hstep

/-- Right-factor variant of
`isRealRooted_of_product_C_add_C_mul_X_pow_sequence`. -/
theorem isRealRooted_of_product_C_add_C_mul_X_pow_right_sequence
    {P : Nat → ℝ[X]} {s t : Nat → ℝ} {m : Nat → Nat}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hs : ∀ n : Nat, s n ≠ 0)
    (hstep :
      ∀ n : Nat, P (n + 1) = P n * (C (t n) + C (s n) * X) ^ (m n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_factor_right_sequence hbase
    (isRealRooted_C_add_C_mul_X_pow_sequence hs m) hstep

/-- Sequence shell for scalar product recurrences. -/
theorem isRealRooted_of_product_scalar_sequence
    {P : Nat → ℝ[X]} {a : Nat → ℝ}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (ha : ∀ n : Nat, a n ≠ 0)
    (hstep : ∀ n : Nat, P (n + 1) = C (a n) * P n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  intro n
  induction n with
  | zero =>
      simpa using hbase
  | succ n ih =>
      have hnext : C (a n) * P n ≠ 0 ∧ (C (a n) * P n).Splits :=
        isRealRooted_C_mul ih.1 ih.2 (ha n)
      simpa [Nat.succ_eq_add_one, hstep n] using hnext

/-- Right-factor variant of `isRealRooted_of_product_scalar_sequence`. -/
theorem isRealRooted_of_product_scalar_right_sequence
    {P : Nat → ℝ[X]} {a : Nat → ℝ}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (ha : ∀ n : Nat, a n ≠ 0)
    (hstep : ∀ n : Nat, P (n + 1) = P n * C (a n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_factor_right_sequence hbase
    (isRealRooted_C_sequence ha) hstep

/-- Sequence shell for degree-plateau scalar/product families with supplied factors.

This generalizes `isRealRooted_of_product_scalar_linear_sequence` by requiring
a real-rootedness certificate for the even-step factor instead of assuming it
has the form `X+C b_n`. -/
theorem isRealRooted_of_product_scalar_factor_sequence
    {P F : Nat → ℝ[X]} {a : Nat → ℝ}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (ha : ∀ n : Nat, a n ≠ 0)
    (hfactor : ∀ n : Nat, F n ≠ 0 ∧ (F n).Splits)
    (hscalar : ∀ n : Nat, P (2 * n + 1) = C (a n) * P (2 * n))
    (hstep : ∀ n : Nat, P (2 * n + 2) = F n * P (2 * n + 1)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  have heven : ∀ n : Nat, P (2 * n) ≠ 0 ∧ (P (2 * n)).Splits := by
    intro n
    induction n with
    | zero =>
        simpa using hbase
    | succ n ih =>
        have hodd : P (2 * n + 1) ≠ 0 ∧ (P (2 * n + 1)).Splits := by
          simpa [hscalar n] using isRealRooted_C_mul ih.1 ih.2 (ha n)
        have hnext :
            (F n * P (2 * n + 1) ≠ 0 ∧ (F n * P (2 * n + 1)).Splits) :=
          isRealRooted_mul (hfactor n).1 (hfactor n).2 hodd.1 hodd.2
        simpa [Nat.mul_succ, Nat.succ_eq_add_one, Nat.add_assoc] using
          (by simpa [hstep n] using hnext)
  have hodd : ∀ n : Nat, P (2 * n + 1) ≠ 0 ∧ (P (2 * n + 1)).Splits := by
    intro n
    simpa [hscalar n] using isRealRooted_C_mul (heven n).1 (heven n).2 (ha n)
  intro n
  rcases Nat.mod_two_eq_zero_or_one n with hmod | hmod
  · have hn : n = 2 * (n / 2) := by
      simpa [hmod] using (Nat.div_add_mod n 2).symm
    rw [hn]
    exact heven (n / 2)
  · have hn : n = 2 * (n / 2) + 1 := by
      simpa [hmod] using (Nat.div_add_mod n 2).symm
    rw [hn]
    exact hodd (n / 2)

/-- Right-factor variant of `isRealRooted_of_product_scalar_factor_sequence`. -/
theorem isRealRooted_of_product_scalar_factor_right_sequence
    {P F : Nat → ℝ[X]} {a : Nat → ℝ}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (ha : ∀ n : Nat, a n ≠ 0)
    (hfactor : ∀ n : Nat, F n ≠ 0 ∧ (F n).Splits)
    (hscalar : ∀ n : Nat, P (2 * n + 1) = C (a n) * P (2 * n))
    (hstep : ∀ n : Nat, P (2 * n + 2) = P (2 * n + 1) * F n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  exact isRealRooted_of_product_scalar_factor_sequence hbase ha hfactor hscalar
    (fun n => by rw [hstep n, mul_comm])

/-- Right-scalar variant of `isRealRooted_of_product_scalar_factor_sequence`. -/
theorem isRealRooted_of_product_scalar_factor_scalar_right_sequence
    {P F : Nat → ℝ[X]} {a : Nat → ℝ}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (ha : ∀ n : Nat, a n ≠ 0)
    (hfactor : ∀ n : Nat, F n ≠ 0 ∧ (F n).Splits)
    (hscalar : ∀ n : Nat, P (2 * n + 1) = P (2 * n) * C (a n))
    (hstep : ∀ n : Nat, P (2 * n + 2) = F n * P (2 * n + 1)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  exact isRealRooted_of_product_scalar_factor_sequence hbase ha hfactor
    (fun n => by rw [hscalar n, mul_comm]) hstep

/-- Right-scalar/right-factor variant of
`isRealRooted_of_product_scalar_factor_sequence`. -/
theorem isRealRooted_of_product_scalar_factor_scalar_right_factor_right_sequence
    {P F : Nat → ℝ[X]} {a : Nat → ℝ}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (ha : ∀ n : Nat, a n ≠ 0)
    (hfactor : ∀ n : Nat, F n ≠ 0 ∧ (F n).Splits)
    (hscalar : ∀ n : Nat, P (2 * n + 1) = P (2 * n) * C (a n))
    (hstep : ∀ n : Nat, P (2 * n + 2) = P (2 * n + 1) * F n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  exact isRealRooted_of_product_scalar_factor_right_sequence hbase ha hfactor
    (fun n => by rw [hscalar n, mul_comm]) hstep

/-- Sequence shell for degree-plateau product families.

This covers recurrences where odd steps only rescale the previous row, while
even steps multiply by a real linear factor.  The motivating OEIS example is
`A060523`, after replacing the fitted lag-2 recurrence by its product form:
`P_{2m+1}=a_m P_{2m}` and `P_{2m+2}=(X+b_m)P_{2m+1}`. -/
theorem isRealRooted_of_product_scalar_linear_sequence
    {P : Nat → ℝ[X]} {a b : Nat → ℝ}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (ha : ∀ n : Nat, a n ≠ 0)
    (hscalar : ∀ n : Nat, P (2 * n + 1) = C (a n) * P (2 * n))
    (hlinear : ∀ n : Nat, P (2 * n + 2) = (X + C (b n)) * P (2 * n + 1)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_scalar_factor_sequence hbase ha
    (isRealRooted_X_add_C_one_sequence b) hscalar hlinear

/-- Right-factor variant of `isRealRooted_of_product_scalar_linear_sequence`. -/
theorem isRealRooted_of_product_scalar_linear_right_sequence
    {P : Nat → ℝ[X]} {a b : Nat → ℝ}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (ha : ∀ n : Nat, a n ≠ 0)
    (hscalar : ∀ n : Nat, P (2 * n + 1) = C (a n) * P (2 * n))
    (hlinear : ∀ n : Nat, P (2 * n + 2) = P (2 * n + 1) * (X + C (b n))) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_scalar_factor_right_sequence hbase ha
    (isRealRooted_X_add_C_one_sequence b) hscalar hlinear

/-- Right-scalar variant of `isRealRooted_of_product_scalar_linear_sequence`. -/
theorem isRealRooted_of_product_scalar_linear_scalar_right_sequence
    {P : Nat → ℝ[X]} {a b : Nat → ℝ}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (ha : ∀ n : Nat, a n ≠ 0)
    (hscalar : ∀ n : Nat, P (2 * n + 1) = P (2 * n) * C (a n))
    (hlinear : ∀ n : Nat, P (2 * n + 2) = (X + C (b n)) * P (2 * n + 1)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_scalar_factor_scalar_right_sequence hbase ha
    (isRealRooted_X_add_C_one_sequence b) hscalar hlinear

/-- Right-scalar/right-factor variant of
`isRealRooted_of_product_scalar_linear_sequence`. -/
theorem isRealRooted_of_product_scalar_linear_scalar_right_linear_right_sequence
    {P : Nat → ℝ[X]} {a b : Nat → ℝ}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (ha : ∀ n : Nat, a n ≠ 0)
    (hscalar : ∀ n : Nat, P (2 * n + 1) = P (2 * n) * C (a n))
    (hlinear : ∀ n : Nat, P (2 * n + 2) = P (2 * n + 1) * (X + C (b n))) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_scalar_factor_scalar_right_factor_right_sequence hbase ha
    (isRealRooted_X_add_C_one_sequence b) hscalar hlinear

/-- Constant-first variant of
`isRealRooted_of_product_scalar_linear_sequence`. -/
theorem isRealRooted_of_product_scalar_C_add_X_sequence
    {P : Nat → ℝ[X]} {a b : Nat → ℝ}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (ha : ∀ n : Nat, a n ≠ 0)
    (hscalar : ∀ n : Nat, P (2 * n + 1) = C (a n) * P (2 * n))
    (hlinear : ∀ n : Nat, P (2 * n + 2) = (C (b n) + X) * P (2 * n + 1)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_scalar_factor_sequence hbase ha
    (isRealRooted_C_add_X_one_sequence b) hscalar hlinear

/-- Right-factor variant of
`isRealRooted_of_product_scalar_C_add_X_sequence`. -/
theorem isRealRooted_of_product_scalar_C_add_X_right_sequence
    {P : Nat → ℝ[X]} {a b : Nat → ℝ}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (ha : ∀ n : Nat, a n ≠ 0)
    (hscalar : ∀ n : Nat, P (2 * n + 1) = C (a n) * P (2 * n))
    (hlinear : ∀ n : Nat, P (2 * n + 2) = P (2 * n + 1) * (C (b n) + X)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_scalar_factor_right_sequence hbase ha
    (isRealRooted_C_add_X_one_sequence b) hscalar hlinear

/-- Right-scalar variant of
`isRealRooted_of_product_scalar_C_add_X_sequence`. -/
theorem isRealRooted_of_product_scalar_C_add_X_scalar_right_sequence
    {P : Nat → ℝ[X]} {a b : Nat → ℝ}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (ha : ∀ n : Nat, a n ≠ 0)
    (hscalar : ∀ n : Nat, P (2 * n + 1) = P (2 * n) * C (a n))
    (hlinear : ∀ n : Nat, P (2 * n + 2) = (C (b n) + X) * P (2 * n + 1)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_scalar_factor_scalar_right_sequence hbase ha
    (isRealRooted_C_add_X_one_sequence b) hscalar hlinear

/-- Right-scalar/right-factor variant of
`isRealRooted_of_product_scalar_C_add_X_sequence`. -/
theorem isRealRooted_of_product_scalar_C_add_X_scalar_right_linear_right_sequence
    {P : Nat → ℝ[X]} {a b : Nat → ℝ}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (ha : ∀ n : Nat, a n ≠ 0)
    (hscalar : ∀ n : Nat, P (2 * n + 1) = P (2 * n) * C (a n))
    (hlinear : ∀ n : Nat, P (2 * n + 2) = P (2 * n + 1) * (C (b n) + X)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_scalar_factor_scalar_right_factor_right_sequence hbase ha
    (isRealRooted_C_add_X_one_sequence b) hscalar hlinear

/-- Sequence shell for degree-plateau scalar/product families whose growth
step is multiplication by `X ^ m_n`. -/
theorem isRealRooted_of_product_scalar_X_pow_sequence
    {P : Nat → ℝ[X]} {a : Nat → ℝ} {m : Nat → Nat}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (ha : ∀ n : Nat, a n ≠ 0)
    (hscalar : ∀ n : Nat, P (2 * n + 1) = C (a n) * P (2 * n))
    (hstep : ∀ n : Nat, P (2 * n + 2) = X ^ (m n) * P (2 * n + 1)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_scalar_factor_sequence hbase ha
    (isRealRooted_X_pow_sequence m) hscalar hstep

/-- Right-factor variant of `isRealRooted_of_product_scalar_X_pow_sequence`. -/
theorem isRealRooted_of_product_scalar_X_pow_right_sequence
    {P : Nat → ℝ[X]} {a : Nat → ℝ} {m : Nat → Nat}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (ha : ∀ n : Nat, a n ≠ 0)
    (hscalar : ∀ n : Nat, P (2 * n + 1) = C (a n) * P (2 * n))
    (hstep : ∀ n : Nat, P (2 * n + 2) = P (2 * n + 1) * X ^ (m n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_scalar_factor_right_sequence hbase ha
    (isRealRooted_X_pow_sequence m) hscalar hstep

/-- Right-scalar variant of `isRealRooted_of_product_scalar_X_pow_sequence`. -/
theorem isRealRooted_of_product_scalar_X_pow_scalar_right_sequence
    {P : Nat → ℝ[X]} {a : Nat → ℝ} {m : Nat → Nat}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (ha : ∀ n : Nat, a n ≠ 0)
    (hscalar : ∀ n : Nat, P (2 * n + 1) = P (2 * n) * C (a n))
    (hstep : ∀ n : Nat, P (2 * n + 2) = X ^ (m n) * P (2 * n + 1)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_scalar_factor_scalar_right_sequence hbase ha
    (isRealRooted_X_pow_sequence m) hscalar hstep

/-- Right-scalar/right-factor variant of
`isRealRooted_of_product_scalar_X_pow_sequence`. -/
theorem isRealRooted_of_product_scalar_X_pow_scalar_right_factor_right_sequence
    {P : Nat → ℝ[X]} {a : Nat → ℝ} {m : Nat → Nat}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (ha : ∀ n : Nat, a n ≠ 0)
    (hscalar : ∀ n : Nat, P (2 * n + 1) = P (2 * n) * C (a n))
    (hstep : ∀ n : Nat, P (2 * n + 2) = P (2 * n + 1) * X ^ (m n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_scalar_factor_scalar_right_factor_right_sequence hbase ha
    (isRealRooted_X_pow_sequence m) hscalar hstep

/-- Alternating scalar/product shell whose growth step is multiplication by
`(X + C b_n) ^ m_n`. -/
theorem isRealRooted_of_product_scalar_X_add_C_pow_sequence
    {P : Nat → ℝ[X]} {a b : Nat → ℝ} {m : Nat → Nat}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (ha : ∀ n : Nat, a n ≠ 0)
    (hscalar : ∀ n : Nat, P (2 * n + 1) = C (a n) * P (2 * n))
    (hstep : ∀ n : Nat, P (2 * n + 2) = (X + C (b n)) ^ (m n) *
      P (2 * n + 1)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_scalar_factor_sequence hbase ha
    (isRealRooted_X_add_C_pow_sequence b m) hscalar hstep

/-- Right-factor variant of
`isRealRooted_of_product_scalar_X_add_C_pow_sequence`. -/
theorem isRealRooted_of_product_scalar_X_add_C_pow_right_sequence
    {P : Nat → ℝ[X]} {a b : Nat → ℝ} {m : Nat → Nat}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (ha : ∀ n : Nat, a n ≠ 0)
    (hscalar : ∀ n : Nat, P (2 * n + 1) = C (a n) * P (2 * n))
    (hstep : ∀ n : Nat, P (2 * n + 2) = P (2 * n + 1) *
      (X + C (b n)) ^ (m n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_scalar_factor_right_sequence hbase ha
    (isRealRooted_X_add_C_pow_sequence b m) hscalar hstep

/-- Right-scalar variant of
`isRealRooted_of_product_scalar_X_add_C_pow_sequence`. -/
theorem isRealRooted_of_product_scalar_X_add_C_pow_scalar_right_sequence
    {P : Nat → ℝ[X]} {a b : Nat → ℝ} {m : Nat → Nat}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (ha : ∀ n : Nat, a n ≠ 0)
    (hscalar : ∀ n : Nat, P (2 * n + 1) = P (2 * n) * C (a n))
    (hstep : ∀ n : Nat, P (2 * n + 2) = (X + C (b n)) ^ (m n) *
      P (2 * n + 1)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_scalar_factor_scalar_right_sequence hbase ha
    (isRealRooted_X_add_C_pow_sequence b m) hscalar hstep

/-- Right-scalar/right-factor variant of
`isRealRooted_of_product_scalar_X_add_C_pow_sequence`. -/
theorem isRealRooted_of_product_scalar_X_add_C_pow_scalar_right_factor_right_sequence
    {P : Nat → ℝ[X]} {a b : Nat → ℝ} {m : Nat → Nat}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (ha : ∀ n : Nat, a n ≠ 0)
    (hscalar : ∀ n : Nat, P (2 * n + 1) = P (2 * n) * C (a n))
    (hstep : ∀ n : Nat, P (2 * n + 2) = P (2 * n + 1) *
      (X + C (b n)) ^ (m n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_scalar_factor_scalar_right_factor_right_sequence hbase ha
    (isRealRooted_X_add_C_pow_sequence b m) hscalar hstep

/-- Alternating scalar/product shell whose growth step is multiplication by
`(C b_n + X) ^ m_n`. -/
theorem isRealRooted_of_product_scalar_C_add_X_pow_sequence
    {P : Nat → ℝ[X]} {a b : Nat → ℝ} {m : Nat → Nat}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (ha : ∀ n : Nat, a n ≠ 0)
    (hscalar : ∀ n : Nat, P (2 * n + 1) = C (a n) * P (2 * n))
    (hstep : ∀ n : Nat, P (2 * n + 2) = (C (b n) + X) ^ (m n) *
      P (2 * n + 1)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_scalar_factor_sequence hbase ha
    (isRealRooted_C_add_X_pow_sequence b m) hscalar hstep

/-- Right-factor variant of
`isRealRooted_of_product_scalar_C_add_X_pow_sequence`. -/
theorem isRealRooted_of_product_scalar_C_add_X_pow_right_sequence
    {P : Nat → ℝ[X]} {a b : Nat → ℝ} {m : Nat → Nat}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (ha : ∀ n : Nat, a n ≠ 0)
    (hscalar : ∀ n : Nat, P (2 * n + 1) = C (a n) * P (2 * n))
    (hstep : ∀ n : Nat, P (2 * n + 2) = P (2 * n + 1) *
      (C (b n) + X) ^ (m n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_scalar_factor_right_sequence hbase ha
    (isRealRooted_C_add_X_pow_sequence b m) hscalar hstep

/-- Right-scalar variant of
`isRealRooted_of_product_scalar_C_add_X_pow_sequence`. -/
theorem isRealRooted_of_product_scalar_C_add_X_pow_scalar_right_sequence
    {P : Nat → ℝ[X]} {a b : Nat → ℝ} {m : Nat → Nat}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (ha : ∀ n : Nat, a n ≠ 0)
    (hscalar : ∀ n : Nat, P (2 * n + 1) = P (2 * n) * C (a n))
    (hstep : ∀ n : Nat, P (2 * n + 2) = (C (b n) + X) ^ (m n) *
      P (2 * n + 1)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_scalar_factor_scalar_right_sequence hbase ha
    (isRealRooted_C_add_X_pow_sequence b m) hscalar hstep

/-- Right-scalar/right-factor variant of
`isRealRooted_of_product_scalar_C_add_X_pow_sequence`. -/
theorem isRealRooted_of_product_scalar_C_add_X_pow_scalar_right_factor_right_sequence
    {P : Nat → ℝ[X]} {a b : Nat → ℝ} {m : Nat → Nat}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (ha : ∀ n : Nat, a n ≠ 0)
    (hscalar : ∀ n : Nat, P (2 * n + 1) = P (2 * n) * C (a n))
    (hstep : ∀ n : Nat, P (2 * n + 2) = P (2 * n + 1) *
      (C (b n) + X) ^ (m n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_scalar_factor_scalar_right_factor_right_sequence hbase ha
    (isRealRooted_C_add_X_pow_sequence b m) hscalar hstep

namespace Tactic

syntax (name := rr_product_factor)
  "rr_product_factor" " using " term ", " term : tactic

syntax (name := rr_product_factor_named)
  "rr_product_factor" " using "
    "realrooted" ":=" term ","
    "slope_ne" ":=" term :
  tactic

syntax (name := rr_product_factor_auto)
  "rr_product_factor_auto" " using " term : tactic

syntax (name := rr_product_factor_auto_named)
  "rr_product_factor_auto" " using "
    "realrooted" ":=" term :
  tactic

syntax (name := rr_product_factor_const_first)
  "rr_product_factor_const_first" " using " term ", " term : tactic

syntax (name := rr_product_factor_const_first_named)
  "rr_product_factor_const_first" " using "
    "realrooted" ":=" term ","
    "slope_ne" ":=" term :
  tactic

syntax (name := rr_product_factor_const_first_auto)
  "rr_product_factor_const_first_auto" " using " term : tactic

syntax (name := rr_product_factor_const_first_auto_named)
  "rr_product_factor_const_first_auto" " using "
    "realrooted" ":=" term :
  tactic

syntax (name := rr_product_factor_X)
  "rr_product_factor_X" " using " term : tactic

syntax (name := rr_product_factor_X_named)
  "rr_product_factor_X" " using "
    "realrooted" ":=" term :
  tactic

syntax (name := rr_product_factor_C_add_X)
  "rr_product_factor_C_add_X" " using " term : tactic

syntax (name := rr_product_factor_C_add_X_named)
  "rr_product_factor_C_add_X" " using "
    "realrooted" ":=" term :
  tactic

syntax (name := rr_product_factor_sequence_named)
  "rr_product_factor_sequence" " using "
    "base" ":=" term ","
    "factor_realrooted" ":=" term ","
    "recurrence" ":=" term :
  tactic

syntax (name := rr_product_identity_sequence_named)
  "rr_product_identity_sequence" " using "
    "base" ":=" term ","
    "recurrence" ":=" term :
  tactic

syntax (name := rr_product_root_zero_sequence_named)
  "rr_product_root_zero_sequence" " using "
    "base" ":=" term ","
    "recurrence" ":=" term :
  tactic

syntax (name := rr_product_period_two_sequence_named)
  "rr_product_period_two_sequence" " using "
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "recurrence" ":=" term :
  tactic

syntax (name := rr_product_lift_sequence_named)
  "rr_product_lift_sequence" " using "
    "quotient_realrooted" ":=" term ","
    "factor_realrooted" ":=" term ","
    "factorization" ":=" term :
  tactic

syntax (name := rr_product_lift_X_sequence_named)
  "rr_product_lift_X_sequence" " using "
    "quotient_realrooted" ":=" term ","
    "factorization" ":=" term :
  tactic

syntax (name := rr_product_lift_X_add_C_sequence_named)
  "rr_product_lift_X_add_C_sequence" " using "
    "quotient_realrooted" ":=" term ","
    "factorization" ":=" term :
  tactic

syntax (name := rr_product_lift_C_add_X_sequence_named)
  "rr_product_lift_C_add_X_sequence" " using "
    "quotient_realrooted" ":=" term ","
    "factorization" ":=" term :
  tactic

syntax (name := rr_product_lift_C_sequence_named)
  "rr_product_lift_C_sequence" " using "
    "quotient_realrooted" ":=" term ","
    "scalar_ne" ":=" term ","
    "factorization" ":=" term :
  tactic

syntax (name := rr_product_lift_C_sequence_auto_named)
  "rr_product_lift_C_sequence_auto" " using "
    "quotient_realrooted" ":=" term ","
    "factorization" ":=" term :
  tactic

syntax (name := rr_even_product_odd_X_scalar_sequence_named)
  "rr_even_product_odd_X_scalar_sequence" " using "
    "even_realrooted" ":=" term ","
    "scalar_ne" ":=" term ","
    "even_factorization" ":=" term ","
    "odd_factorization" ":=" term :
  tactic

syntax (name := rr_product_lift_affine_sequence_named)
  "rr_product_lift_affine_sequence" " using "
    "quotient_realrooted" ":=" term ","
    "slope_ne" ":=" term ","
    "factorization" ":=" term :
  tactic

syntax (name := rr_product_lift_affine_sequence_auto_named)
  "rr_product_lift_affine_sequence_auto" " using "
    "quotient_realrooted" ":=" term ","
    "factorization" ":=" term :
  tactic

syntax (name := rr_product_lift_const_first_sequence_named)
  "rr_product_lift_const_first_sequence" " using "
    "quotient_realrooted" ":=" term ","
    "slope_ne" ":=" term ","
    "factorization" ":=" term :
  tactic

syntax (name := rr_product_lift_const_first_sequence_auto_named)
  "rr_product_lift_const_first_sequence_auto" " using "
    "quotient_realrooted" ":=" term ","
    "factorization" ":=" term :
  tactic

syntax (name := rr_product_lift_C_pow_sequence_named)
  "rr_product_lift_C_pow_sequence" " using "
    "quotient_realrooted" ":=" term ","
    "scalar_ne" ":=" term ","
    "factorization" ":=" term :
  tactic

syntax (name := rr_product_lift_C_pow_sequence_auto_named)
  "rr_product_lift_C_pow_sequence_auto" " using "
    "quotient_realrooted" ":=" term ","
    "factorization" ":=" term :
  tactic

syntax (name := rr_product_lift_X_pow_sequence_named)
  "rr_product_lift_X_pow_sequence" " using "
    "quotient_realrooted" ":=" term ","
    "factorization" ":=" term :
  tactic

syntax (name := rr_product_lift_X_add_C_pow_sequence_named)
  "rr_product_lift_X_add_C_pow_sequence" " using "
    "quotient_realrooted" ":=" term ","
    "factorization" ":=" term :
  tactic

syntax (name := rr_product_lift_X_add_C_row_pow_sequence_named)
  "rr_product_lift_X_add_C_row_pow_sequence" " using "
    "quotient_realrooted" ":=" term ","
    "factorization" ":=" term :
  tactic

syntax (name := rr_product_lift_C_add_X_pow_sequence_named)
  "rr_product_lift_C_add_X_pow_sequence" " using "
    "quotient_realrooted" ":=" term ","
    "factorization" ":=" term :
  tactic

syntax (name := rr_product_lift_affine_pow_sequence_named)
  "rr_product_lift_affine_pow_sequence" " using "
    "quotient_realrooted" ":=" term ","
    "slope_ne" ":=" term ","
    "factorization" ":=" term :
  tactic

syntax (name := rr_product_lift_affine_pow_sequence_auto_named)
  "rr_product_lift_affine_pow_sequence_auto" " using "
    "quotient_realrooted" ":=" term ","
    "factorization" ":=" term :
  tactic

syntax (name := rr_product_lift_const_first_affine_pow_sequence_named)
  "rr_product_lift_const_first_affine_pow_sequence" " using "
    "quotient_realrooted" ":=" term ","
    "slope_ne" ":=" term ","
    "factorization" ":=" term :
  tactic

syntax (name := rr_product_lift_const_first_affine_pow_sequence_auto_named)
  "rr_product_lift_const_first_affine_pow_sequence_auto" " using "
    "quotient_realrooted" ":=" term ","
    "factorization" ":=" term :
  tactic

syntax (name := rr_endpoint_sum_then_X_pair_sequence_named)
  "rr_endpoint_sum_then_X_pair_sequence" " using "
    "base" ":=" term ","
    "left_nonneg" ":=" term ","
    "right_nonneg" ":=" term ","
    "sum_step" ":=" term ","
    "x_step" ":=" term ","
    "coprime" ":=" term :
  tactic

syntax (name := rr_endpoint_sum_then_X_pair_sequence_realrooted_named)
  "rr_endpoint_sum_then_X_pair_sequence_realrooted" " using "
    "base" ":=" term ","
    "left_nonneg" ":=" term ","
    "right_nonneg" ":=" term ","
    "sum_step" ":=" term ","
    "x_step" ":=" term ","
    "coprime" ":=" term :
  tactic

syntax (name := rr_endpoint_X_then_sum_pair_sequence_named)
  "rr_endpoint_X_then_sum_pair_sequence" " using "
    "base" ":=" term ","
    "left_nonneg" ":=" term ","
    "right_nonneg" ":=" term ","
    "x_step" ":=" term ","
    "sum_step" ":=" term ","
    "coprime" ":=" term :
  tactic

syntax (name := rr_endpoint_X_then_sum_pair_sequence_realrooted_named)
  "rr_endpoint_X_then_sum_pair_sequence_realrooted" " using "
    "base" ":=" term ","
    "left_nonneg" ":=" term ","
    "right_nonneg" ":=" term ","
    "x_step" ":=" term ","
    "sum_step" ":=" term ","
    "coprime" ":=" term :
  tactic

syntax (name := rr_endpoint_sum_then_X_pair_lift_sequence_named)
  "rr_endpoint_sum_then_X_pair_lift_sequence" " using "
    "base" ":=" term ","
    "left_nonneg" ":=" term ","
    "right_nonneg" ":=" term ","
    "sum_step" ":=" term ","
    "x_step" ":=" term ","
    "coprime" ":=" term ","
    "even_factorization" ":=" term ","
    "odd_factorization" ":=" term :
  tactic

syntax (name := rr_endpoint_X_then_sum_pair_lift_sequence_named)
  "rr_endpoint_X_then_sum_pair_lift_sequence" " using "
    "base" ":=" term ","
    "left_nonneg" ":=" term ","
    "right_nonneg" ":=" term ","
    "x_step" ":=" term ","
    "sum_step" ":=" term ","
    "coprime" ":=" term ","
    "even_factorization" ":=" term ","
    "odd_factorization" ":=" term :
  tactic

syntax (name := rr_endpoint_X_then_sum_pair_lift_swapped_sequence_named)
  "rr_endpoint_X_then_sum_pair_lift_swapped_sequence" " using "
    "base" ":=" term ","
    "left_nonneg" ":=" term ","
    "right_nonneg" ":=" term ","
    "x_step" ":=" term ","
    "sum_step" ":=" term ","
    "coprime" ":=" term ","
    "even_factorization" ":=" term ","
    "odd_factorization" ":=" term :
  tactic

syntax (name := rr_product_affine_sequence_named)
  "rr_product_affine_sequence" " using "
    "base" ":=" term ","
    "slope_ne" ":=" term ","
    "recurrence" ":=" term :
  tactic

syntax (name := rr_product_affine_sequence_auto_named)
  "rr_product_affine_sequence_auto" " using "
    "base" ":=" term ","
    "recurrence" ":=" term :
  tactic

syntax (name := rr_product_const_first_sequence_named)
  "rr_product_const_first_sequence" " using "
    "base" ":=" term ","
    "slope_ne" ":=" term ","
    "recurrence" ":=" term :
  tactic

syntax (name := rr_product_const_first_sequence_auto_named)
  "rr_product_const_first_sequence_auto" " using "
    "base" ":=" term ","
    "recurrence" ":=" term :
  tactic

syntax (name := rr_product_X_sequence_named)
  "rr_product_X_sequence" " using "
    "base" ":=" term ","
    "recurrence" ":=" term :
  tactic

syntax (name := rr_product_C_add_X_sequence_named)
  "rr_product_C_add_X_sequence" " using "
    "base" ":=" term ","
    "recurrence" ":=" term :
  tactic

syntax (name := rr_product_C_pow_sequence_named)
  "rr_product_C_pow_sequence" " using "
    "base" ":=" term ","
    "scalar_ne" ":=" term ","
    "recurrence" ":=" term :
  tactic

syntax (name := rr_product_C_pow_sequence_auto_named)
  "rr_product_C_pow_sequence_auto" " using "
    "base" ":=" term ","
    "recurrence" ":=" term :
  tactic

syntax (name := rr_product_X_pow_sequence_named)
  "rr_product_X_pow_sequence" " using "
    "base" ":=" term ","
    "recurrence" ":=" term :
  tactic

syntax (name := rr_product_X_add_C_pow_sequence_named)
  "rr_product_X_add_C_pow_sequence" " using "
    "base" ":=" term ","
    "recurrence" ":=" term :
  tactic

syntax (name := rr_product_C_add_X_pow_sequence_named)
  "rr_product_C_add_X_pow_sequence" " using "
    "base" ":=" term ","
    "recurrence" ":=" term :
  tactic

syntax (name := rr_product_affine_pow_sequence_named)
  "rr_product_affine_pow_sequence" " using "
    "base" ":=" term ","
    "slope_ne" ":=" term ","
    "recurrence" ":=" term :
  tactic

syntax (name := rr_product_affine_pow_sequence_auto_named)
  "rr_product_affine_pow_sequence_auto" " using "
    "base" ":=" term ","
    "recurrence" ":=" term :
  tactic

syntax (name := rr_product_const_first_affine_pow_sequence_named)
  "rr_product_const_first_affine_pow_sequence" " using "
    "base" ":=" term ","
    "slope_ne" ":=" term ","
    "recurrence" ":=" term :
  tactic

syntax (name := rr_product_const_first_affine_pow_sequence_auto_named)
  "rr_product_const_first_affine_pow_sequence_auto" " using "
    "base" ":=" term ","
    "recurrence" ":=" term :
  tactic

syntax (name := rr_product_scalar_sequence_named)
  "rr_product_scalar_sequence" " using "
    "base" ":=" term ","
    "scalar_ne" ":=" term ","
    "recurrence" ":=" term :
  tactic

syntax (name := rr_product_scalar_sequence_auto_named)
  "rr_product_scalar_sequence_auto" " using "
    "base" ":=" term ","
    "recurrence" ":=" term :
  tactic

syntax (name := rr_product_scalar_linear_sequence_named)
  "rr_product_scalar_linear_sequence" " using "
    "base" ":=" term ","
    "scalar_ne" ":=" term ","
    "scalar_step" ":=" term ","
    "linear_step" ":=" term :
  tactic

syntax (name := rr_product_scalar_linear_sequence_auto_named)
  "rr_product_scalar_linear_sequence_auto" " using "
    "base" ":=" term ","
    "scalar_step" ":=" term ","
    "linear_step" ":=" term :
  tactic

syntax (name := rr_product_scalar_C_add_X_sequence_named)
  "rr_product_scalar_C_add_X_sequence" " using "
    "base" ":=" term ","
    "scalar_ne" ":=" term ","
    "scalar_step" ":=" term ","
    "linear_step" ":=" term :
  tactic

syntax (name := rr_product_scalar_C_add_X_sequence_auto_named)
  "rr_product_scalar_C_add_X_sequence_auto" " using "
    "base" ":=" term ","
    "scalar_step" ":=" term ","
    "linear_step" ":=" term :
  tactic

syntax (name := rr_product_scalar_factor_sequence_named)
  "rr_product_scalar_factor_sequence" " using "
    "base" ":=" term ","
    "scalar_ne" ":=" term ","
    "factor_realrooted" ":=" term ","
    "scalar_step" ":=" term ","
    "factor_step" ":=" term :
  tactic

syntax (name := rr_product_scalar_factor_sequence_auto_named)
  "rr_product_scalar_factor_sequence_auto" " using "
    "base" ":=" term ","
    "factor_realrooted" ":=" term ","
    "scalar_step" ":=" term ","
    "factor_step" ":=" term :
  tactic

syntax (name := rr_product_scalar_X_pow_sequence_named)
  "rr_product_scalar_X_pow_sequence" " using "
    "base" ":=" term ","
    "scalar_ne" ":=" term ","
    "scalar_step" ":=" term ","
    "factor_step" ":=" term :
  tactic

syntax (name := rr_product_scalar_X_pow_sequence_auto_named)
  "rr_product_scalar_X_pow_sequence_auto" " using "
    "base" ":=" term ","
    "scalar_step" ":=" term ","
    "factor_step" ":=" term :
  tactic

syntax (name := rr_product_scalar_X_add_C_pow_sequence_named)
  "rr_product_scalar_X_add_C_pow_sequence" " using "
    "base" ":=" term ","
    "scalar_ne" ":=" term ","
    "scalar_step" ":=" term ","
    "factor_step" ":=" term :
  tactic

syntax (name := rr_product_scalar_X_add_C_pow_sequence_auto_named)
  "rr_product_scalar_X_add_C_pow_sequence_auto" " using "
    "base" ":=" term ","
    "scalar_step" ":=" term ","
    "factor_step" ":=" term :
  tactic

syntax (name := rr_product_scalar_C_add_X_pow_sequence_named)
  "rr_product_scalar_C_add_X_pow_sequence" " using "
    "base" ":=" term ","
    "scalar_ne" ":=" term ","
    "scalar_step" ":=" term ","
    "factor_step" ":=" term :
  tactic

syntax (name := rr_product_scalar_C_add_X_pow_sequence_auto_named)
  "rr_product_scalar_C_add_X_pow_sequence_auto" " using "
    "base" ":=" term ","
    "scalar_step" ":=" term ","
    "factor_step" ":=" term :
  tactic

syntax (name := rr_product_nonzero) "rr_product_nonzero" : tactic

syntax (name := rr_product_nonzero_seq) "rr_product_nonzero_seq" : term

syntax (name := rr_product_two_variants)
  "rr_product_two_variants" term ", " term :
  tactic

syntax (name := rr_product_two_sequence_variants)
  "rr_product_two_sequence_variants" term ", " term :
  tactic

syntax (name := rr_product_four_sequence_variants)
  "rr_product_four_sequence_variants" term ", " term ", " term ", " term :
  tactic

macro_rules
  | `(tactic| rr_product_nonzero) =>
      `(tactic| rr_side_ne)
  | `(rr_product_nonzero_seq) =>
      `(fun n => by rr_product_nonzero)
  | `(tactic| rr_product_two_variants $hleft:term, $hright:term) =>
      `(tactic|
        rr_first_realrooted_or_projection $hleft, $hright)
  | `(tactic| rr_product_two_sequence_variants $hleft:term, $hright:term) =>
      `(tactic|
        rr_first_realrooted_sequence_or_projection $hleft, $hright)
  | `(tactic|
      rr_product_four_sequence_variants
        $hleft:term, $hright:term, $hscalar_right:term, $hfactor_right:term) =>
      `(tactic|
        rr_first_realrooted_sequence_or_projection
          $hleft, $hright, $hscalar_right, $hfactor_right)

macro_rules
  | `(tactic| rr_product_factor using $hp:term, $hs:term) =>
      `(tactic|
        rr_product_two_variants
          (RealRooted.isRealRooted_C_mul_X_add_C_mul $hp $hs),
          (RealRooted.isRealRooted_mul_C_mul_X_add_C $hp $hs))
  | `(tactic|
      rr_product_factor using
        realrooted := $hp:term,
        slope_ne := $hs:term) =>
      `(tactic|
        rr_product_factor using $hp, $hs)
  | `(tactic| rr_product_factor_auto using $hp:term) =>
      `(tactic|
        rr_product_factor using $hp, (by rr_product_nonzero))
  | `(tactic|
      rr_product_factor_auto using
        realrooted := $hp:term) =>
      `(tactic|
        rr_product_factor_auto using $hp)
  | `(tactic| rr_product_factor_const_first using $hp:term, $hs:term) =>
      `(tactic|
        rr_product_two_variants
          (RealRooted.isRealRooted_C_add_C_mul_X_mul $hp $hs),
          (RealRooted.isRealRooted_mul_C_add_C_mul_X $hp $hs))
  | `(tactic|
      rr_product_factor_const_first using
        realrooted := $hp:term,
        slope_ne := $hs:term) =>
      `(tactic|
        rr_product_factor_const_first using $hp, $hs)
  | `(tactic| rr_product_factor_const_first_auto using $hp:term) =>
      `(tactic|
        rr_product_factor_const_first using $hp, (by rr_product_nonzero))
  | `(tactic|
      rr_product_factor_const_first_auto using
        realrooted := $hp:term) =>
      `(tactic|
        rr_product_factor_const_first_auto using $hp)
  | `(tactic| rr_product_factor_X using $hp:term) =>
      `(tactic|
        rr_product_two_variants
          (RealRooted.isRealRooted_X_add_C_mul $hp),
          (RealRooted.isRealRooted_mul_X_add_C $hp))
  | `(tactic|
      rr_product_factor_X using
        realrooted := $hp:term) =>
      `(tactic|
        rr_product_factor_X using $hp)
  | `(tactic| rr_product_factor_C_add_X using $hp:term) =>
      `(tactic|
        rr_product_two_variants
          (RealRooted.isRealRooted_C_add_X_mul $hp),
          (RealRooted.isRealRooted_mul_C_add_X $hp))
  | `(tactic|
      rr_product_factor_C_add_X using
        realrooted := $hp:term) =>
      `(tactic|
        rr_product_factor_C_add_X using $hp)
  | `(tactic|
      rr_product_factor_sequence using
        base := $hbase:term,
        factor_realrooted := $hfactor:term,
        recurrence := $hstep:term) =>
      `(tactic|
        rr_product_two_sequence_variants
          (RealRooted.isRealRooted_of_product_factor_sequence
            $hbase $hfactor $hstep),
          (RealRooted.isRealRooted_of_product_factor_right_sequence
            $hbase $hfactor $hstep))
  | `(tactic|
      rr_product_identity_sequence using
        base := $hbase:term,
        recurrence := $hstep:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_product_identity_sequence $hbase $hstep))
  | `(tactic|
      rr_product_root_zero_sequence using
        base := $hbase:term,
        recurrence := $hstep:term) =>
      `(tactic|
        rr_product_two_sequence_variants
          (RealRooted.isRealRooted_of_product_root_zero_sequence $hbase $hstep),
          (RealRooted.isRealRooted_of_product_root_zero_right_sequence
            $hbase $hstep))
  | `(tactic|
      rr_product_period_two_sequence using
        base_zero := $hbase_zero:term,
        base_one := $hbase_one:term,
        recurrence := $hstep:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_product_period_two_sequence
            $hbase_zero $hbase_one $hstep))
  | `(tactic|
      rr_product_lift_sequence using
        quotient_realrooted := $hquot:term,
        factor_realrooted := $hfactor:term,
        factorization := $hrow:term) =>
      `(tactic|
        rr_product_two_sequence_variants
          (RealRooted.isRealRooted_of_product_lift_sequence
            $hquot $hfactor $hrow),
          (RealRooted.isRealRooted_of_product_lift_right_sequence
            $hquot $hfactor $hrow))
  | `(tactic|
      rr_product_lift_X_sequence using
        quotient_realrooted := $hquot:term,
        factorization := $hrow:term) =>
      `(tactic|
        rr_product_two_sequence_variants
          (RealRooted.isRealRooted_of_X_lift_sequence $hquot $hrow),
          (RealRooted.isRealRooted_of_X_lift_right_sequence $hquot $hrow))
  | `(tactic|
      rr_product_lift_X_add_C_sequence using
        quotient_realrooted := $hquot:term,
        factorization := $hrow:term) =>
      `(tactic|
        rr_product_two_sequence_variants
          (RealRooted.isRealRooted_of_X_add_C_lift_sequence $hquot $hrow),
          (RealRooted.isRealRooted_of_X_add_C_lift_right_sequence
            $hquot $hrow))
  | `(tactic|
      rr_product_lift_C_add_X_sequence using
        quotient_realrooted := $hquot:term,
        factorization := $hrow:term) =>
      `(tactic|
        rr_product_two_sequence_variants
          (RealRooted.isRealRooted_of_C_add_X_lift_sequence $hquot $hrow),
          (RealRooted.isRealRooted_of_C_add_X_lift_right_sequence
            $hquot $hrow))
  | `(tactic|
      rr_product_lift_C_sequence using
        quotient_realrooted := $hquot:term,
        scalar_ne := $hc:term,
        factorization := $hrow:term) =>
      `(tactic|
        rr_product_two_sequence_variants
          (RealRooted.isRealRooted_of_C_lift_sequence $hquot $hc $hrow),
          (RealRooted.isRealRooted_of_C_lift_right_sequence $hquot $hc $hrow))
  | `(tactic|
      rr_product_lift_C_sequence_auto using
        quotient_realrooted := $hquot:term,
        factorization := $hrow:term) =>
      `(tactic|
        rr_product_lift_C_sequence using
          quotient_realrooted := $hquot,
          scalar_ne := rr_product_nonzero_seq,
          factorization := $hrow)
  | `(tactic|
      rr_even_product_odd_X_scalar_sequence using
        even_realrooted := $hquot:term,
        scalar_ne := $ha:term,
        even_factorization := $heven:term,
        odd_factorization := $hodd:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_even_product_odd_X_scalar_sequence
            $hquot $ha $heven $hodd))
  | `(tactic|
      rr_product_lift_affine_sequence using
        quotient_realrooted := $hquot:term,
        slope_ne := $hs:term,
        factorization := $hrow:term) =>
      `(tactic|
        rr_product_two_sequence_variants
          (RealRooted.isRealRooted_of_C_mul_X_add_C_lift_sequence
            $hquot $hs $hrow),
          (RealRooted.isRealRooted_of_C_mul_X_add_C_lift_right_sequence
            $hquot $hs $hrow))
  | `(tactic|
      rr_product_lift_affine_sequence_auto using
        quotient_realrooted := $hquot:term,
        factorization := $hrow:term) =>
      `(tactic|
        rr_product_lift_affine_sequence using
          quotient_realrooted := $hquot,
          slope_ne := rr_product_nonzero_seq,
          factorization := $hrow)
  | `(tactic|
      rr_product_lift_const_first_sequence using
        quotient_realrooted := $hquot:term,
        slope_ne := $hs:term,
        factorization := $hrow:term) =>
      `(tactic|
        rr_product_two_sequence_variants
          (RealRooted.isRealRooted_of_C_add_C_mul_X_lift_sequence
            $hquot $hs $hrow),
          (RealRooted.isRealRooted_of_C_add_C_mul_X_lift_right_sequence
            $hquot $hs $hrow))
  | `(tactic|
      rr_product_lift_const_first_sequence_auto using
        quotient_realrooted := $hquot:term,
        factorization := $hrow:term) =>
      `(tactic|
        rr_product_lift_const_first_sequence using
          quotient_realrooted := $hquot,
          slope_ne := rr_product_nonzero_seq,
          factorization := $hrow)
  | `(tactic|
      rr_product_lift_C_pow_sequence using
        quotient_realrooted := $hquot:term,
        scalar_ne := $hc:term,
        factorization := $hrow:term) =>
      `(tactic|
        rr_product_two_sequence_variants
          (RealRooted.isRealRooted_of_C_pow_lift_sequence $hquot $hc $hrow),
          (RealRooted.isRealRooted_of_C_pow_lift_right_sequence
            $hquot $hc $hrow))
  | `(tactic|
      rr_product_lift_C_pow_sequence_auto using
        quotient_realrooted := $hquot:term,
        factorization := $hrow:term) =>
      `(tactic|
        rr_product_lift_C_pow_sequence using
          quotient_realrooted := $hquot,
          scalar_ne := rr_product_nonzero_seq,
          factorization := $hrow)
  | `(tactic|
      rr_product_lift_X_pow_sequence using
        quotient_realrooted := $hquot:term,
        factorization := $hrow:term) =>
      `(tactic|
        rr_product_two_sequence_variants
          (RealRooted.isRealRooted_of_X_pow_lift_sequence $hquot $hrow),
          (RealRooted.isRealRooted_of_X_pow_lift_right_sequence $hquot $hrow))
  | `(tactic|
      rr_product_lift_X_add_C_pow_sequence using
        quotient_realrooted := $hquot:term,
        factorization := $hrow:term) =>
      `(tactic|
        rr_product_two_sequence_variants
          (RealRooted.isRealRooted_of_X_add_C_pow_lift_sequence $hquot $hrow),
          (RealRooted.isRealRooted_of_X_add_C_pow_lift_right_sequence
            $hquot $hrow))
  | `(tactic|
      rr_product_lift_X_add_C_row_pow_sequence using
        quotient_realrooted := $hquot:term,
        factorization := $hrow:term) =>
      `(tactic|
        rr_product_two_sequence_variants
          (RealRooted.isRealRooted_of_X_add_C_row_pow_lift_sequence
            $hquot $hrow),
          (RealRooted.isRealRooted_of_X_add_C_row_pow_lift_right_sequence
            $hquot $hrow))
  | `(tactic|
      rr_product_lift_C_add_X_pow_sequence using
        quotient_realrooted := $hquot:term,
        factorization := $hrow:term) =>
      `(tactic|
        rr_product_two_sequence_variants
          (RealRooted.isRealRooted_of_C_add_X_pow_lift_sequence $hquot $hrow),
          (RealRooted.isRealRooted_of_C_add_X_pow_lift_right_sequence
            $hquot $hrow))
  | `(tactic|
      rr_product_lift_affine_pow_sequence using
        quotient_realrooted := $hquot:term,
        slope_ne := $hs:term,
        factorization := $hrow:term) =>
      `(tactic|
        rr_product_two_sequence_variants
          (RealRooted.isRealRooted_of_C_mul_X_add_C_pow_lift_sequence
            $hquot $hs $hrow),
          (RealRooted.isRealRooted_of_C_mul_X_add_C_pow_lift_right_sequence
            $hquot $hs $hrow))
  | `(tactic|
      rr_product_lift_affine_pow_sequence_auto using
        quotient_realrooted := $hquot:term,
        factorization := $hrow:term) =>
      `(tactic|
        rr_product_lift_affine_pow_sequence using
          quotient_realrooted := $hquot,
          slope_ne := rr_product_nonzero_seq,
          factorization := $hrow)
  | `(tactic|
      rr_product_lift_const_first_affine_pow_sequence using
        quotient_realrooted := $hquot:term,
        slope_ne := $hs:term,
        factorization := $hrow:term) =>
      `(tactic|
        rr_product_two_sequence_variants
          (RealRooted.isRealRooted_of_C_add_C_mul_X_pow_lift_sequence
            $hquot $hs $hrow),
          (RealRooted.isRealRooted_of_C_add_C_mul_X_pow_lift_right_sequence
            $hquot $hs $hrow))
  | `(tactic|
      rr_product_lift_const_first_affine_pow_sequence_auto using
        quotient_realrooted := $hquot:term,
        factorization := $hrow:term) =>
      `(tactic|
        rr_product_lift_const_first_affine_pow_sequence using
          quotient_realrooted := $hquot,
          slope_ne := rr_product_nonzero_seq,
          factorization := $hrow)
  | `(tactic|
      rr_endpoint_sum_then_X_pair_sequence using
        base := $hbase:term,
        left_nonneg := $hleft_nonneg:term,
        right_nonneg := $hright_nonneg:term,
        sum_step := $hsum_step:term,
        x_step := $hx_step:term,
        coprime := $hcop:term) =>
      `(tactic|
        exact RealRooted.prec_endpoint_sum_then_X_pair_sequence
          $hbase $hleft_nonneg $hright_nonneg $hsum_step $hx_step $hcop)
  | `(tactic|
      rr_endpoint_sum_then_X_pair_sequence_realrooted using
        base := $hbase:term,
        left_nonneg := $hleft_nonneg:term,
        right_nonneg := $hright_nonneg:term,
        sum_step := $hsum_step:term,
        x_step := $hx_step:term,
        coprime := $hcop:term) =>
      `(tactic|
        rr_exact_realrooted_pair_sequence_or_projection
          (RealRooted.isRealRooted_of_endpoint_sum_then_X_pair_sequence
            $hbase $hleft_nonneg $hright_nonneg $hsum_step $hx_step $hcop))
  | `(tactic|
      rr_endpoint_X_then_sum_pair_sequence using
        base := $hbase:term,
        left_nonneg := $hleft_nonneg:term,
        right_nonneg := $hright_nonneg:term,
        x_step := $hx_step:term,
        sum_step := $hsum_step:term,
        coprime := $hcop:term) =>
      `(tactic|
        exact RealRooted.prec_endpoint_X_then_sum_pair_sequence
          $hbase $hleft_nonneg $hright_nonneg $hx_step $hsum_step $hcop)
  | `(tactic|
      rr_endpoint_X_then_sum_pair_sequence_realrooted using
        base := $hbase:term,
        left_nonneg := $hleft_nonneg:term,
        right_nonneg := $hright_nonneg:term,
        x_step := $hx_step:term,
        sum_step := $hsum_step:term,
        coprime := $hcop:term) =>
      `(tactic|
        rr_exact_realrooted_pair_sequence_or_projection
          (RealRooted.isRealRooted_of_endpoint_X_then_sum_pair_sequence
            $hbase $hleft_nonneg $hright_nonneg $hx_step $hsum_step $hcop))
  | `(tactic|
      rr_endpoint_sum_then_X_pair_lift_sequence using
        base := $hbase:term,
        left_nonneg := $hleft_nonneg:term,
        right_nonneg := $hright_nonneg:term,
        sum_step := $hsum_step:term,
        x_step := $hx_step:term,
        coprime := $hcop:term,
        even_factorization := $heven:term,
        odd_factorization := $hodd:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_endpoint_sum_then_X_pair_lift_sequence
            $hbase $hleft_nonneg $hright_nonneg $hsum_step $hx_step $hcop
            $heven $hodd))
  | `(tactic|
      rr_endpoint_X_then_sum_pair_lift_sequence using
        base := $hbase:term,
        left_nonneg := $hleft_nonneg:term,
        right_nonneg := $hright_nonneg:term,
        x_step := $hx_step:term,
        sum_step := $hsum_step:term,
        coprime := $hcop:term,
        even_factorization := $heven:term,
        odd_factorization := $hodd:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_endpoint_X_then_sum_pair_lift_sequence
            $hbase $hleft_nonneg $hright_nonneg $hx_step $hsum_step $hcop
            $heven $hodd))
  | `(tactic|
      rr_endpoint_X_then_sum_pair_lift_swapped_sequence using
        base := $hbase:term,
        left_nonneg := $hleft_nonneg:term,
        right_nonneg := $hright_nonneg:term,
        x_step := $hx_step:term,
        sum_step := $hsum_step:term,
        coprime := $hcop:term,
        even_factorization := $heven:term,
        odd_factorization := $hodd:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_endpoint_X_then_sum_pair_lift_swapped_sequence
            $hbase $hleft_nonneg $hright_nonneg $hx_step $hsum_step $hcop
            $heven $hodd))
  | `(tactic|
      rr_product_affine_sequence using
        base := $hbase:term,
        slope_ne := $hs:term,
        recurrence := $hstep:term) =>
      `(tactic|
        rr_product_two_sequence_variants
          (RealRooted.isRealRooted_of_product_affine_sequence
            $hbase $hs $hstep),
          (RealRooted.isRealRooted_of_product_affine_right_sequence
            $hbase $hs $hstep))
  | `(tactic|
      rr_product_affine_sequence_auto using
        base := $hbase:term,
        recurrence := $hstep:term) =>
      `(tactic|
        rr_product_affine_sequence using
          base := $hbase,
          slope_ne := rr_product_nonzero_seq,
          recurrence := $hstep)
  | `(tactic|
      rr_product_const_first_sequence using
        base := $hbase:term,
        slope_ne := $hs:term,
        recurrence := $hstep:term) =>
      `(tactic|
        rr_product_two_sequence_variants
          (RealRooted.isRealRooted_of_product_const_first_affine_sequence
            $hbase $hs $hstep),
          (RealRooted.isRealRooted_of_product_const_first_affine_right_sequence
            $hbase $hs $hstep))
  | `(tactic|
      rr_product_const_first_sequence_auto using
        base := $hbase:term,
        recurrence := $hstep:term) =>
      `(tactic|
        rr_product_const_first_sequence using
          base := $hbase,
          slope_ne := rr_product_nonzero_seq,
          recurrence := $hstep)
  | `(tactic|
      rr_product_X_sequence using
        base := $hbase:term,
        recurrence := $hstep:term) =>
      `(tactic|
        rr_product_two_sequence_variants
          (RealRooted.isRealRooted_of_product_X_add_C_sequence $hbase $hstep),
          (RealRooted.isRealRooted_of_product_X_add_C_right_sequence
            $hbase $hstep))
  | `(tactic|
      rr_product_C_add_X_sequence using
        base := $hbase:term,
        recurrence := $hstep:term) =>
      `(tactic|
        rr_product_two_sequence_variants
          (RealRooted.isRealRooted_of_product_C_add_X_sequence $hbase $hstep),
          (RealRooted.isRealRooted_of_product_C_add_X_right_sequence
            $hbase $hstep))
  | `(tactic|
      rr_product_C_pow_sequence using
        base := $hbase:term,
        scalar_ne := $hc:term,
        recurrence := $hstep:term) =>
      `(tactic|
        rr_product_two_sequence_variants
          (RealRooted.isRealRooted_of_product_C_pow_sequence
            $hbase $hc $hstep),
          (RealRooted.isRealRooted_of_product_C_pow_right_sequence
            $hbase $hc $hstep))
  | `(tactic|
      rr_product_C_pow_sequence_auto using
        base := $hbase:term,
        recurrence := $hstep:term) =>
      `(tactic|
        rr_product_C_pow_sequence using
          base := $hbase,
          scalar_ne := rr_product_nonzero_seq,
          recurrence := $hstep)
  | `(tactic|
      rr_product_X_pow_sequence using
        base := $hbase:term,
        recurrence := $hstep:term) =>
      `(tactic|
        rr_product_two_sequence_variants
          (RealRooted.isRealRooted_of_product_X_pow_sequence $hbase $hstep),
          (RealRooted.isRealRooted_of_product_X_pow_right_sequence
            $hbase $hstep))
  | `(tactic|
      rr_product_X_add_C_pow_sequence using
        base := $hbase:term,
        recurrence := $hstep:term) =>
      `(tactic|
        rr_product_two_sequence_variants
          (RealRooted.isRealRooted_of_product_X_add_C_pow_sequence
            $hbase $hstep),
          (RealRooted.isRealRooted_of_product_X_add_C_pow_right_sequence
            $hbase $hstep))
  | `(tactic|
      rr_product_C_add_X_pow_sequence using
        base := $hbase:term,
        recurrence := $hstep:term) =>
      `(tactic|
        rr_product_two_sequence_variants
          (RealRooted.isRealRooted_of_product_C_add_X_pow_sequence
            $hbase $hstep),
          (RealRooted.isRealRooted_of_product_C_add_X_pow_right_sequence
            $hbase $hstep))
  | `(tactic|
      rr_product_affine_pow_sequence using
        base := $hbase:term,
        slope_ne := $hs:term,
        recurrence := $hstep:term) =>
      `(tactic|
        rr_product_two_sequence_variants
          (RealRooted.isRealRooted_of_product_C_mul_X_add_C_pow_sequence
            $hbase $hs $hstep),
          (RealRooted.isRealRooted_of_product_C_mul_X_add_C_pow_right_sequence
            $hbase $hs $hstep))
  | `(tactic|
      rr_product_affine_pow_sequence_auto using
        base := $hbase:term,
        recurrence := $hstep:term) =>
      `(tactic|
        rr_product_affine_pow_sequence using
          base := $hbase,
          slope_ne := rr_product_nonzero_seq,
          recurrence := $hstep)
  | `(tactic|
      rr_product_const_first_affine_pow_sequence using
        base := $hbase:term,
        slope_ne := $hs:term,
        recurrence := $hstep:term) =>
      `(tactic|
        rr_product_two_sequence_variants
          (RealRooted.isRealRooted_of_product_C_add_C_mul_X_pow_sequence
            $hbase $hs $hstep),
          (RealRooted.isRealRooted_of_product_C_add_C_mul_X_pow_right_sequence
            $hbase $hs $hstep))
  | `(tactic|
      rr_product_const_first_affine_pow_sequence_auto using
        base := $hbase:term,
        recurrence := $hstep:term) =>
      `(tactic|
        rr_product_const_first_affine_pow_sequence using
          base := $hbase,
          slope_ne := rr_product_nonzero_seq,
          recurrence := $hstep)
  | `(tactic|
      rr_product_scalar_sequence using
        base := $hbase:term,
        scalar_ne := $ha:term,
        recurrence := $hstep:term) =>
      `(tactic|
        rr_product_two_sequence_variants
          (RealRooted.isRealRooted_of_product_scalar_sequence
            $hbase $ha $hstep),
          (RealRooted.isRealRooted_of_product_scalar_right_sequence
            $hbase $ha $hstep))
  | `(tactic|
      rr_product_scalar_sequence_auto using
        base := $hbase:term,
        recurrence := $hstep:term) =>
      `(tactic|
        rr_product_scalar_sequence using
          base := $hbase,
          scalar_ne := rr_product_nonzero_seq,
          recurrence := $hstep)
  | `(tactic|
      rr_product_scalar_linear_sequence using
        base := $hbase:term,
        scalar_ne := $ha:term,
        scalar_step := $hscalar:term,
        linear_step := $hlinear:term) =>
      `(tactic|
        rr_product_four_sequence_variants
          (RealRooted.isRealRooted_of_product_scalar_linear_sequence
            $hbase $ha $hscalar $hlinear),
          (RealRooted.isRealRooted_of_product_scalar_linear_right_sequence
            $hbase $ha $hscalar $hlinear),
          (RealRooted.isRealRooted_of_product_scalar_linear_scalar_right_sequence
            $hbase $ha $hscalar $hlinear),
          (RealRooted.isRealRooted_of_product_scalar_linear_scalar_right_linear_right_sequence
            $hbase $ha $hscalar $hlinear))
  | `(tactic|
      rr_product_scalar_linear_sequence_auto using
        base := $hbase:term,
        scalar_step := $hscalar:term,
        linear_step := $hlinear:term) =>
      `(tactic|
        rr_product_scalar_linear_sequence using
          base := $hbase,
          scalar_ne := rr_product_nonzero_seq,
          scalar_step := $hscalar,
          linear_step := $hlinear)
  | `(tactic|
      rr_product_scalar_C_add_X_sequence using
        base := $hbase:term,
        scalar_ne := $ha:term,
        scalar_step := $hscalar:term,
        linear_step := $hlinear:term) =>
      `(tactic|
        rr_product_four_sequence_variants
          (RealRooted.isRealRooted_of_product_scalar_C_add_X_sequence
            $hbase $ha $hscalar $hlinear),
          (RealRooted.isRealRooted_of_product_scalar_C_add_X_right_sequence
            $hbase $ha $hscalar $hlinear),
          (RealRooted.isRealRooted_of_product_scalar_C_add_X_scalar_right_sequence
            $hbase $ha $hscalar $hlinear),
          (RealRooted.isRealRooted_of_product_scalar_C_add_X_scalar_right_linear_right_sequence
            $hbase $ha $hscalar $hlinear))
  | `(tactic|
      rr_product_scalar_C_add_X_sequence_auto using
        base := $hbase:term,
        scalar_step := $hscalar:term,
        linear_step := $hlinear:term) =>
      `(tactic|
        rr_product_scalar_C_add_X_sequence using
          base := $hbase,
          scalar_ne := rr_product_nonzero_seq,
          scalar_step := $hscalar,
          linear_step := $hlinear)
  | `(tactic|
      rr_product_scalar_factor_sequence using
        base := $hbase:term,
        scalar_ne := $ha:term,
        factor_realrooted := $hfactor:term,
        scalar_step := $hscalar:term,
        factor_step := $hstep:term) =>
      `(tactic|
        rr_product_four_sequence_variants
          (RealRooted.isRealRooted_of_product_scalar_factor_sequence
            $hbase $ha $hfactor $hscalar $hstep),
          (RealRooted.isRealRooted_of_product_scalar_factor_right_sequence
            $hbase $ha $hfactor $hscalar $hstep),
          (RealRooted.isRealRooted_of_product_scalar_factor_scalar_right_sequence
            $hbase $ha $hfactor $hscalar $hstep),
          (RealRooted.isRealRooted_of_product_scalar_factor_scalar_right_factor_right_sequence
            $hbase $ha $hfactor $hscalar $hstep))
  | `(tactic|
      rr_product_scalar_factor_sequence_auto using
        base := $hbase:term,
        factor_realrooted := $hfactor:term,
        scalar_step := $hscalar:term,
        factor_step := $hstep:term) =>
      `(tactic|
        rr_product_scalar_factor_sequence using
          base := $hbase,
          scalar_ne := rr_product_nonzero_seq,
          factor_realrooted := $hfactor,
          scalar_step := $hscalar,
          factor_step := $hstep)
  | `(tactic|
      rr_product_scalar_X_pow_sequence using
        base := $hbase:term,
        scalar_ne := $ha:term,
        scalar_step := $hscalar:term,
        factor_step := $hstep:term) =>
      `(tactic|
        rr_product_four_sequence_variants
          (RealRooted.isRealRooted_of_product_scalar_X_pow_sequence
            $hbase $ha $hscalar $hstep),
          (RealRooted.isRealRooted_of_product_scalar_X_pow_right_sequence
            $hbase $ha $hscalar $hstep),
          (RealRooted.isRealRooted_of_product_scalar_X_pow_scalar_right_sequence
            $hbase $ha $hscalar $hstep),
          (RealRooted.isRealRooted_of_product_scalar_X_pow_scalar_right_factor_right_sequence
            $hbase $ha $hscalar $hstep))
  | `(tactic|
      rr_product_scalar_X_pow_sequence_auto using
        base := $hbase:term,
        scalar_step := $hscalar:term,
        factor_step := $hstep:term) =>
      `(tactic|
        rr_product_scalar_X_pow_sequence using
          base := $hbase,
          scalar_ne := rr_product_nonzero_seq,
          scalar_step := $hscalar,
          factor_step := $hstep)
  | `(tactic|
      rr_product_scalar_X_add_C_pow_sequence using
        base := $hbase:term,
        scalar_ne := $ha:term,
        scalar_step := $hscalar:term,
        factor_step := $hstep:term) =>
      `(tactic|
        rr_product_four_sequence_variants
          (RealRooted.isRealRooted_of_product_scalar_X_add_C_pow_sequence
            $hbase $ha $hscalar $hstep),
          (RealRooted.isRealRooted_of_product_scalar_X_add_C_pow_right_sequence
            $hbase $ha $hscalar $hstep),
          (RealRooted.isRealRooted_of_product_scalar_X_add_C_pow_scalar_right_sequence
            $hbase $ha $hscalar $hstep),
          (isRealRooted_of_product_scalar_X_add_C_pow_scalar_right_factor_right_sequence
            $hbase $ha $hscalar $hstep))
  | `(tactic|
      rr_product_scalar_X_add_C_pow_sequence_auto using
        base := $hbase:term,
        scalar_step := $hscalar:term,
        factor_step := $hstep:term) =>
      `(tactic|
        rr_product_scalar_X_add_C_pow_sequence using
          base := $hbase,
          scalar_ne := rr_product_nonzero_seq,
          scalar_step := $hscalar,
          factor_step := $hstep)
  | `(tactic|
      rr_product_scalar_C_add_X_pow_sequence using
        base := $hbase:term,
        scalar_ne := $ha:term,
        scalar_step := $hscalar:term,
        factor_step := $hstep:term) =>
      `(tactic|
        rr_product_four_sequence_variants
          (RealRooted.isRealRooted_of_product_scalar_C_add_X_pow_sequence
            $hbase $ha $hscalar $hstep),
          (RealRooted.isRealRooted_of_product_scalar_C_add_X_pow_right_sequence
            $hbase $ha $hscalar $hstep),
          (RealRooted.isRealRooted_of_product_scalar_C_add_X_pow_scalar_right_sequence
            $hbase $ha $hscalar $hstep),
          (isRealRooted_of_product_scalar_C_add_X_pow_scalar_right_factor_right_sequence
            $hbase $ha $hscalar $hstep))
  | `(tactic|
      rr_product_scalar_C_add_X_pow_sequence_auto using
        base := $hbase:term,
        scalar_step := $hscalar:term,
        factor_step := $hstep:term) =>
      `(tactic|
        rr_product_scalar_C_add_X_pow_sequence using
          base := $hbase,
          scalar_ne := rr_product_nonzero_seq,
          scalar_step := $hscalar,
          factor_step := $hstep)

end Tactic
end RealRooted
