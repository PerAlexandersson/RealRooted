import RealRooted.Linear
import RealRooted.PosCombo
import RealRooted.Tactic.Finish

/-!
# Product-factor tactic

Small wrappers for recurrence steps where a row is obtained by multiplying the
previous row by a real linear factor.
-/

open Polynomial
open scoped BigOperators

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

/-- Unit-slope real linear factors are real-rooted. -/
theorem isRealRooted_X_add_C (t : ℝ) :
    (X + C t : ℝ[X]) ≠ 0 ∧ (X + C t : ℝ[X]).Splits := by
  simpa using isRealRooted_C_mul_X_add_C (s := 1) (t := t) rr_side_ne_term

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
    (isRealRooted_C_mul_X_add_C_mul (p := p) (s := 1) (t := t) hp rr_side_ne_term)

theorem isRealRooted_mul_X_add_C {p : ℝ[X]} {t : ℝ}
    (hp : p ≠ 0 ∧ p.Splits) :
    (p * (X + C t) ≠ 0 ∧ (p * (X + C t)).Splits) := by
  simpa using
    (isRealRooted_mul_C_mul_X_add_C (p := p) (s := 1) (t := t) hp rr_side_ne_term)

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

private theorem isRealRooted_of_even_odd_sequence {P : Nat → ℝ[X]}
    (heven : ∀ n : Nat, P (2 * n) ≠ 0 ∧ (P (2 * n)).Splits)
    (hodd : ∀ n : Nat, P (2 * n + 1) ≠ 0 ∧ (P (2 * n + 1)).Splits) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
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
        isRealRooted_mul_of_isRealRooted (hfactor n) ih
      simpa [Nat.succ_eq_add_one, hstep n] using hnext

/-- Tail-start sequence shell for first-order product recurrences with a
supplied factor certificate.  The finitely many rows before `N` are supplied
as base cases, and the product recurrence is used from row `N` onward. -/
theorem isRealRooted_of_product_factor_sequence_from
    {P F : Nat → ℝ[X]}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hfactor : ∀ n : Nat, N ≤ n → F n ≠ 0 ∧ (F n).Splits)
    (hstep : ∀ n : Nat, N ≤ n → P (n + 1) = F n * P n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := fun n =>
  Nat.strong_induction_on n fun n ih => by
    by_cases hn : n ≤ N
    · exact hbase n hn
    · cases n with
      | zero =>
          exact False.elim (hn (Nat.zero_le N))
      | succ m =>
          have hNm : N ≤ m := by lia
          have hm : P m ≠ 0 ∧ (P m).Splits := ih m (Nat.lt_succ_self m)
          have hnext : F m * P m ≠ 0 ∧ (F m * P m).Splits :=
            isRealRooted_mul_of_isRealRooted (hfactor m hNm) hm
          simpa [Nat.succ_eq_add_one, hstep m hNm] using hnext

/-- Right-factor variant of `isRealRooted_of_product_factor_sequence`. -/
theorem isRealRooted_of_product_factor_right_sequence
    {P F : Nat → ℝ[X]}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hfactor : ∀ n : Nat, F n ≠ 0 ∧ (F n).Splits)
    (hstep : ∀ n : Nat, P (n + 1) = P n * F n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_factor_sequence hbase hfactor
    (fun n => by rw [hstep n, mul_comm])

/-- Right-factor variant of
`isRealRooted_of_product_factor_sequence_from`. -/
theorem isRealRooted_of_product_factor_right_sequence_from
    {P F : Nat → ℝ[X]}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hfactor : ∀ n : Nat, N ≤ n → F n ≠ 0 ∧ (F n).Splits)
    (hstep : ∀ n : Nat, N ≤ n → P (n + 1) = P n * F n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_factor_sequence_from N hbase hfactor
    (fun n hn => by rw [hstep n hn, mul_comm])

/-- A finite product of real linear factors is real-rooted. -/
theorem isRealRooted_finset_prod_X_sub_C
    {ι : Type*} (s : Finset ι) (root : ι → ℝ) :
    (∏ j ∈ s, (X - C (root j))) ≠ 0 ∧
      (∏ j ∈ s, (X - C (root j))).Splits := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | insert j s hjs hs =>
      have hlin := isRealRooted_X_sub_C (root j)
      have hmul :
          (X - C (root j)) * (∏ k ∈ s, (X - C (root k))) ≠ 0 ∧
            ((X - C (root j)) * (∏ k ∈ s, (X - C (root k)))).Splits :=
        isRealRooted_mul_of_isRealRooted hlin hs
      simpa [Finset.prod_insert hjs] using hmul

/-- Sequence shell for rows supplied as finite products of real linear factors. -/
theorem finiteLinearProductSequence_realRooted
    {P : Nat → ℝ[X]} {root : Nat → Nat → ℝ}
    (hroot : ∀ n : Nat,
      P n = ∏ j ∈ Finset.range n, (X - C (root n j))) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  intro n
  classical
  have hprod := isRealRooted_finset_prod_X_sub_C (Finset.range n) (root n)
  simpa [hroot n] using hprod

/-- Sequence shell for nonzero scalar multiples of finite products of real
linear factors. -/
theorem finiteLinearProductScalarSequence_realRooted
    {P : Nat → ℝ[X]} {c : Nat → ℝ} {rootCount : Nat → Nat}
    {roots : Nat → Nat → ℝ}
    (hc : ∀ n : Nat, c n ≠ 0)
    (hroot : ∀ n : Nat,
      P n = C (c n) *
        ∏ j ∈ Finset.range (rootCount n), (X - C (roots n j))) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  intro n
  classical
  have hprod := isRealRooted_finset_prod_X_sub_C
    (Finset.range (rootCount n)) (roots n)
  simpa [hroot n] using isRealRooted_C_mul_of_isRealRooted hprod (hc n)

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

/-- Tail-start sequence shell for identity product recurrences. -/
theorem isRealRooted_of_product_identity_sequence_from
    {P : Nat → ℝ[X]}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hstep : ∀ n : Nat, N ≤ n → P (n + 1) = P n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := fun n =>
  Nat.strong_induction_on n fun n ih => by
    by_cases hn : n ≤ N
    · exact hbase n hn
    · cases n with
      | zero =>
          exact False.elim (hn (Nat.zero_le N))
      | succ m =>
          have hNm : N ≤ m := by lia
          have hm : P m ≠ 0 ∧ (P m).Splits := ih m (Nat.lt_succ_self m)
          simpa [Nat.succ_eq_add_one, hstep m hNm] using hm

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

/-- Tail-start sequence shell for recurrences that multiply each row by `X`. -/
theorem isRealRooted_of_product_root_zero_sequence_from
    {P : Nat → ℝ[X]}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hstep : ∀ n : Nat, N ≤ n → P (n + 1) = X * P n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_factor_sequence_from N hbase
    (fun n _ => isRealRooted_X_sequence n) hstep

/-- Right-factor variant of
`isRealRooted_of_product_root_zero_sequence_from`. -/
theorem isRealRooted_of_product_root_zero_right_sequence_from
    {P : Nat → ℝ[X]}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hstep : ∀ n : Nat, N ≤ n → P (n + 1) = P n * X) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_factor_right_sequence_from N hbase
    (fun n _ => isRealRooted_X_sequence n) hstep

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

/-- Tail-start sequence shell for period-two product recurrences.  The
recurrence starts at row `N`, so the finite base interval must include rows
through `N + 1`. -/
theorem isRealRooted_of_product_period_two_sequence_from
    {P : Nat → ℝ[X]}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N + 1 → P n ≠ 0 ∧ (P n).Splits)
    (hstep : ∀ n : Nat, N ≤ n → P (n + 2) = P n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := fun n =>
  Nat.strong_induction_on n fun n ih => by
    by_cases hn : n ≤ N + 1
    · exact hbase n hn
    · cases n with
      | zero =>
          exact False.elim (hn (by lia))
      | succ m =>
          cases m with
          | zero =>
              exact False.elim (hn (by lia))
          | succ k =>
              have hNk : N ≤ k := by lia
              have hklt : k < k + 2 := Nat.lt_succ_of_lt (Nat.lt_succ_self k)
              have hk : P k ≠ 0 ∧ (P k).Splits := ih k hklt
              change P (k + 2) ≠ 0 ∧ (P (k + 2)).Splits
              simpa [hstep k hNk] using hk

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
    isRealRooted_mul_of_isRealRooted (hfactor n) (hquot n)
  simpa [hrow n] using hnext

/-- Right-factor variant of `isRealRooted_of_product_lift_sequence`. -/
theorem isRealRooted_of_product_lift_right_sequence
    {P Q F : Nat → ℝ[X]}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hfactor : ∀ n : Nat, F n ≠ 0 ∧ (F n).Splits)
    (hrow : ∀ n : Nat, P n = Q n * F n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_lift_sequence hquot hfactor
    (fun n => by rw [hrow n, mul_comm])

/-- Tail-start lift from a quotient sequence through row-wise real-rooted
left factors. -/
theorem isRealRooted_of_product_lift_sequence_from
    {P Q F : Nat → ℝ[X]}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hquot : ∀ n : Nat, N ≤ n → Q n ≠ 0 ∧ (Q n).Splits)
    (hfactor : ∀ n : Nat, N ≤ n → F n ≠ 0 ∧ (F n).Splits)
    (hrow : ∀ n : Nat, N ≤ n → P n = F n * Q n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  intro n
  by_cases hn : n ≤ N
  · exact hbase n hn
  · have hNn : N ≤ n := by lia
    have hnext : F n * Q n ≠ 0 ∧ (F n * Q n).Splits :=
      isRealRooted_mul_of_isRealRooted (hfactor n hNn) (hquot n hNn)
    simpa [hrow n hNn] using hnext

/-- Right-factor variant of `isRealRooted_of_product_lift_sequence_from`. -/
theorem isRealRooted_of_product_lift_right_sequence_from
    {P Q F : Nat → ℝ[X]}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hquot : ∀ n : Nat, N ≤ n → Q n ≠ 0 ∧ (Q n).Splits)
    (hfactor : ∀ n : Nat, N ≤ n → F n ≠ 0 ∧ (F n).Splits)
    (hrow : ∀ n : Nat, N ≤ n → P n = Q n * F n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_lift_sequence_from N hbase hquot hfactor
    (fun n hn => by rw [hrow n hn, mul_comm])

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

/-- Tail-start variant of `isRealRooted_of_X_lift_sequence`. -/
theorem isRealRooted_of_X_lift_sequence_from
    {P Q : Nat → ℝ[X]}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hquot : ∀ n : Nat, N ≤ n → Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, N ≤ n → P n = X * Q n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_lift_sequence_from N hbase hquot
    (fun n _ => isRealRooted_X_sequence n) hrow

/-- Right-factor variant of `isRealRooted_of_X_lift_sequence_from`. -/
theorem isRealRooted_of_X_lift_right_sequence_from
    {P Q : Nat → ℝ[X]}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hquot : ∀ n : Nat, N ≤ n → Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, N ≤ n → P n = Q n * X) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_lift_right_sequence_from N hbase hquot
    (fun n _ => isRealRooted_X_sequence n) hrow

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

/-- Tail-start variant of `isRealRooted_of_X_add_C_lift_sequence`. -/
theorem isRealRooted_of_X_add_C_lift_sequence_from
    {P Q : Nat → ℝ[X]} {t : Nat → ℝ}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hquot : ∀ n : Nat, N ≤ n → Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, N ≤ n → P n = (X + C (t n)) * Q n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_lift_sequence_from N hbase hquot
    (fun n _ => isRealRooted_X_add_C_one_sequence t n) hrow

/-- Right-factor variant of `isRealRooted_of_X_add_C_lift_sequence_from`. -/
theorem isRealRooted_of_X_add_C_lift_right_sequence_from
    {P Q : Nat → ℝ[X]} {t : Nat → ℝ}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hquot : ∀ n : Nat, N ≤ n → Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, N ≤ n → P n = Q n * (X + C (t n))) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_lift_right_sequence_from N hbase hquot
    (fun n _ => isRealRooted_X_add_C_one_sequence t n) hrow

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

/-- Tail-start variant of `isRealRooted_of_C_add_X_lift_sequence`. -/
theorem isRealRooted_of_C_add_X_lift_sequence_from
    {P Q : Nat → ℝ[X]} {t : Nat → ℝ}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hquot : ∀ n : Nat, N ≤ n → Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, N ≤ n → P n = (C (t n) + X) * Q n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_lift_sequence_from N hbase hquot
    (fun n _ => isRealRooted_C_add_X_one_sequence t n) hrow

/-- Right-factor variant of `isRealRooted_of_C_add_X_lift_sequence_from`. -/
theorem isRealRooted_of_C_add_X_lift_right_sequence_from
    {P Q : Nat → ℝ[X]} {t : Nat → ℝ}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hquot : ∀ n : Nat, N ≤ n → Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, N ≤ n → P n = Q n * (C (t n) + X)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_lift_right_sequence_from N hbase hquot
    (fun n _ => isRealRooted_C_add_X_one_sequence t n) hrow

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

/-- Tail-start variant of `isRealRooted_of_C_lift_sequence`. -/
theorem isRealRooted_of_C_lift_sequence_from
    {P Q : Nat → ℝ[X]} {c : Nat → ℝ}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hquot : ∀ n : Nat, N ≤ n → Q n ≠ 0 ∧ (Q n).Splits)
    (hc : ∀ n : Nat, N ≤ n → c n ≠ 0)
    (hrow : ∀ n : Nat, N ≤ n → P n = C (c n) * Q n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_lift_sequence_from N hbase hquot
    (fun n hn => isRealRooted_C (hc n hn)) hrow

/-- Right-factor variant of `isRealRooted_of_C_lift_sequence_from`. -/
theorem isRealRooted_of_C_lift_right_sequence_from
    {P Q : Nat → ℝ[X]} {c : Nat → ℝ}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hquot : ∀ n : Nat, N ≤ n → Q n ≠ 0 ∧ (Q n).Splits)
    (hc : ∀ n : Nat, N ≤ n → c n ≠ 0)
    (hrow : ∀ n : Nat, N ≤ n → P n = Q n * C (c n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_lift_right_sequence_from N hbase hquot
    (fun n hn => isRealRooted_C (hc n hn)) hrow

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

/-- Tail-start variant of
`isRealRooted_of_C_mul_X_add_C_lift_sequence`. -/
theorem isRealRooted_of_C_mul_X_add_C_lift_sequence_from
    {P Q : Nat → ℝ[X]} {s t : Nat → ℝ}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hquot : ∀ n : Nat, N ≤ n → Q n ≠ 0 ∧ (Q n).Splits)
    (hs : ∀ n : Nat, N ≤ n → s n ≠ 0)
    (hrow : ∀ n : Nat, N ≤ n → P n = (C (s n) * X + C (t n)) * Q n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_lift_sequence_from N hbase hquot
    (fun n hn => isRealRooted_C_mul_X_add_C (hs n hn)) hrow

/-- Right-factor variant of
`isRealRooted_of_C_mul_X_add_C_lift_sequence_from`. -/
theorem isRealRooted_of_C_mul_X_add_C_lift_right_sequence_from
    {P Q : Nat → ℝ[X]} {s t : Nat → ℝ}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hquot : ∀ n : Nat, N ≤ n → Q n ≠ 0 ∧ (Q n).Splits)
    (hs : ∀ n : Nat, N ≤ n → s n ≠ 0)
    (hrow : ∀ n : Nat, N ≤ n → P n = Q n * (C (s n) * X + C (t n))) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_lift_right_sequence_from N hbase hquot
    (fun n hn => isRealRooted_C_mul_X_add_C (hs n hn)) hrow

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

/-- Tail-start variant of
`isRealRooted_of_C_add_C_mul_X_lift_sequence`. -/
theorem isRealRooted_of_C_add_C_mul_X_lift_sequence_from
    {P Q : Nat → ℝ[X]} {s t : Nat → ℝ}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hquot : ∀ n : Nat, N ≤ n → Q n ≠ 0 ∧ (Q n).Splits)
    (hs : ∀ n : Nat, N ≤ n → s n ≠ 0)
    (hrow : ∀ n : Nat, N ≤ n → P n = (C (t n) + C (s n) * X) * Q n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_lift_sequence_from N hbase hquot
    (fun n hn => isRealRooted_C_add_C_mul_X (hs n hn)) hrow

/-- Right-factor variant of
`isRealRooted_of_C_add_C_mul_X_lift_sequence_from`. -/
theorem isRealRooted_of_C_add_C_mul_X_lift_right_sequence_from
    {P Q : Nat → ℝ[X]} {s t : Nat → ℝ}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hquot : ∀ n : Nat, N ≤ n → Q n ≠ 0 ∧ (Q n).Splits)
    (hs : ∀ n : Nat, N ≤ n → s n ≠ 0)
    (hrow : ∀ n : Nat, N ≤ n → P n = Q n * (C (t n) + C (s n) * X)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_lift_right_sequence_from N hbase hquot
    (fun n hn => isRealRooted_C_add_C_mul_X (hs n hn)) hrow

/-- Powers of the root-at-zero factor are real-rooted. -/
theorem isRealRooted_X_pow (n : Nat) :
    ((X : ℝ[X]) ^ n ≠ 0 ∧ (((X : ℝ[X]) ^ n).Splits)) :=
  isRealRooted_pow_of_isRealRooted isRealRooted_X n

/-- Powers of a nonzero scalar constant are real-rooted. -/
theorem isRealRooted_C_pow {a : ℝ} (ha : a ≠ 0) (n : Nat) :
    ((C a : ℝ[X]) ^ n ≠ 0 ∧ (((C a : ℝ[X]) ^ n).Splits)) :=
  isRealRooted_pow_of_isRealRooted (isRealRooted_C ha) n

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

/-- Tail-start variant of `isRealRooted_of_C_pow_lift_sequence`. -/
theorem isRealRooted_of_C_pow_lift_sequence_from
    {P Q : Nat → ℝ[X]} {c : Nat → ℝ} {m : Nat → Nat}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hquot : ∀ n : Nat, N ≤ n → Q n ≠ 0 ∧ (Q n).Splits)
    (hc : ∀ n : Nat, N ≤ n → c n ≠ 0)
    (hrow : ∀ n : Nat, N ≤ n → P n = (C (c n) : ℝ[X]) ^ (m n) * Q n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_lift_sequence_from N hbase hquot
    (fun n hn => isRealRooted_C_pow (hc n hn) (m n)) hrow

/-- Right-factor variant of `isRealRooted_of_C_pow_lift_sequence_from`. -/
theorem isRealRooted_of_C_pow_lift_right_sequence_from
    {P Q : Nat → ℝ[X]} {c : Nat → ℝ} {m : Nat → Nat}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hquot : ∀ n : Nat, N ≤ n → Q n ≠ 0 ∧ (Q n).Splits)
    (hc : ∀ n : Nat, N ≤ n → c n ≠ 0)
    (hrow : ∀ n : Nat, N ≤ n → P n = Q n * (C (c n) : ℝ[X]) ^ (m n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_lift_right_sequence_from N hbase hquot
    (fun n hn => isRealRooted_C_pow (hc n hn) (m n)) hrow

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

/-- Tail-start variant of `isRealRooted_of_X_pow_lift_sequence`. -/
theorem isRealRooted_of_X_pow_lift_sequence_from
    {P Q : Nat → ℝ[X]} {m : Nat → Nat}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hquot : ∀ n : Nat, N ≤ n → Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, N ≤ n → P n = X ^ (m n) * Q n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_lift_sequence_from N hbase hquot
    (fun n _ => isRealRooted_X_pow_sequence m n) hrow

/-- Right-factor variant of `isRealRooted_of_X_pow_lift_sequence_from`. -/
theorem isRealRooted_of_X_pow_lift_right_sequence_from
    {P Q : Nat → ℝ[X]} {m : Nat → Nat}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hquot : ∀ n : Nat, N ≤ n → Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, N ≤ n → P n = Q n * X ^ (m n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_lift_right_sequence_from N hbase hquot
    (fun n _ => isRealRooted_X_pow_sequence m n) hrow

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

/-- Tail-start variant of `isRealRooted_of_X_add_C_pow_lift_sequence`. -/
theorem isRealRooted_of_X_add_C_pow_lift_sequence_from
    {P Q : Nat → ℝ[X]} {t : ℝ} {m : Nat → Nat}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hquot : ∀ n : Nat, N ≤ n → Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, N ≤ n → P n = (X + C t) ^ (m n) * Q n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_lift_sequence_from N hbase hquot
    (fun n _ => isRealRooted_fixed_X_add_C_pow_sequence t m n) hrow

/-- Right-factor variant of `isRealRooted_of_X_add_C_pow_lift_sequence_from`. -/
theorem isRealRooted_of_X_add_C_pow_lift_right_sequence_from
    {P Q : Nat → ℝ[X]} {t : ℝ} {m : Nat → Nat}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hquot : ∀ n : Nat, N ≤ n → Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, N ≤ n → P n = Q n * (X + C t) ^ (m n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_lift_right_sequence_from N hbase hquot
    (fun n _ => isRealRooted_fixed_X_add_C_pow_sequence t m n) hrow

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

/-- Tail-start variant of
`isRealRooted_of_X_add_C_row_pow_lift_sequence`. -/
theorem isRealRooted_of_X_add_C_row_pow_lift_sequence_from
    {P Q : Nat → ℝ[X]} {t : Nat → ℝ} {m : Nat → Nat}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hquot : ∀ n : Nat, N ≤ n → Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, N ≤ n → P n = (X + C (t n)) ^ (m n) * Q n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_lift_sequence_from N hbase hquot
    (fun n _ => isRealRooted_X_add_C_pow_sequence t m n) hrow

/-- Right-factor variant of
`isRealRooted_of_X_add_C_row_pow_lift_sequence_from`. -/
theorem isRealRooted_of_X_add_C_row_pow_lift_right_sequence_from
    {P Q : Nat → ℝ[X]} {t : Nat → ℝ} {m : Nat → Nat}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hquot : ∀ n : Nat, N ≤ n → Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, N ≤ n → P n = Q n * (X + C (t n)) ^ (m n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_lift_right_sequence_from N hbase hquot
    (fun n _ => isRealRooted_X_add_C_pow_sequence t m n) hrow

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

/-- Tail-start variant of `isRealRooted_of_C_add_X_pow_lift_sequence`. -/
theorem isRealRooted_of_C_add_X_pow_lift_sequence_from
    {P Q : Nat → ℝ[X]} {t : Nat → ℝ} {m : Nat → Nat}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hquot : ∀ n : Nat, N ≤ n → Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, N ≤ n → P n = (C (t n) + X) ^ (m n) * Q n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_lift_sequence_from N hbase hquot
    (fun n _ => isRealRooted_C_add_X_pow_sequence t m n) hrow

/-- Right-factor variant of `isRealRooted_of_C_add_X_pow_lift_sequence_from`. -/
theorem isRealRooted_of_C_add_X_pow_lift_right_sequence_from
    {P Q : Nat → ℝ[X]} {t : Nat → ℝ} {m : Nat → Nat}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hquot : ∀ n : Nat, N ≤ n → Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, N ≤ n → P n = Q n * (C (t n) + X) ^ (m n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_lift_right_sequence_from N hbase hquot
    (fun n _ => isRealRooted_C_add_X_pow_sequence t m n) hrow

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

/-- Tail-start variant of
`isRealRooted_of_C_mul_X_add_C_pow_lift_sequence`. -/
theorem isRealRooted_of_C_mul_X_add_C_pow_lift_sequence_from
    {P Q : Nat → ℝ[X]} {s t : Nat → ℝ} {m : Nat → Nat}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hquot : ∀ n : Nat, N ≤ n → Q n ≠ 0 ∧ (Q n).Splits)
    (hs : ∀ n : Nat, N ≤ n → s n ≠ 0)
    (hrow : ∀ n : Nat,
      N ≤ n → P n = (C (s n) * X + C (t n)) ^ (m n) * Q n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_lift_sequence_from N hbase hquot
    (fun n hn => isRealRooted_C_mul_X_add_C_pow (hs n hn) (m n)) hrow

/-- Right-factor variant of
`isRealRooted_of_C_mul_X_add_C_pow_lift_sequence_from`. -/
theorem isRealRooted_of_C_mul_X_add_C_pow_lift_right_sequence_from
    {P Q : Nat → ℝ[X]} {s t : Nat → ℝ} {m : Nat → Nat}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hquot : ∀ n : Nat, N ≤ n → Q n ≠ 0 ∧ (Q n).Splits)
    (hs : ∀ n : Nat, N ≤ n → s n ≠ 0)
    (hrow : ∀ n : Nat,
      N ≤ n → P n = Q n * (C (s n) * X + C (t n)) ^ (m n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_lift_right_sequence_from N hbase hquot
    (fun n hn => isRealRooted_C_mul_X_add_C_pow (hs n hn) (m n)) hrow

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

/-- Tail-start variant of
`isRealRooted_of_C_add_C_mul_X_pow_lift_sequence`. -/
theorem isRealRooted_of_C_add_C_mul_X_pow_lift_sequence_from
    {P Q : Nat → ℝ[X]} {s t : Nat → ℝ} {m : Nat → Nat}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hquot : ∀ n : Nat, N ≤ n → Q n ≠ 0 ∧ (Q n).Splits)
    (hs : ∀ n : Nat, N ≤ n → s n ≠ 0)
    (hrow : ∀ n : Nat,
      N ≤ n → P n = (C (t n) + C (s n) * X) ^ (m n) * Q n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_lift_sequence_from N hbase hquot
    (fun n hn => isRealRooted_C_add_C_mul_X_pow (hs n hn) (m n)) hrow

/-- Right-factor variant of
`isRealRooted_of_C_add_C_mul_X_pow_lift_sequence_from`. -/
theorem isRealRooted_of_C_add_C_mul_X_pow_lift_right_sequence_from
    {P Q : Nat → ℝ[X]} {s t : Nat → ℝ} {m : Nat → Nat}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hquot : ∀ n : Nat, N ≤ n → Q n ≠ 0 ∧ (Q n).Splits)
    (hs : ∀ n : Nat, N ≤ n → s n ≠ 0)
    (hrow : ∀ n : Nat,
      N ≤ n → P n = Q n * (C (t n) + C (s n) * X) ^ (m n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_lift_right_sequence_from N hbase hquot
    (fun n hn => isRealRooted_C_add_C_mul_X_pow (hs n hn) (m n)) hrow

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
      isRealRooted_C_mul_of_isRealRooted isRealRooted_X (ha n)
    have hrow : (C (a n) * X) * Q n ≠ 0 ∧ ((C (a n) * X) * Q n).Splits :=
      isRealRooted_mul_of_isRealRooted hfactor (hquot n)
    simpa [hodd n, mul_assoc] using hrow
  exact isRealRooted_of_even_odd_sequence heven_realrooted hodd_realrooted

/-- One endpoint-quotient transition: first form `a+b`, then the next row is
`b+X(a+b)`. -/
theorem prec_endpoint_sum_then_X_step {a b : ℝ[X]}
    (hab : Prec a b)
    (ha_nonneg : HasNonnegCoeffs a) (hb_nonneg : HasNonnegCoeffs b)
    (hcop : IsCoprime b (X * (a + b))) :
    Prec (a + b) (b + X * (a + b)) := by
  have ha_pos : HasPosLeadingCoeff a := by
    rr_pos_lc using nonzero := left_ne_zero_of_prec hab
  have hb_pos : HasPosLeadingCoeff b := by
    rr_pos_lc using nonzero := right_ne_zero_of_prec hab
  have hsum_prec_raw : Prec (C (1 : ℝ) * a + C (1 : ℝ) * b) b :=
    prec_nonneg_combo_right hab ha_pos hb_pos zero_le_one zero_le_one (Or.inl zero_lt_one)
  have hsum_prec : Prec (a + b) b := by
    simpa using hsum_prec_raw
  have hsum_nonneg : HasNonnegCoeffs (a + b) := by
    rr_nonneg_coeffs
  have hsum_pos : HasPosLeadingCoeff (a + b) := by
    rr_pos_lc using nonzero := left_ne_zero_of_prec hsum_prec
  have hXsum_prec : Prec (a + b) (X * (a + b)) :=
    prec_mul_X_of_prec_of_nonneg
      (prec_refl (left_ne_zero_of_prec hsum_prec) (left_splits_of_prec hsum_prec))
      hsum_nonneg hsum_nonneg
  have hXsum_pos : HasPosLeadingCoeff (X * (a + b)) := by
    rr_pos_lc
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
  have ha_pos : HasPosLeadingCoeff a := by
    rr_pos_lc using nonzero := left_ne_zero_of_prec hab
  have hb_pos : HasPosLeadingCoeff b := by
    rr_pos_lc using nonzero := right_ne_zero_of_prec hab
  have hXa_prec : Prec a (X * a) :=
    prec_mul_X_of_prec_of_nonneg
      (prec_refl (left_ne_zero_of_prec hab) (left_splits_of_prec hab))
      ha_nonneg ha_nonneg
  have hXa_pos : HasPosLeadingCoeff (X * a) := by
    rr_pos_lc
  have hcombo : PosComboRealRooted b (X * a) :=
    PosComboRealRooted.of_commonLeftInterleaver hab hXa_prec hb_pos hXa_pos
  have hrr : b + X * a ≠ 0 ∧ (b + X * a).Splits :=
    PosComboRealRooted.isRealRooted_add hcombo
  have ha_sum_prec : Prec a (b + X * a) :=
    prec_add_of_prec_left hab hXa_prec hb_pos hXa_pos hrr.1 hrr.2 hcop
  have hsum_nonneg : HasNonnegCoeffs (b + X * a) := by
    rr_nonneg_coeffs
  have hsum_pos : HasPosLeadingCoeff (b + X * a) := by
    rr_pos_lc using nonzero := right_ne_zero_of_prec ha_sum_prec
  have hnext_raw :
      Prec (C (1 : ℝ) * a + C (1 : ℝ) * (b + X * a)) (b + X * a) :=
    prec_nonneg_combo_right ha_sum_prec ha_pos hsum_pos
      zero_le_one zero_le_one (Or.inl zero_lt_one)
  simpa [add_assoc] using hnext_raw

private def endpointPairPackage (A B : Nat → ℝ[X]) (n : Nat) : Prop :=
  Prec (A n) (B n) ∧ HasNonnegCoeffs (A n) ∧ HasNonnegCoeffs (B n)

private theorem prec_sequence_of_endpointPairPackage {A B : Nat → ℝ[X]}
    (hpack : ∀ n : Nat, endpointPairPackage A B n) :
    ∀ n : Nat, Prec (A n) (B n) :=
  fun n => (hpack n).1

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
  have hpack : ∀ n : Nat, endpointPairPackage A B n := by
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
          rw [hstepA n]
          rr_nonneg_coeffs
        have hB_nonneg_next : HasNonnegCoeffs (B (n + 1)) := by
          rw [hstepB n]
          rr_nonneg_coeffs
        exact ⟨hprec_next, hA_nonneg_next, hB_nonneg_next⟩
  exact prec_sequence_of_endpointPairPackage hpack

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
    ∀ n : Nat, (A n ≠ 0 ∧ (A n).Splits) ∧ (B n ≠ 0 ∧ (B n).Splits) :=
  isRealRooted_pair_sequence_of_prec_sequence <|
    prec_endpoint_sum_then_X_pair_sequence
      hbase hA0_nonneg hB0_nonneg hstepA hstepB hcop

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
  have hpack : ∀ n : Nat, endpointPairPackage A B n := by
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
          rw [hstepB n]
          rr_nonneg_coeffs
        have hA_nonneg_next : HasNonnegCoeffs (A (n + 1)) := by
          rw [hstepA n]
          rr_nonneg_coeffs
        exact ⟨hprec_next, hA_nonneg_next, hB_nonneg_next⟩
  exact prec_sequence_of_endpointPairPackage hpack

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
    ∀ n : Nat, (A n ≠ 0 ∧ (A n).Splits) ∧ (B n ≠ 0 ∧ (B n).Splits) :=
  isRealRooted_pair_sequence_of_prec_sequence <|
    prec_endpoint_X_then_sum_pair_sequence
      hbase hA0_nonneg hB0_nonneg hstepB hstepA hcop

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
  have heven : ∀ n : Nat, P (2 * n) ≠ 0 ∧ (P (2 * n)).Splits :=
    isRealRooted_of_X_add_C_pow_lift_sequence
      (P := fun n => P (2 * n)) (Q := A) (t := t) (m := mA)
      (left_isRealRooted_of_isRealRooted_pair_sequence hquot) hrowA
  have hodd : ∀ n : Nat, P (2 * n + 1) ≠ 0 ∧ (P (2 * n + 1)).Splits :=
    isRealRooted_of_X_add_C_pow_lift_sequence
      (P := fun n => P (2 * n + 1)) (Q := B) (t := t) (m := mB)
      (right_isRealRooted_of_isRealRooted_pair_sequence hquot) hrowB
  exact isRealRooted_of_even_odd_sequence heven hodd

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
  have heven : ∀ n : Nat, P (2 * n) ≠ 0 ∧ (P (2 * n)).Splits :=
    isRealRooted_of_X_add_C_pow_lift_sequence
      (P := fun n => P (2 * n)) (Q := A) (t := t) (m := mA)
      (left_isRealRooted_of_isRealRooted_pair_sequence hquot) hrowA
  have hodd : ∀ n : Nat, P (2 * n + 1) ≠ 0 ∧ (P (2 * n + 1)).Splits :=
    isRealRooted_of_X_add_C_pow_lift_sequence
      (P := fun n => P (2 * n + 1)) (Q := B) (t := t) (m := mB)
      (right_isRealRooted_of_isRealRooted_pair_sequence hquot) hrowB
  exact isRealRooted_of_even_odd_sequence heven hodd

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
  have heven : ∀ n : Nat, P (2 * n) ≠ 0 ∧ (P (2 * n)).Splits :=
    isRealRooted_of_X_add_C_pow_lift_sequence
      (P := fun n => P (2 * n)) (Q := B) (t := t) (m := mB)
      (right_isRealRooted_of_isRealRooted_pair_sequence hquot) hrowB
  have hodd : ∀ n : Nat, P (2 * n + 1) ≠ 0 ∧ (P (2 * n + 1)).Splits :=
    isRealRooted_of_X_add_C_pow_lift_sequence
      (P := fun n => P (2 * n + 1)) (Q := A) (t := t) (m := mA)
      (left_isRealRooted_of_isRealRooted_pair_sequence hquot) hrowA
  exact isRealRooted_of_even_odd_sequence heven hodd

/-- Sequence shell for first-order affine-product recurrences. -/
theorem isRealRooted_of_product_affine_sequence
    {P : Nat → ℝ[X]} {s t : Nat → ℝ}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hs : ∀ n : Nat, s n ≠ 0)
    (hstep : ∀ n : Nat, P (n + 1) = (C (s n) * X + C (t n)) * P n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_factor_sequence hbase
    (isRealRooted_C_mul_X_add_C_sequence hs) hstep

/-- Right-factor variant of `isRealRooted_of_product_affine_sequence`. -/
theorem isRealRooted_of_product_affine_right_sequence
    {P : Nat → ℝ[X]} {s t : Nat → ℝ}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hs : ∀ n : Nat, s n ≠ 0)
    (hstep : ∀ n : Nat, P (n + 1) = P n * (C (s n) * X + C (t n))) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_factor_right_sequence hbase
    (isRealRooted_C_mul_X_add_C_sequence hs) hstep

/-- Tail-start sequence shell for first-order affine-product recurrences. -/
theorem isRealRooted_of_product_affine_sequence_from
    {P : Nat → ℝ[X]} {s t : Nat → ℝ}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hs : ∀ n : Nat, s n ≠ 0)
    (hstep :
      ∀ n : Nat, N ≤ n → P (n + 1) = (C (s n) * X + C (t n)) * P n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_factor_sequence_from N hbase
    (fun n _ => isRealRooted_C_mul_X_add_C_sequence hs n) hstep

/-- Right-factor variant of
`isRealRooted_of_product_affine_sequence_from`. -/
theorem isRealRooted_of_product_affine_right_sequence_from
    {P : Nat → ℝ[X]} {s t : Nat → ℝ}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hs : ∀ n : Nat, s n ≠ 0)
    (hstep :
      ∀ n : Nat, N ≤ n → P (n + 1) = P n * (C (s n) * X + C (t n))) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_factor_right_sequence_from N hbase
    (fun n _ => isRealRooted_C_mul_X_add_C_sequence hs n) hstep

/-- Sequence shell for report-order affine factors `C t + C s * X`. -/
theorem isRealRooted_of_product_const_first_affine_sequence
    {P : Nat → ℝ[X]} {s t : Nat → ℝ}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hs : ∀ n : Nat, s n ≠ 0)
    (hstep : ∀ n : Nat, P (n + 1) = (C (t n) + C (s n) * X) * P n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_factor_sequence hbase
    (isRealRooted_C_add_C_mul_X_one_sequence hs) hstep

/-- Right-factor variant of `isRealRooted_of_product_const_first_affine_sequence`. -/
theorem isRealRooted_of_product_const_first_affine_right_sequence
    {P : Nat → ℝ[X]} {s t : Nat → ℝ}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hs : ∀ n : Nat, s n ≠ 0)
    (hstep : ∀ n : Nat, P (n + 1) = P n * (C (t n) + C (s n) * X)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_factor_right_sequence hbase
    (isRealRooted_C_add_C_mul_X_one_sequence hs) hstep

/-- Tail-start sequence shell for report-order affine factors
`C t + C s * X`. -/
theorem isRealRooted_of_product_const_first_affine_sequence_from
    {P : Nat → ℝ[X]} {s t : Nat → ℝ}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hs : ∀ n : Nat, s n ≠ 0)
    (hstep :
      ∀ n : Nat, N ≤ n → P (n + 1) = (C (t n) + C (s n) * X) * P n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_factor_sequence_from N hbase
    (fun n _ => isRealRooted_C_add_C_mul_X_one_sequence hs n) hstep

/-- Right-factor variant of
`isRealRooted_of_product_const_first_affine_sequence_from`. -/
theorem isRealRooted_of_product_const_first_affine_right_sequence_from
    {P : Nat → ℝ[X]} {s t : Nat → ℝ}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hs : ∀ n : Nat, s n ≠ 0)
    (hstep :
      ∀ n : Nat, N ≤ n → P (n + 1) = P n * (C (t n) + C (s n) * X)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_factor_right_sequence_from N hbase
    (fun n _ => isRealRooted_C_add_C_mul_X_one_sequence hs n) hstep

/-- Sequence shell for unit-slope factors `X + C t`. -/
theorem isRealRooted_of_product_X_add_C_sequence
    {P : Nat → ℝ[X]} {t : Nat → ℝ}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hstep : ∀ n : Nat, P (n + 1) = (X + C (t n)) * P n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_factor_sequence hbase
    (isRealRooted_X_add_C_one_sequence t) hstep

/-- Right-factor variant of `isRealRooted_of_product_X_add_C_sequence`. -/
theorem isRealRooted_of_product_X_add_C_right_sequence
    {P : Nat → ℝ[X]} {t : Nat → ℝ}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hstep : ∀ n : Nat, P (n + 1) = P n * (X + C (t n))) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_factor_right_sequence hbase
    (isRealRooted_X_add_C_one_sequence t) hstep

/-- Tail-start sequence shell for unit-slope factors `X + C t`. -/
theorem isRealRooted_of_product_X_add_C_sequence_from
    {P : Nat → ℝ[X]} {t : Nat → ℝ}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hstep : ∀ n : Nat, N ≤ n → P (n + 1) = (X + C (t n)) * P n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_factor_sequence_from N hbase
    (fun n _ => isRealRooted_X_add_C_one_sequence t n) hstep

/-- Right-factor variant of
`isRealRooted_of_product_X_add_C_sequence_from`. -/
theorem isRealRooted_of_product_X_add_C_right_sequence_from
    {P : Nat → ℝ[X]} {t : Nat → ℝ}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hstep : ∀ n : Nat, N ≤ n → P (n + 1) = P n * (X + C (t n))) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_factor_right_sequence_from N hbase
    (fun n _ => isRealRooted_X_add_C_one_sequence t n) hstep

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

/-- Tail-start sequence shell for constant-first unit-slope factors
`C t + X`. -/
theorem isRealRooted_of_product_C_add_X_sequence_from
    {P : Nat → ℝ[X]} {t : Nat → ℝ}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hstep : ∀ n : Nat, N ≤ n → P (n + 1) = (C (t n) + X) * P n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_factor_sequence_from N hbase
    (fun n _ => isRealRooted_C_add_X_one_sequence t n) hstep

/-- Right-factor variant of
`isRealRooted_of_product_C_add_X_sequence_from`. -/
theorem isRealRooted_of_product_C_add_X_right_sequence_from
    {P : Nat → ℝ[X]} {t : Nat → ℝ}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hstep : ∀ n : Nat, N ≤ n → P (n + 1) = P n * (C (t n) + X)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_factor_right_sequence_from N hbase
    (fun n _ => isRealRooted_C_add_X_one_sequence t n) hstep

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

/-- Tail-start sequence shell for product recurrences with factors `X ^ m_n`. -/
theorem isRealRooted_of_product_X_pow_sequence_from
    {P : Nat → ℝ[X]} {m : Nat → Nat}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hstep : ∀ n : Nat, N ≤ n → P (n + 1) = X ^ (m n) * P n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_factor_sequence_from N hbase
    (fun n _ => isRealRooted_X_pow_sequence m n) hstep

/-- Right-factor variant of `isRealRooted_of_product_X_pow_sequence_from`. -/
theorem isRealRooted_of_product_X_pow_right_sequence_from
    {P : Nat → ℝ[X]} {m : Nat → Nat}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hstep : ∀ n : Nat, N ≤ n → P (n + 1) = P n * X ^ (m n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_factor_right_sequence_from N hbase
    (fun n _ => isRealRooted_X_pow_sequence m n) hstep

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

/-- Tail-start sequence shell for product recurrences with nonzero
scalar-power factors. -/
theorem isRealRooted_of_product_C_pow_sequence_from
    {P : Nat → ℝ[X]} {c : Nat → ℝ} {m : Nat → Nat}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hc : ∀ n : Nat, c n ≠ 0)
    (hstep :
      ∀ n : Nat, N ≤ n → P (n + 1) = (C (c n) : ℝ[X]) ^ (m n) * P n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_factor_sequence_from N hbase
    (fun n _ => isRealRooted_C_pow_sequence hc m n) hstep

/-- Right-factor variant of
`isRealRooted_of_product_C_pow_sequence_from`. -/
theorem isRealRooted_of_product_C_pow_right_sequence_from
    {P : Nat → ℝ[X]} {c : Nat → ℝ} {m : Nat → Nat}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hc : ∀ n : Nat, c n ≠ 0)
    (hstep :
      ∀ n : Nat, N ≤ n → P (n + 1) = P n * (C (c n) : ℝ[X]) ^ (m n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_factor_right_sequence_from N hbase
    (fun n _ => isRealRooted_C_pow_sequence hc m n) hstep

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

/-- Tail-start sequence shell for product recurrences with factors
`(X + C t_n) ^ m_n`. -/
theorem isRealRooted_of_product_X_add_C_pow_sequence_from
    {P : Nat → ℝ[X]} {t : Nat → ℝ} {m : Nat → Nat}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hstep :
      ∀ n : Nat, N ≤ n → P (n + 1) = (X + C (t n)) ^ (m n) * P n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_factor_sequence_from N hbase
    (fun n _ => isRealRooted_X_add_C_pow_sequence t m n) hstep

/-- Right-factor variant of
`isRealRooted_of_product_X_add_C_pow_sequence_from`. -/
theorem isRealRooted_of_product_X_add_C_pow_right_sequence_from
    {P : Nat → ℝ[X]} {t : Nat → ℝ} {m : Nat → Nat}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hstep :
      ∀ n : Nat, N ≤ n → P (n + 1) = P n * (X + C (t n)) ^ (m n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_factor_right_sequence_from N hbase
    (fun n _ => isRealRooted_X_add_C_pow_sequence t m n) hstep

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

/-- Tail-start sequence shell for product recurrences with factors
`(C t_n + X) ^ m_n`. -/
theorem isRealRooted_of_product_C_add_X_pow_sequence_from
    {P : Nat → ℝ[X]} {t : Nat → ℝ} {m : Nat → Nat}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hstep :
      ∀ n : Nat, N ≤ n → P (n + 1) = (C (t n) + X) ^ (m n) * P n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_factor_sequence_from N hbase
    (fun n _ => isRealRooted_C_add_X_pow_sequence t m n) hstep

/-- Right-factor variant of
`isRealRooted_of_product_C_add_X_pow_sequence_from`. -/
theorem isRealRooted_of_product_C_add_X_pow_right_sequence_from
    {P : Nat → ℝ[X]} {t : Nat → ℝ} {m : Nat → Nat}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hstep :
      ∀ n : Nat, N ≤ n → P (n + 1) = P n * (C (t n) + X) ^ (m n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_factor_right_sequence_from N hbase
    (fun n _ => isRealRooted_C_add_X_pow_sequence t m n) hstep

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

/-- Tail-start sequence shell for product recurrences with powered affine
factors. -/
theorem isRealRooted_of_product_C_mul_X_add_C_pow_sequence_from
    {P : Nat → ℝ[X]} {s t : Nat → ℝ} {m : Nat → Nat}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hs : ∀ n : Nat, s n ≠ 0)
    (hstep :
      ∀ n : Nat, N ≤ n →
        P (n + 1) = (C (s n) * X + C (t n)) ^ (m n) * P n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_factor_sequence_from N hbase
    (fun n _ => isRealRooted_C_mul_X_add_C_pow_sequence hs m n) hstep

/-- Right-factor variant of
`isRealRooted_of_product_C_mul_X_add_C_pow_sequence_from`. -/
theorem isRealRooted_of_product_C_mul_X_add_C_pow_right_sequence_from
    {P : Nat → ℝ[X]} {s t : Nat → ℝ} {m : Nat → Nat}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hs : ∀ n : Nat, s n ≠ 0)
    (hstep :
      ∀ n : Nat, N ≤ n →
        P (n + 1) = P n * (C (s n) * X + C (t n)) ^ (m n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_factor_right_sequence_from N hbase
    (fun n _ => isRealRooted_C_mul_X_add_C_pow_sequence hs m n) hstep

/-- Tail-start sequence shell for product recurrences with powered
constant-first affine factors. -/
theorem isRealRooted_of_product_C_add_C_mul_X_pow_sequence_from
    {P : Nat → ℝ[X]} {s t : Nat → ℝ} {m : Nat → Nat}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hs : ∀ n : Nat, s n ≠ 0)
    (hstep :
      ∀ n : Nat, N ≤ n →
        P (n + 1) = (C (t n) + C (s n) * X) ^ (m n) * P n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_factor_sequence_from N hbase
    (fun n _ => isRealRooted_C_add_C_mul_X_pow_sequence hs m n) hstep

/-- Right-factor variant of
`isRealRooted_of_product_C_add_C_mul_X_pow_sequence_from`. -/
theorem isRealRooted_of_product_C_add_C_mul_X_pow_right_sequence_from
    {P : Nat → ℝ[X]} {s t : Nat → ℝ} {m : Nat → Nat}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hs : ∀ n : Nat, s n ≠ 0)
    (hstep :
      ∀ n : Nat, N ≤ n →
        P (n + 1) = P n * (C (t n) + C (s n) * X) ^ (m n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_factor_right_sequence_from N hbase
    (fun n _ => isRealRooted_C_add_C_mul_X_pow_sequence hs m n) hstep

/-- Sequence shell for scalar product recurrences. -/
theorem isRealRooted_of_product_scalar_sequence
    {P : Nat → ℝ[X]} {a : Nat → ℝ}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (ha : ∀ n : Nat, a n ≠ 0)
    (hstep : ∀ n : Nat, P (n + 1) = C (a n) * P n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_factor_sequence hbase (isRealRooted_C_sequence ha) hstep

/-- Right-factor variant of `isRealRooted_of_product_scalar_sequence`. -/
theorem isRealRooted_of_product_scalar_right_sequence
    {P : Nat → ℝ[X]} {a : Nat → ℝ}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (ha : ∀ n : Nat, a n ≠ 0)
    (hstep : ∀ n : Nat, P (n + 1) = P n * C (a n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_factor_right_sequence hbase
    (isRealRooted_C_sequence ha) hstep

/-- Tail-start sequence shell for scalar product recurrences. -/
theorem isRealRooted_of_product_scalar_sequence_from
    {P : Nat → ℝ[X]} {a : Nat → ℝ}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (ha : ∀ n : Nat, a n ≠ 0)
    (hstep : ∀ n : Nat, N ≤ n → P (n + 1) = C (a n) * P n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_factor_sequence_from N hbase
    (fun n _ => isRealRooted_C_sequence ha n) hstep

/-- Right-factor variant of
`isRealRooted_of_product_scalar_sequence_from`. -/
theorem isRealRooted_of_product_scalar_right_sequence_from
    {P : Nat → ℝ[X]} {a : Nat → ℝ}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (ha : ∀ n : Nat, a n ≠ 0)
    (hstep : ∀ n : Nat, N ≤ n → P (n + 1) = P n * C (a n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_factor_right_sequence_from N hbase
    (fun n _ => isRealRooted_C_sequence ha n) hstep

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
          simpa [hscalar n] using isRealRooted_C_mul_of_isRealRooted ih (ha n)
        have hnext :
            (F n * P (2 * n + 1) ≠ 0 ∧ (F n * P (2 * n + 1)).Splits) :=
          isRealRooted_mul_of_isRealRooted (hfactor n) hodd
        simpa [Nat.mul_succ, Nat.succ_eq_add_one, Nat.add_assoc] using
          (by simpa [hstep n] using hnext)
  have hodd : ∀ n : Nat, P (2 * n + 1) ≠ 0 ∧ (P (2 * n + 1)).Splits := by
    intro n
    simpa [hscalar n] using isRealRooted_C_mul_of_isRealRooted (heven n) (ha n)
  exact isRealRooted_of_even_odd_sequence heven hodd

/-- Right-factor variant of `isRealRooted_of_product_scalar_factor_sequence`. -/
theorem isRealRooted_of_product_scalar_factor_right_sequence
    {P F : Nat → ℝ[X]} {a : Nat → ℝ}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (ha : ∀ n : Nat, a n ≠ 0)
    (hfactor : ∀ n : Nat, F n ≠ 0 ∧ (F n).Splits)
    (hscalar : ∀ n : Nat, P (2 * n + 1) = C (a n) * P (2 * n))
    (hstep : ∀ n : Nat, P (2 * n + 2) = P (2 * n + 1) * F n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_scalar_factor_sequence hbase ha hfactor hscalar
    (fun n => by rw [hstep n, mul_comm])

/-- Right-scalar variant of `isRealRooted_of_product_scalar_factor_sequence`. -/
theorem isRealRooted_of_product_scalar_factor_scalar_right_sequence
    {P F : Nat → ℝ[X]} {a : Nat → ℝ}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (ha : ∀ n : Nat, a n ≠ 0)
    (hfactor : ∀ n : Nat, F n ≠ 0 ∧ (F n).Splits)
    (hscalar : ∀ n : Nat, P (2 * n + 1) = P (2 * n) * C (a n))
    (hstep : ∀ n : Nat, P (2 * n + 2) = F n * P (2 * n + 1)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_scalar_factor_sequence hbase ha hfactor
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
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_scalar_factor_right_sequence hbase ha hfactor
    (fun n => by rw [hscalar n, mul_comm]) hstep

/-- Tail-start sequence shell for degree-plateau scalar/product families with
supplied factors.

The parity recurrence starts at parity index `N`, so the finite base interval
contains rows through `2 * N`.  The odd row `2 * N + 1` is then produced by
the scalar step. -/
theorem isRealRooted_of_product_scalar_factor_sequence_from
    {P F : Nat → ℝ[X]} {a : Nat → ℝ}
    (N : Nat)
    (hbase : ∀ k : Nat, k ≤ 2 * N → P k ≠ 0 ∧ (P k).Splits)
    (ha : ∀ n : Nat, N ≤ n → a n ≠ 0)
    (hfactor : ∀ n : Nat, N ≤ n → F n ≠ 0 ∧ (F n).Splits)
    (hscalar : ∀ n : Nat, N ≤ n → P (2 * n + 1) = C (a n) * P (2 * n))
    (hstep : ∀ n : Nat, N ≤ n → P (2 * n + 2) = F n * P (2 * n + 1)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  have heven : ∀ n : Nat, P (2 * n) ≠ 0 ∧ (P (2 * n)).Splits := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih
    by_cases hn : n ≤ N
    · exact hbase (2 * n) (by lia)
    · cases n with
      | zero =>
          exact False.elim (hn (Nat.zero_le N))
      | succ m =>
          have hNm : N ≤ m := by lia
          have hm : P (2 * m) ≠ 0 ∧ (P (2 * m)).Splits :=
            ih m (Nat.lt_succ_self m)
          have hodd : P (2 * m + 1) ≠ 0 ∧ (P (2 * m + 1)).Splits := by
            simpa [hscalar m hNm] using
              isRealRooted_C_mul_of_isRealRooted hm (ha m hNm)
          have hnext :
              (F m * P (2 * m + 1) ≠ 0 ∧
                (F m * P (2 * m + 1)).Splits) :=
            isRealRooted_mul_of_isRealRooted (hfactor m hNm) hodd
          simpa [Nat.mul_succ, Nat.succ_eq_add_one, Nat.add_assoc] using
            (by simpa [hstep m hNm] using hnext)
  have hodd : ∀ n : Nat, P (2 * n + 1) ≠ 0 ∧ (P (2 * n + 1)).Splits := by
    intro n
    by_cases hn : n < N
    · exact hbase (2 * n + 1) (by lia)
    · have hNn : N ≤ n := by lia
      simpa [hscalar n hNn] using
        isRealRooted_C_mul_of_isRealRooted (heven n) (ha n hNn)
  exact isRealRooted_of_even_odd_sequence heven hodd

/-- Right-factor variant of
`isRealRooted_of_product_scalar_factor_sequence_from`. -/
theorem isRealRooted_of_product_scalar_factor_right_sequence_from
    {P F : Nat → ℝ[X]} {a : Nat → ℝ}
    (N : Nat)
    (hbase : ∀ k : Nat, k ≤ 2 * N → P k ≠ 0 ∧ (P k).Splits)
    (ha : ∀ n : Nat, N ≤ n → a n ≠ 0)
    (hfactor : ∀ n : Nat, N ≤ n → F n ≠ 0 ∧ (F n).Splits)
    (hscalar : ∀ n : Nat, N ≤ n → P (2 * n + 1) = C (a n) * P (2 * n))
    (hstep : ∀ n : Nat, N ≤ n → P (2 * n + 2) = P (2 * n + 1) * F n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_scalar_factor_sequence_from N hbase ha hfactor hscalar
    (fun n hn => by rw [hstep n hn, mul_comm])

/-- Right-scalar variant of
`isRealRooted_of_product_scalar_factor_sequence_from`. -/
theorem isRealRooted_of_product_scalar_factor_scalar_right_sequence_from
    {P F : Nat → ℝ[X]} {a : Nat → ℝ}
    (N : Nat)
    (hbase : ∀ k : Nat, k ≤ 2 * N → P k ≠ 0 ∧ (P k).Splits)
    (ha : ∀ n : Nat, N ≤ n → a n ≠ 0)
    (hfactor : ∀ n : Nat, N ≤ n → F n ≠ 0 ∧ (F n).Splits)
    (hscalar : ∀ n : Nat, N ≤ n → P (2 * n + 1) = P (2 * n) * C (a n))
    (hstep : ∀ n : Nat, N ≤ n → P (2 * n + 2) = F n * P (2 * n + 1)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_scalar_factor_sequence_from N hbase ha hfactor
    (fun n hn => by rw [hscalar n hn, mul_comm]) hstep

/-- Right-scalar/right-factor variant of
`isRealRooted_of_product_scalar_factor_sequence_from`. -/
theorem isRealRooted_of_product_scalar_factor_scalar_right_factor_right_sequence_from
    {P F : Nat → ℝ[X]} {a : Nat → ℝ}
    (N : Nat)
    (hbase : ∀ k : Nat, k ≤ 2 * N → P k ≠ 0 ∧ (P k).Splits)
    (ha : ∀ n : Nat, N ≤ n → a n ≠ 0)
    (hfactor : ∀ n : Nat, N ≤ n → F n ≠ 0 ∧ (F n).Splits)
    (hscalar : ∀ n : Nat, N ≤ n → P (2 * n + 1) = P (2 * n) * C (a n))
    (hstep : ∀ n : Nat, N ≤ n → P (2 * n + 2) = P (2 * n + 1) * F n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_scalar_factor_right_sequence_from N hbase ha hfactor
    (fun n hn => by rw [hscalar n hn, mul_comm]) hstep

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

/-- Tail-start variant of `isRealRooted_of_product_scalar_linear_sequence`. -/
theorem isRealRooted_of_product_scalar_linear_sequence_from
    {P : Nat → ℝ[X]} {a b : Nat → ℝ}
    (N : Nat)
    (hbase : ∀ k : Nat, k ≤ 2 * N → P k ≠ 0 ∧ (P k).Splits)
    (ha : ∀ n : Nat, N ≤ n → a n ≠ 0)
    (hscalar : ∀ n : Nat, N ≤ n → P (2 * n + 1) = C (a n) * P (2 * n))
    (hlinear :
      ∀ n : Nat, N ≤ n → P (2 * n + 2) = (X + C (b n)) * P (2 * n + 1)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_scalar_factor_sequence_from N hbase ha
    (fun n _ => isRealRooted_X_add_C_one_sequence b n) hscalar hlinear

/-- Right-factor variant of
`isRealRooted_of_product_scalar_linear_sequence_from`. -/
theorem isRealRooted_of_product_scalar_linear_right_sequence_from
    {P : Nat → ℝ[X]} {a b : Nat → ℝ}
    (N : Nat)
    (hbase : ∀ k : Nat, k ≤ 2 * N → P k ≠ 0 ∧ (P k).Splits)
    (ha : ∀ n : Nat, N ≤ n → a n ≠ 0)
    (hscalar : ∀ n : Nat, N ≤ n → P (2 * n + 1) = C (a n) * P (2 * n))
    (hlinear :
      ∀ n : Nat, N ≤ n → P (2 * n + 2) = P (2 * n + 1) * (X + C (b n))) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_scalar_factor_right_sequence_from N hbase ha
    (fun n _ => isRealRooted_X_add_C_one_sequence b n) hscalar hlinear

/-- Right-scalar variant of
`isRealRooted_of_product_scalar_linear_sequence_from`. -/
theorem isRealRooted_of_product_scalar_linear_scalar_right_sequence_from
    {P : Nat → ℝ[X]} {a b : Nat → ℝ}
    (N : Nat)
    (hbase : ∀ k : Nat, k ≤ 2 * N → P k ≠ 0 ∧ (P k).Splits)
    (ha : ∀ n : Nat, N ≤ n → a n ≠ 0)
    (hscalar : ∀ n : Nat, N ≤ n → P (2 * n + 1) = P (2 * n) * C (a n))
    (hlinear :
      ∀ n : Nat, N ≤ n → P (2 * n + 2) = (X + C (b n)) * P (2 * n + 1)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_scalar_factor_scalar_right_sequence_from N hbase ha
    (fun n _ => isRealRooted_X_add_C_one_sequence b n) hscalar hlinear

/-- Right-scalar/right-factor variant of
`isRealRooted_of_product_scalar_linear_sequence_from`. -/
theorem isRealRooted_of_product_scalar_linear_scalar_right_linear_right_sequence_from
    {P : Nat → ℝ[X]} {a b : Nat → ℝ}
    (N : Nat)
    (hbase : ∀ k : Nat, k ≤ 2 * N → P k ≠ 0 ∧ (P k).Splits)
    (ha : ∀ n : Nat, N ≤ n → a n ≠ 0)
    (hscalar : ∀ n : Nat, N ≤ n → P (2 * n + 1) = P (2 * n) * C (a n))
    (hlinear :
      ∀ n : Nat, N ≤ n → P (2 * n + 2) = P (2 * n + 1) * (X + C (b n))) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_scalar_factor_scalar_right_factor_right_sequence_from
    N hbase ha (fun n _ => isRealRooted_X_add_C_one_sequence b n)
    hscalar hlinear

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

/-- Tail-start variant of
`isRealRooted_of_product_scalar_C_add_X_sequence`. -/
theorem isRealRooted_of_product_scalar_C_add_X_sequence_from
    {P : Nat → ℝ[X]} {a b : Nat → ℝ}
    (N : Nat)
    (hbase : ∀ k : Nat, k ≤ 2 * N → P k ≠ 0 ∧ (P k).Splits)
    (ha : ∀ n : Nat, N ≤ n → a n ≠ 0)
    (hscalar : ∀ n : Nat, N ≤ n → P (2 * n + 1) = C (a n) * P (2 * n))
    (hlinear :
      ∀ n : Nat, N ≤ n → P (2 * n + 2) = (C (b n) + X) * P (2 * n + 1)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_scalar_factor_sequence_from N hbase ha
    (fun n _ => isRealRooted_C_add_X_one_sequence b n) hscalar hlinear

/-- Right-factor variant of
`isRealRooted_of_product_scalar_C_add_X_sequence_from`. -/
theorem isRealRooted_of_product_scalar_C_add_X_right_sequence_from
    {P : Nat → ℝ[X]} {a b : Nat → ℝ}
    (N : Nat)
    (hbase : ∀ k : Nat, k ≤ 2 * N → P k ≠ 0 ∧ (P k).Splits)
    (ha : ∀ n : Nat, N ≤ n → a n ≠ 0)
    (hscalar : ∀ n : Nat, N ≤ n → P (2 * n + 1) = C (a n) * P (2 * n))
    (hlinear :
      ∀ n : Nat, N ≤ n → P (2 * n + 2) = P (2 * n + 1) * (C (b n) + X)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_scalar_factor_right_sequence_from N hbase ha
    (fun n _ => isRealRooted_C_add_X_one_sequence b n) hscalar hlinear

/-- Right-scalar variant of
`isRealRooted_of_product_scalar_C_add_X_sequence_from`. -/
theorem isRealRooted_of_product_scalar_C_add_X_scalar_right_sequence_from
    {P : Nat → ℝ[X]} {a b : Nat → ℝ}
    (N : Nat)
    (hbase : ∀ k : Nat, k ≤ 2 * N → P k ≠ 0 ∧ (P k).Splits)
    (ha : ∀ n : Nat, N ≤ n → a n ≠ 0)
    (hscalar : ∀ n : Nat, N ≤ n → P (2 * n + 1) = P (2 * n) * C (a n))
    (hlinear :
      ∀ n : Nat, N ≤ n → P (2 * n + 2) = (C (b n) + X) * P (2 * n + 1)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_scalar_factor_scalar_right_sequence_from N hbase ha
    (fun n _ => isRealRooted_C_add_X_one_sequence b n) hscalar hlinear

/-- Right-scalar/right-factor variant of
`isRealRooted_of_product_scalar_C_add_X_sequence_from`. -/
theorem isRealRooted_of_product_scalar_C_add_X_scalar_right_linear_right_sequence_from
    {P : Nat → ℝ[X]} {a b : Nat → ℝ}
    (N : Nat)
    (hbase : ∀ k : Nat, k ≤ 2 * N → P k ≠ 0 ∧ (P k).Splits)
    (ha : ∀ n : Nat, N ≤ n → a n ≠ 0)
    (hscalar : ∀ n : Nat, N ≤ n → P (2 * n + 1) = P (2 * n) * C (a n))
    (hlinear :
      ∀ n : Nat, N ≤ n → P (2 * n + 2) = P (2 * n + 1) * (C (b n) + X)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_scalar_factor_scalar_right_factor_right_sequence_from
    N hbase ha (fun n _ => isRealRooted_C_add_X_one_sequence b n)
    hscalar hlinear

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

/-- Tail-start variant of
`isRealRooted_of_product_scalar_X_pow_sequence`. -/
theorem isRealRooted_of_product_scalar_X_pow_sequence_from
    {P : Nat → ℝ[X]} {a : Nat → ℝ} {m : Nat → Nat}
    (N : Nat)
    (hbase : ∀ k : Nat, k ≤ 2 * N → P k ≠ 0 ∧ (P k).Splits)
    (ha : ∀ n : Nat, N ≤ n → a n ≠ 0)
    (hscalar : ∀ n : Nat, N ≤ n → P (2 * n + 1) = C (a n) * P (2 * n))
    (hstep : ∀ n : Nat, N ≤ n → P (2 * n + 2) = X ^ (m n) * P (2 * n + 1)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_scalar_factor_sequence_from N hbase ha
    (fun n _ => isRealRooted_X_pow_sequence m n) hscalar hstep

/-- Right-factor variant of
`isRealRooted_of_product_scalar_X_pow_sequence_from`. -/
theorem isRealRooted_of_product_scalar_X_pow_right_sequence_from
    {P : Nat → ℝ[X]} {a : Nat → ℝ} {m : Nat → Nat}
    (N : Nat)
    (hbase : ∀ k : Nat, k ≤ 2 * N → P k ≠ 0 ∧ (P k).Splits)
    (ha : ∀ n : Nat, N ≤ n → a n ≠ 0)
    (hscalar : ∀ n : Nat, N ≤ n → P (2 * n + 1) = C (a n) * P (2 * n))
    (hstep : ∀ n : Nat, N ≤ n → P (2 * n + 2) = P (2 * n + 1) * X ^ (m n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_scalar_factor_right_sequence_from N hbase ha
    (fun n _ => isRealRooted_X_pow_sequence m n) hscalar hstep

/-- Right-scalar variant of
`isRealRooted_of_product_scalar_X_pow_sequence_from`. -/
theorem isRealRooted_of_product_scalar_X_pow_scalar_right_sequence_from
    {P : Nat → ℝ[X]} {a : Nat → ℝ} {m : Nat → Nat}
    (N : Nat)
    (hbase : ∀ k : Nat, k ≤ 2 * N → P k ≠ 0 ∧ (P k).Splits)
    (ha : ∀ n : Nat, N ≤ n → a n ≠ 0)
    (hscalar : ∀ n : Nat, N ≤ n → P (2 * n + 1) = P (2 * n) * C (a n))
    (hstep : ∀ n : Nat, N ≤ n → P (2 * n + 2) = X ^ (m n) * P (2 * n + 1)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_scalar_factor_scalar_right_sequence_from N hbase ha
    (fun n _ => isRealRooted_X_pow_sequence m n) hscalar hstep

/-- Right-scalar/right-factor variant of
`isRealRooted_of_product_scalar_X_pow_sequence_from`. -/
theorem isRealRooted_of_product_scalar_X_pow_scalar_right_factor_right_sequence_from
    {P : Nat → ℝ[X]} {a : Nat → ℝ} {m : Nat → Nat}
    (N : Nat)
    (hbase : ∀ k : Nat, k ≤ 2 * N → P k ≠ 0 ∧ (P k).Splits)
    (ha : ∀ n : Nat, N ≤ n → a n ≠ 0)
    (hscalar : ∀ n : Nat, N ≤ n → P (2 * n + 1) = P (2 * n) * C (a n))
    (hstep : ∀ n : Nat, N ≤ n → P (2 * n + 2) = P (2 * n + 1) * X ^ (m n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_scalar_factor_scalar_right_factor_right_sequence_from
    N hbase ha (fun n _ => isRealRooted_X_pow_sequence m n) hscalar hstep

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

/-- Tail-start variant of
`isRealRooted_of_product_scalar_X_add_C_pow_sequence`. -/
theorem isRealRooted_of_product_scalar_X_add_C_pow_sequence_from
    {P : Nat → ℝ[X]} {a b : Nat → ℝ} {m : Nat → Nat}
    (N : Nat)
    (hbase : ∀ k : Nat, k ≤ 2 * N → P k ≠ 0 ∧ (P k).Splits)
    (ha : ∀ n : Nat, N ≤ n → a n ≠ 0)
    (hscalar : ∀ n : Nat, N ≤ n → P (2 * n + 1) = C (a n) * P (2 * n))
    (hstep : ∀ n : Nat, N ≤ n →
      P (2 * n + 2) = (X + C (b n)) ^ (m n) * P (2 * n + 1)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_scalar_factor_sequence_from N hbase ha
    (fun n _ => isRealRooted_X_add_C_pow_sequence b m n) hscalar hstep

/-- Right-factor variant of
`isRealRooted_of_product_scalar_X_add_C_pow_sequence_from`. -/
theorem isRealRooted_of_product_scalar_X_add_C_pow_right_sequence_from
    {P : Nat → ℝ[X]} {a b : Nat → ℝ} {m : Nat → Nat}
    (N : Nat)
    (hbase : ∀ k : Nat, k ≤ 2 * N → P k ≠ 0 ∧ (P k).Splits)
    (ha : ∀ n : Nat, N ≤ n → a n ≠ 0)
    (hscalar : ∀ n : Nat, N ≤ n → P (2 * n + 1) = C (a n) * P (2 * n))
    (hstep : ∀ n : Nat, N ≤ n →
      P (2 * n + 2) = P (2 * n + 1) * (X + C (b n)) ^ (m n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_scalar_factor_right_sequence_from N hbase ha
    (fun n _ => isRealRooted_X_add_C_pow_sequence b m n) hscalar hstep

/-- Right-scalar variant of
`isRealRooted_of_product_scalar_X_add_C_pow_sequence_from`. -/
theorem isRealRooted_of_product_scalar_X_add_C_pow_scalar_right_sequence_from
    {P : Nat → ℝ[X]} {a b : Nat → ℝ} {m : Nat → Nat}
    (N : Nat)
    (hbase : ∀ k : Nat, k ≤ 2 * N → P k ≠ 0 ∧ (P k).Splits)
    (ha : ∀ n : Nat, N ≤ n → a n ≠ 0)
    (hscalar : ∀ n : Nat, N ≤ n → P (2 * n + 1) = P (2 * n) * C (a n))
    (hstep : ∀ n : Nat, N ≤ n →
      P (2 * n + 2) = (X + C (b n)) ^ (m n) * P (2 * n + 1)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_scalar_factor_scalar_right_sequence_from N hbase ha
    (fun n _ => isRealRooted_X_add_C_pow_sequence b m n) hscalar hstep

/-- Right-scalar/right-factor variant of
`isRealRooted_of_product_scalar_X_add_C_pow_sequence_from`. -/
theorem isRealRooted_of_product_scalar_X_add_C_pow_scalar_right_factor_right_sequence_from
    {P : Nat → ℝ[X]} {a b : Nat → ℝ} {m : Nat → Nat}
    (N : Nat)
    (hbase : ∀ k : Nat, k ≤ 2 * N → P k ≠ 0 ∧ (P k).Splits)
    (ha : ∀ n : Nat, N ≤ n → a n ≠ 0)
    (hscalar : ∀ n : Nat, N ≤ n → P (2 * n + 1) = P (2 * n) * C (a n))
    (hstep : ∀ n : Nat, N ≤ n →
      P (2 * n + 2) = P (2 * n + 1) * (X + C (b n)) ^ (m n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_scalar_factor_scalar_right_factor_right_sequence_from
    N hbase ha (fun n _ => isRealRooted_X_add_C_pow_sequence b m n)
    hscalar hstep

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

/-- Tail-start variant of
`isRealRooted_of_product_scalar_C_add_X_pow_sequence`. -/
theorem isRealRooted_of_product_scalar_C_add_X_pow_sequence_from
    {P : Nat → ℝ[X]} {a b : Nat → ℝ} {m : Nat → Nat}
    (N : Nat)
    (hbase : ∀ k : Nat, k ≤ 2 * N → P k ≠ 0 ∧ (P k).Splits)
    (ha : ∀ n : Nat, N ≤ n → a n ≠ 0)
    (hscalar : ∀ n : Nat, N ≤ n → P (2 * n + 1) = C (a n) * P (2 * n))
    (hstep : ∀ n : Nat, N ≤ n →
      P (2 * n + 2) = (C (b n) + X) ^ (m n) * P (2 * n + 1)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_scalar_factor_sequence_from N hbase ha
    (fun n _ => isRealRooted_C_add_X_pow_sequence b m n) hscalar hstep

/-- Right-factor variant of
`isRealRooted_of_product_scalar_C_add_X_pow_sequence_from`. -/
theorem isRealRooted_of_product_scalar_C_add_X_pow_right_sequence_from
    {P : Nat → ℝ[X]} {a b : Nat → ℝ} {m : Nat → Nat}
    (N : Nat)
    (hbase : ∀ k : Nat, k ≤ 2 * N → P k ≠ 0 ∧ (P k).Splits)
    (ha : ∀ n : Nat, N ≤ n → a n ≠ 0)
    (hscalar : ∀ n : Nat, N ≤ n → P (2 * n + 1) = C (a n) * P (2 * n))
    (hstep : ∀ n : Nat, N ≤ n →
      P (2 * n + 2) = P (2 * n + 1) * (C (b n) + X) ^ (m n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_scalar_factor_right_sequence_from N hbase ha
    (fun n _ => isRealRooted_C_add_X_pow_sequence b m n) hscalar hstep

/-- Right-scalar variant of
`isRealRooted_of_product_scalar_C_add_X_pow_sequence_from`. -/
theorem isRealRooted_of_product_scalar_C_add_X_pow_scalar_right_sequence_from
    {P : Nat → ℝ[X]} {a b : Nat → ℝ} {m : Nat → Nat}
    (N : Nat)
    (hbase : ∀ k : Nat, k ≤ 2 * N → P k ≠ 0 ∧ (P k).Splits)
    (ha : ∀ n : Nat, N ≤ n → a n ≠ 0)
    (hscalar : ∀ n : Nat, N ≤ n → P (2 * n + 1) = P (2 * n) * C (a n))
    (hstep : ∀ n : Nat, N ≤ n →
      P (2 * n + 2) = (C (b n) + X) ^ (m n) * P (2 * n + 1)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_scalar_factor_scalar_right_sequence_from N hbase ha
    (fun n _ => isRealRooted_C_add_X_pow_sequence b m n) hscalar hstep

/-- Right-scalar/right-factor variant of
`isRealRooted_of_product_scalar_C_add_X_pow_sequence_from`. -/
theorem isRealRooted_of_product_scalar_C_add_X_pow_scalar_right_factor_right_sequence_from
    {P : Nat → ℝ[X]} {a b : Nat → ℝ} {m : Nat → Nat}
    (N : Nat)
    (hbase : ∀ k : Nat, k ≤ 2 * N → P k ≠ 0 ∧ (P k).Splits)
    (ha : ∀ n : Nat, N ≤ n → a n ≠ 0)
    (hscalar : ∀ n : Nat, N ≤ n → P (2 * n + 1) = P (2 * n) * C (a n))
    (hstep : ∀ n : Nat, N ≤ n →
      P (2 * n + 2) = P (2 * n + 1) * (C (b n) + X) ^ (m n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_scalar_factor_scalar_right_factor_right_sequence_from
    N hbase ha (fun n _ => isRealRooted_C_add_X_pow_sequence b m n)
    hscalar hstep

namespace Tactic

open Lean
open Lean.Elab.Tactic
open Lean.Meta

syntax (name := rr_product_C_named)
  "rr_product_C" " using "
    "scalar_ne" ":=" term :
  tactic

syntax (name := rr_product_C_auto) "rr_product_C_auto" : tactic

syntax (name := rr_product_C_pow_named)
  "rr_product_C_pow" " using "
    "scalar_ne" ":=" term ","
    "exponent" ":=" term :
  tactic

syntax (name := rr_product_C_pow_auto_named)
  "rr_product_C_pow_auto" " using "
    "exponent" ":=" term :
  tactic

syntax (name := rr_product_X_named) "rr_product_X" : tactic

syntax (name := rr_product_X_pow_named)
  "rr_product_X_pow" " using "
    "exponent" ":=" term :
  tactic

syntax (name := rr_product_X_add_C_named)
  "rr_product_X_add_C" " using "
    "constant" ":=" term :
  tactic

syntax (name := rr_product_X_add_C_pow_named)
  "rr_product_X_add_C_pow" " using "
    "constant" ":=" term ","
    "exponent" ":=" term :
  tactic

syntax (name := rr_product_C_add_X_named)
  "rr_product_C_add_X" " using "
    "constant" ":=" term :
  tactic

syntax (name := rr_product_C_add_X_pow_named)
  "rr_product_C_add_X_pow" " using "
    "constant" ":=" term ","
    "exponent" ":=" term :
  tactic

syntax (name := rr_product_affine_named)
  "rr_product_affine" " using "
    "slope_ne" ":=" term :
  tactic

syntax (name := rr_product_affine_auto) "rr_product_affine_auto" : tactic

syntax (name := rr_product_affine_pow_named)
  "rr_product_affine_pow" " using "
    "slope_ne" ":=" term ","
    "exponent" ":=" term :
  tactic

syntax (name := rr_product_affine_pow_auto_named)
  "rr_product_affine_pow_auto" " using "
    "exponent" ":=" term :
  tactic

syntax (name := rr_product_const_first_affine_named)
  "rr_product_const_first_affine" " using "
    "slope_ne" ":=" term :
  tactic

syntax (name := rr_product_const_first_affine_auto)
  "rr_product_const_first_affine_auto" :
  tactic

syntax (name := rr_product_const_first_affine_pow_named)
  "rr_product_const_first_affine_pow" " using "
    "slope_ne" ":=" term ","
    "exponent" ":=" term :
  tactic

syntax (name := rr_product_const_first_affine_pow_auto_named)
  "rr_product_const_first_affine_pow_auto" " using "
    "exponent" ":=" term :
  tactic

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
    ("cutoff" ":=" term ",")?
    "recurrence" ":=" term :
  tactic

syntax (name := rr_product_factor_sequence)
  "rr_product_factor_sequence" " using " term ", " term ", " term :
  tactic

syntax (name := rr_affine_product_sequence_named)
  "rr_affine_product_sequence" " using " "formula" ":=" term :
  tactic

syntax (name := rr_j1_factorable_lag3_sequence_realrooted_named)
  "rr_j1_factorable_lag3_sequence_realrooted" " using "
    "scalar_ne_zero" ":=" term ","
    "root_grid" ":=" term :
  tactic

syntax (name := rr_product_identity_sequence_named)
  "rr_product_identity_sequence" " using "
    "base" ":=" term ","
    ("cutoff" ":=" term ",")?
    "recurrence" ":=" term :
  tactic

syntax (name := rr_product_identity_sequence)
  "rr_product_identity_sequence" " using " term ", " term :
  tactic

syntax (name := rr_product_root_zero_sequence_named)
  "rr_product_root_zero_sequence" " using "
    "base" ":=" term ","
    ("cutoff" ":=" term ",")?
    "recurrence" ":=" term :
  tactic

syntax (name := rr_product_root_zero_sequence)
  "rr_product_root_zero_sequence" " using " term ", " term :
  tactic

syntax (name := rr_product_period_two_sequence_named)
  "rr_product_period_two_sequence" " using "
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "recurrence" ":=" term :
  tactic

syntax (name := rr_product_period_two_sequence_cutoff_named)
  "rr_product_period_two_sequence" " using "
    "base" ":=" term ","
    "cutoff" ":=" term ","
    "recurrence" ":=" term :
  tactic

syntax (name := rr_product_period_two_sequence)
  "rr_product_period_two_sequence" " using " term ", " term ", " term :
  tactic

syntax (name := rr_product_lift_sequence_named)
  "rr_product_lift_sequence" " using "
    "quotient_realrooted" ":=" term ","
    "factor_realrooted" ":=" term ","
    "factorization" ":=" term :
  tactic

syntax (name := rr_product_lift_sequence_cutoff_named)
  "rr_product_lift_sequence" " using "
    "base" ":=" term ","
    "quotient_realrooted" ":=" term ","
    "factor_realrooted" ":=" term ","
    "cutoff" ":=" term ","
    "factorization" ":=" term :
  tactic

syntax (name := rr_product_lift_sequence)
  "rr_product_lift_sequence" " using " term ", " term ", " term :
  tactic

syntax (name := rr_product_lift_sequence_auto_named)
  "rr_product_lift_sequence_auto" " using "
    "quotient_realrooted" ":=" term ","
    "factorization" ":=" term :
  tactic

syntax (name := rr_product_lift_sequence_auto_cutoff_named)
  "rr_product_lift_sequence_auto" " using "
    "base" ":=" term ","
    "quotient_realrooted" ":=" term ","
    "cutoff" ":=" term ","
    "factorization" ":=" term :
  tactic

syntax (name := rr_product_lift_X_sequence_named)
  "rr_product_lift_X_sequence" " using "
    "quotient_realrooted" ":=" term ","
    "factorization" ":=" term :
  tactic

syntax (name := rr_product_lift_X_sequence_cutoff_named)
  "rr_product_lift_X_sequence" " using "
    "base" ":=" term ","
    "quotient_realrooted" ":=" term ","
    "cutoff" ":=" term ","
    "factorization" ":=" term :
  tactic

syntax (name := rr_product_lift_X_add_C_sequence_named)
  "rr_product_lift_X_add_C_sequence" " using "
    "quotient_realrooted" ":=" term ","
    "factorization" ":=" term :
  tactic

syntax (name := rr_product_lift_X_add_C_sequence_cutoff_named)
  "rr_product_lift_X_add_C_sequence" " using "
    "base" ":=" term ","
    "quotient_realrooted" ":=" term ","
    "cutoff" ":=" term ","
    "factorization" ":=" term :
  tactic

syntax (name := rr_product_lift_C_add_X_sequence_named)
  "rr_product_lift_C_add_X_sequence" " using "
    "quotient_realrooted" ":=" term ","
    "factorization" ":=" term :
  tactic

syntax (name := rr_product_lift_C_add_X_sequence_cutoff_named)
  "rr_product_lift_C_add_X_sequence" " using "
    "base" ":=" term ","
    "quotient_realrooted" ":=" term ","
    "cutoff" ":=" term ","
    "factorization" ":=" term :
  tactic

syntax (name := rr_product_lift_C_sequence_named)
  "rr_product_lift_C_sequence" " using "
    "quotient_realrooted" ":=" term ","
    "scalar_ne" ":=" term ","
    "factorization" ":=" term :
  tactic

syntax (name := rr_product_lift_C_sequence_cutoff_named)
  "rr_product_lift_C_sequence" " using "
    "base" ":=" term ","
    "quotient_realrooted" ":=" term ","
    "scalar_ne" ":=" term ","
    "cutoff" ":=" term ","
    "factorization" ":=" term :
  tactic

syntax (name := rr_product_lift_C_sequence_auto_named)
  "rr_product_lift_C_sequence_auto" " using "
    "quotient_realrooted" ":=" term ","
    "factorization" ":=" term :
  tactic

syntax (name := rr_product_lift_C_sequence_auto_cutoff_named)
  "rr_product_lift_C_sequence_auto" " using "
    "base" ":=" term ","
    "quotient_realrooted" ":=" term ","
    "cutoff" ":=" term ","
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

syntax (name := rr_product_lift_affine_sequence_cutoff_named)
  "rr_product_lift_affine_sequence" " using "
    "base" ":=" term ","
    "quotient_realrooted" ":=" term ","
    "slope_ne" ":=" term ","
    "cutoff" ":=" term ","
    "factorization" ":=" term :
  tactic

syntax (name := rr_product_lift_affine_sequence_auto_named)
  "rr_product_lift_affine_sequence_auto" " using "
    "quotient_realrooted" ":=" term ","
    "factorization" ":=" term :
  tactic

syntax (name := rr_product_lift_affine_sequence_auto_cutoff_named)
  "rr_product_lift_affine_sequence_auto" " using "
    "base" ":=" term ","
    "quotient_realrooted" ":=" term ","
    "cutoff" ":=" term ","
    "factorization" ":=" term :
  tactic

syntax (name := rr_product_lift_const_first_sequence_named)
  "rr_product_lift_const_first_sequence" " using "
    "quotient_realrooted" ":=" term ","
    "slope_ne" ":=" term ","
    "factorization" ":=" term :
  tactic

syntax (name := rr_product_lift_const_first_sequence_cutoff_named)
  "rr_product_lift_const_first_sequence" " using "
    "base" ":=" term ","
    "quotient_realrooted" ":=" term ","
    "slope_ne" ":=" term ","
    "cutoff" ":=" term ","
    "factorization" ":=" term :
  tactic

syntax (name := rr_product_lift_const_first_sequence_auto_named)
  "rr_product_lift_const_first_sequence_auto" " using "
    "quotient_realrooted" ":=" term ","
    "factorization" ":=" term :
  tactic

syntax (name := rr_product_lift_const_first_sequence_auto_cutoff_named)
  "rr_product_lift_const_first_sequence_auto" " using "
    "base" ":=" term ","
    "quotient_realrooted" ":=" term ","
    "cutoff" ":=" term ","
    "factorization" ":=" term :
  tactic

syntax (name := rr_product_lift_C_pow_sequence_named)
  "rr_product_lift_C_pow_sequence" " using "
    "quotient_realrooted" ":=" term ","
    "scalar_ne" ":=" term ","
    "factorization" ":=" term :
  tactic

syntax (name := rr_product_lift_C_pow_sequence_cutoff_named)
  "rr_product_lift_C_pow_sequence" " using "
    "base" ":=" term ","
    "quotient_realrooted" ":=" term ","
    "scalar_ne" ":=" term ","
    "cutoff" ":=" term ","
    "factorization" ":=" term :
  tactic

syntax (name := rr_product_lift_C_pow_sequence_auto_named)
  "rr_product_lift_C_pow_sequence_auto" " using "
    "quotient_realrooted" ":=" term ","
    "factorization" ":=" term :
  tactic

syntax (name := rr_product_lift_C_pow_sequence_auto_cutoff_named)
  "rr_product_lift_C_pow_sequence_auto" " using "
    "base" ":=" term ","
    "quotient_realrooted" ":=" term ","
    "cutoff" ":=" term ","
    "factorization" ":=" term :
  tactic

syntax (name := rr_product_lift_checked_scalar_sequence_auto_named)
  "rr_product_lift_checked_scalar_sequence_auto" " using "
    "quotient_realrooted" ":=" term ","
    "factorization" ":=" term :
  tactic

syntax (name := rr_product_lift_checked_scalar_sequence_auto_cutoff_named)
  "rr_product_lift_checked_scalar_sequence_auto" " using "
    "base" ":=" term ","
    "quotient_realrooted" ":=" term ","
    "cutoff" ":=" term ","
    "factorization" ":=" term :
  tactic

syntax (name := rr_product_lift_X_pow_sequence_named)
  "rr_product_lift_X_pow_sequence" " using "
    "quotient_realrooted" ":=" term ","
    "factorization" ":=" term :
  tactic

syntax (name := rr_product_lift_X_pow_sequence_cutoff_named)
  "rr_product_lift_X_pow_sequence" " using "
    "base" ":=" term ","
    "quotient_realrooted" ":=" term ","
    "cutoff" ":=" term ","
    "factorization" ":=" term :
  tactic

syntax (name := rr_product_lift_X_add_C_pow_sequence_named)
  "rr_product_lift_X_add_C_pow_sequence" " using "
    "quotient_realrooted" ":=" term ","
    "factorization" ":=" term :
  tactic

syntax (name := rr_product_lift_X_add_C_pow_sequence_cutoff_named)
  "rr_product_lift_X_add_C_pow_sequence" " using "
    "base" ":=" term ","
    "quotient_realrooted" ":=" term ","
    "cutoff" ":=" term ","
    "factorization" ":=" term :
  tactic

syntax (name := rr_product_lift_X_add_C_row_pow_sequence_named)
  "rr_product_lift_X_add_C_row_pow_sequence" " using "
    "quotient_realrooted" ":=" term ","
    "factorization" ":=" term :
  tactic

syntax (name := rr_product_lift_X_add_C_row_pow_sequence_cutoff_named)
  "rr_product_lift_X_add_C_row_pow_sequence" " using "
    "base" ":=" term ","
    "quotient_realrooted" ":=" term ","
    "cutoff" ":=" term ","
    "factorization" ":=" term :
  tactic

syntax (name := rr_product_lift_C_add_X_pow_sequence_named)
  "rr_product_lift_C_add_X_pow_sequence" " using "
    "quotient_realrooted" ":=" term ","
    "factorization" ":=" term :
  tactic

syntax (name := rr_product_lift_C_add_X_pow_sequence_cutoff_named)
  "rr_product_lift_C_add_X_pow_sequence" " using "
    "base" ":=" term ","
    "quotient_realrooted" ":=" term ","
    "cutoff" ":=" term ","
    "factorization" ":=" term :
  tactic

syntax (name := rr_product_lift_affine_pow_sequence_named)
  "rr_product_lift_affine_pow_sequence" " using "
    "quotient_realrooted" ":=" term ","
    "slope_ne" ":=" term ","
    "factorization" ":=" term :
  tactic

syntax (name := rr_product_lift_affine_pow_sequence_cutoff_named)
  "rr_product_lift_affine_pow_sequence" " using "
    "base" ":=" term ","
    "quotient_realrooted" ":=" term ","
    "slope_ne" ":=" term ","
    "cutoff" ":=" term ","
    "factorization" ":=" term :
  tactic

syntax (name := rr_product_lift_affine_pow_sequence_auto_named)
  "rr_product_lift_affine_pow_sequence_auto" " using "
    "quotient_realrooted" ":=" term ","
    "factorization" ":=" term :
  tactic

syntax (name := rr_product_lift_affine_pow_sequence_auto_cutoff_named)
  "rr_product_lift_affine_pow_sequence_auto" " using "
    "base" ":=" term ","
    "quotient_realrooted" ":=" term ","
    "cutoff" ":=" term ","
    "factorization" ":=" term :
  tactic

syntax (name := rr_product_lift_const_first_affine_pow_sequence_named)
  "rr_product_lift_const_first_affine_pow_sequence" " using "
    "quotient_realrooted" ":=" term ","
    "slope_ne" ":=" term ","
    "factorization" ":=" term :
  tactic

syntax (name := rr_product_lift_const_first_affine_pow_sequence_cutoff_named)
  "rr_product_lift_const_first_affine_pow_sequence" " using "
    "base" ":=" term ","
    "quotient_realrooted" ":=" term ","
    "slope_ne" ":=" term ","
    "cutoff" ":=" term ","
    "factorization" ":=" term :
  tactic

syntax (name := rr_product_lift_const_first_affine_pow_sequence_auto_named)
  "rr_product_lift_const_first_affine_pow_sequence_auto" " using "
    "quotient_realrooted" ":=" term ","
    "factorization" ":=" term :
  tactic

syntax (name := rr_product_lift_const_first_affine_pow_sequence_auto_cutoff_named)
  "rr_product_lift_const_first_affine_pow_sequence_auto" " using "
    "base" ":=" term ","
    "quotient_realrooted" ":=" term ","
    "cutoff" ":=" term ","
    "factorization" ":=" term :
  tactic

syntax (name := rr_product_lift_checked_affine_sequence_auto_named)
  "rr_product_lift_checked_affine_sequence_auto" " using "
    "quotient_realrooted" ":=" term ","
    "factorization" ":=" term :
  tactic

syntax (name := rr_product_lift_checked_affine_sequence_auto_cutoff_named)
  "rr_product_lift_checked_affine_sequence_auto" " using "
    "base" ":=" term ","
    "quotient_realrooted" ":=" term ","
    "cutoff" ":=" term ","
    "factorization" ":=" term :
  tactic

syntax (name := rr_product_lift_checked_affine_pow_sequence_auto_named)
  "rr_product_lift_checked_affine_pow_sequence_auto" " using "
    "quotient_realrooted" ":=" term ","
    "factorization" ":=" term :
  tactic

syntax (name := rr_product_lift_checked_affine_pow_sequence_auto_cutoff_named)
  "rr_product_lift_checked_affine_pow_sequence_auto" " using "
    "base" ":=" term ","
    "quotient_realrooted" ":=" term ","
    "cutoff" ":=" term ","
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
    ("cutoff" ":=" term ",")?
    "recurrence" ":=" term :
  tactic

syntax (name := rr_product_affine_sequence_auto_named)
  "rr_product_affine_sequence_auto" " using "
    "base" ":=" term ","
    ("cutoff" ":=" term ",")?
    "recurrence" ":=" term :
  tactic

syntax (name := rr_product_const_first_sequence_named)
  "rr_product_const_first_sequence" " using "
    "base" ":=" term ","
    "slope_ne" ":=" term ","
    ("cutoff" ":=" term ",")?
    "recurrence" ":=" term :
  tactic

syntax (name := rr_product_const_first_sequence_auto_named)
  "rr_product_const_first_sequence_auto" " using "
    "base" ":=" term ","
    ("cutoff" ":=" term ",")?
    "recurrence" ":=" term :
  tactic

syntax (name := rr_product_checked_affine_sequence_auto_named)
  "rr_product_checked_affine_sequence_auto" " using "
    "base" ":=" term ","
    ("cutoff" ":=" term ",")?
    "recurrence" ":=" term :
  tactic

syntax (name := rr_product_X_sequence_named)
  "rr_product_X_sequence" " using "
    "base" ":=" term ","
    ("cutoff" ":=" term ",")?
    "recurrence" ":=" term :
  tactic

syntax (name := rr_product_C_add_X_sequence_named)
  "rr_product_C_add_X_sequence" " using "
    "base" ":=" term ","
    ("cutoff" ":=" term ",")?
    "recurrence" ":=" term :
  tactic

syntax (name := rr_product_C_pow_sequence_named)
  "rr_product_C_pow_sequence" " using "
    "base" ":=" term ","
    "scalar_ne" ":=" term ","
    ("cutoff" ":=" term ",")?
    "recurrence" ":=" term :
  tactic

syntax (name := rr_product_C_pow_sequence_auto_named)
  "rr_product_C_pow_sequence_auto" " using "
    "base" ":=" term ","
    ("cutoff" ":=" term ",")?
    "recurrence" ":=" term :
  tactic

syntax (name := rr_product_X_pow_sequence_named)
  "rr_product_X_pow_sequence" " using "
    "base" ":=" term ","
    ("cutoff" ":=" term ",")?
    "recurrence" ":=" term :
  tactic

syntax (name := rr_product_X_add_C_pow_sequence_named)
  "rr_product_X_add_C_pow_sequence" " using "
    "base" ":=" term ","
    ("cutoff" ":=" term ",")?
    "recurrence" ":=" term :
  tactic

syntax (name := rr_product_C_add_X_pow_sequence_named)
  "rr_product_C_add_X_pow_sequence" " using "
    "base" ":=" term ","
    ("cutoff" ":=" term ",")?
    "recurrence" ":=" term :
  tactic

syntax (name := rr_product_affine_pow_sequence_named)
  "rr_product_affine_pow_sequence" " using "
    "base" ":=" term ","
    "slope_ne" ":=" term ","
    ("cutoff" ":=" term ",")?
    "recurrence" ":=" term :
  tactic

syntax (name := rr_product_affine_pow_sequence_auto_named)
  "rr_product_affine_pow_sequence_auto" " using "
    "base" ":=" term ","
    ("cutoff" ":=" term ",")?
    "recurrence" ":=" term :
  tactic

syntax (name := rr_product_const_first_affine_pow_sequence_named)
  "rr_product_const_first_affine_pow_sequence" " using "
    "base" ":=" term ","
    "slope_ne" ":=" term ","
    ("cutoff" ":=" term ",")?
    "recurrence" ":=" term :
  tactic

syntax (name := rr_product_const_first_affine_pow_sequence_auto_named)
  "rr_product_const_first_affine_pow_sequence_auto" " using "
    "base" ":=" term ","
    ("cutoff" ":=" term ",")?
    "recurrence" ":=" term :
  tactic

syntax (name := rr_product_checked_affine_pow_sequence_auto_named)
  "rr_product_checked_affine_pow_sequence_auto" " using "
    "base" ":=" term ","
    ("cutoff" ":=" term ",")?
    "recurrence" ":=" term :
  tactic

syntax (name := rr_product_checked_scalar_sequence_auto_named)
  "rr_product_checked_scalar_sequence_auto" " using "
    "base" ":=" term ","
    ("cutoff" ":=" term ",")?
    "recurrence" ":=" term :
  tactic

syntax (name := rr_product_scalar_sequence_named)
  "rr_product_scalar_sequence" " using "
    "base" ":=" term ","
    "scalar_ne" ":=" term ","
    ("cutoff" ":=" term ",")?
    "recurrence" ":=" term :
  tactic

syntax (name := rr_product_scalar_sequence_auto_named)
  "rr_product_scalar_sequence_auto" " using "
    "base" ":=" term ","
    ("cutoff" ":=" term ",")?
    "recurrence" ":=" term :
  tactic

syntax (name := rr_product_scalar_linear_sequence_named)
  "rr_product_scalar_linear_sequence" " using "
    "base" ":=" term ","
    "scalar_ne" ":=" term ","
    ("cutoff" ":=" term ",")?
    "scalar_step" ":=" term ","
    "linear_step" ":=" term :
  tactic

syntax (name := rr_product_scalar_linear_sequence_auto_named)
  "rr_product_scalar_linear_sequence_auto" " using "
    "base" ":=" term ","
    ("cutoff" ":=" term ",")?
    "scalar_step" ":=" term ","
    "linear_step" ":=" term :
  tactic

syntax (name := rr_product_scalar_C_add_X_sequence_named)
  "rr_product_scalar_C_add_X_sequence" " using "
    "base" ":=" term ","
    "scalar_ne" ":=" term ","
    ("cutoff" ":=" term ",")?
    "scalar_step" ":=" term ","
    "linear_step" ":=" term :
  tactic

syntax (name := rr_product_scalar_C_add_X_sequence_auto_named)
  "rr_product_scalar_C_add_X_sequence_auto" " using "
    "base" ":=" term ","
    ("cutoff" ":=" term ",")?
    "scalar_step" ":=" term ","
    "linear_step" ":=" term :
  tactic

syntax (name := rr_product_scalar_factor_sequence_named)
  "rr_product_scalar_factor_sequence" " using "
    "base" ":=" term ","
    "scalar_ne" ":=" term ","
    "factor_realrooted" ":=" term ","
    ("cutoff" ":=" term ",")?
    "scalar_step" ":=" term ","
    "factor_step" ":=" term :
  tactic

syntax (name := rr_product_scalar_factor_sequence_auto_named)
  "rr_product_scalar_factor_sequence_auto" " using "
    "base" ":=" term ","
    "factor_realrooted" ":=" term ","
    ("cutoff" ":=" term ",")?
    "scalar_step" ":=" term ","
    "factor_step" ":=" term :
  tactic

syntax (name := rr_product_scalar_X_pow_sequence_named)
  "rr_product_scalar_X_pow_sequence" " using "
    "base" ":=" term ","
    "scalar_ne" ":=" term ","
    ("cutoff" ":=" term ",")?
    "scalar_step" ":=" term ","
    "factor_step" ":=" term :
  tactic

syntax (name := rr_product_scalar_X_pow_sequence_auto_named)
  "rr_product_scalar_X_pow_sequence_auto" " using "
    "base" ":=" term ","
    ("cutoff" ":=" term ",")?
    "scalar_step" ":=" term ","
    "factor_step" ":=" term :
  tactic

syntax (name := rr_product_scalar_X_add_C_pow_sequence_named)
  "rr_product_scalar_X_add_C_pow_sequence" " using "
    "base" ":=" term ","
    "scalar_ne" ":=" term ","
    ("cutoff" ":=" term ",")?
    "scalar_step" ":=" term ","
    "factor_step" ":=" term :
  tactic

syntax (name := rr_product_scalar_X_add_C_pow_sequence_auto_named)
  "rr_product_scalar_X_add_C_pow_sequence_auto" " using "
    "base" ":=" term ","
    ("cutoff" ":=" term ",")?
    "scalar_step" ":=" term ","
    "factor_step" ":=" term :
  tactic

syntax (name := rr_product_scalar_C_add_X_pow_sequence_named)
  "rr_product_scalar_C_add_X_pow_sequence" " using "
    "base" ":=" term ","
    "scalar_ne" ":=" term ","
    ("cutoff" ":=" term ",")?
    "scalar_step" ":=" term ","
    "factor_step" ":=" term :
  tactic

syntax (name := rr_product_scalar_C_add_X_pow_sequence_auto_named)
  "rr_product_scalar_C_add_X_pow_sequence_auto" " using "
    "base" ":=" term ","
    ("cutoff" ":=" term ",")?
    "scalar_step" ":=" term ","
    "factor_step" ":=" term :
  tactic

syntax (name := rr_product_nonzero) "rr_product_nonzero" : tactic

syntax (name := rr_product_normalize)
  "rr_product_normalize" " using " term :
  tactic

syntax (name := rr_product_nonzero_term) "rr_product_nonzero_term" : term

syntax (name := rr_product_nonzero_seq) "rr_product_nonzero_seq" : term

syntax (name := rr_product_nonzero_seq_from) "rr_product_nonzero_seq_from" : term

syntax (name := rr_product_two_variants)
  "rr_product_two_variants" term ", " term :
  tactic

syntax (name := rr_product_two_sequence_variants)
  "rr_product_two_sequence_variants" term ", " term :
  tactic

syntax (name := rr_product_four_sequence_variants)
  "rr_product_four_sequence_variants" term ", " term ", " term ", " term :
  tactic

private inductive AffinePowOrientation where
  | mulXFirst
  | constFirst

private inductive ScalarFactorKind where
  | scalar
  | scalarPow

private def appFnName? (e : Expr) : Option Name :=
  e.consumeMData.getAppFn.constName?

private partial def containsAppFn (needle : Name) (e : Expr) : Bool :=
  let e := e.consumeMData
  appFnName? e == some needle ||
    e.getAppArgs.any (containsAppFn needle) ||
    match e with
    | .forallE _ domain body _ => containsAppFn needle domain || containsAppFn needle body
    | .lam _ domain body _ => containsAppFn needle domain || containsAppFn needle body
    | .letE _ type value body _ =>
        containsAppFn needle type || containsAppFn needle value || containsAppFn needle body
    | .proj _ _ body => containsAppFn needle body
    | _ => false

private def isPolynomialX (e : Expr) : Bool :=
  appFnName? e == some ``Polynomial.X

private def containsPolynomialX (e : Expr) : Bool :=
  containsAppFn ``Polynomial.X e

private def isScalarPolynomialExpr (e : Expr) : Bool :=
  containsAppFn ``Polynomial.C e && !containsPolynomialX e

private def scalarFactorKind? (e : Expr) : Option ScalarFactorKind :=
  let e := e.consumeMData
  if appFnName? e == some ``HPow.hPow then
    let args := e.getAppArgs
    if args.size > 5 && isScalarPolynomialExpr args[4]! then
      some .scalarPow
    else
      none
  else if isScalarPolynomialExpr e then
    some .scalar
  else
    none

private partial def topMulFactors (e : Expr) : List Expr :=
  let e := e.consumeMData
  if appFnName? e == some ``HMul.hMul then
    let args := e.getAppArgs
    if args.size > 5 then
      topMulFactors args[4]! ++ topMulFactors args[5]!
    else
      [e]
  else
    [e]

private def scalarKindOfTopProduct? (rhs : Expr) : Option ScalarFactorKind :=
  match topMulFactors rhs with
  | lhsFactor :: rhsFactor :: [] =>
      match scalarFactorKind? lhsFactor, scalarFactorKind? rhsFactor with
      | some kind, none => some kind
      | none, some kind => some kind
      | _, _ => none
  | _ => none

private partial def findScalarTopProductKind? (e : Expr) :
    Option ScalarFactorKind := Id.run do
  let e := e.consumeMData
  if appFnName? e == some ``Eq then
    let args := e.getAppArgs
    if args.size > 0 then
      if let some kind := scalarKindOfTopProduct? args[args.size - 1]! then
        return some kind
  match e with
  | .forallE _ _ body _ => findScalarTopProductKind? body
  | .lam _ _ body _ => findScalarTopProductKind? body
  | .letE _ _ value body _ =>
      if let some kind := findScalarTopProductKind? value then
        return some kind
      findScalarTopProductKind? body
  | .proj _ _ body => findScalarTopProductKind? body
  | _ => none

private def isPolynomialCMulX (e : Expr) : Bool :=
  let e := e.consumeMData
  appFnName? e == some ``HMul.hMul &&
    let args := e.getAppArgs
    args.size > 5 &&
      containsAppFn ``Polynomial.C args[4]! &&
      isPolynomialX args[5]!

private def affineOrientationOfBase? (e : Expr) : Option AffinePowOrientation :=
  let e := e.consumeMData
  if appFnName? e == some ``HAdd.hAdd then
    let args := e.getAppArgs
    if args.size > 5 then
      if isPolynomialCMulX args[4]! then
        some .mulXFirst
      else if isPolynomialCMulX args[5]! then
        some .constFirst
      else
        none
    else
      none
  else
    none

private partial def findAffinePowOrientation? (e : Expr) :
    Option AffinePowOrientation := Id.run do
  let e := e.consumeMData
  if appFnName? e == some ``HPow.hPow then
    let args := e.getAppArgs
    if args.size > 5 then
      if let some orientation := affineOrientationOfBase? args[4]! then
        return some orientation
  for arg in e.getAppArgs do
    if let some orientation := findAffinePowOrientation? arg then
      return some orientation
  match e with
  | .forallE _ domain body _ =>
      if let some orientation := findAffinePowOrientation? domain then
        return some orientation
      findAffinePowOrientation? body
  | .lam _ domain body _ =>
      if let some orientation := findAffinePowOrientation? domain then
        return some orientation
      findAffinePowOrientation? body
  | .letE _ type value body _ =>
      if let some orientation := findAffinePowOrientation? type then
        return some orientation
      if let some orientation := findAffinePowOrientation? value then
        return some orientation
      findAffinePowOrientation? body
  | .proj _ _ body => findAffinePowOrientation? body
  | _ => none

private partial def findAffineLinearOrientation? (e : Expr) :
    Option AffinePowOrientation := Id.run do
  let e := e.consumeMData
  if appFnName? e == some ``HPow.hPow then
    return none
  if let some orientation := affineOrientationOfBase? e then
    return some orientation
  for arg in e.getAppArgs do
    if let some orientation := findAffineLinearOrientation? arg then
      return some orientation
  match e with
  | .forallE _ domain body _ =>
      if let some orientation := findAffineLinearOrientation? domain then
        return some orientation
      findAffineLinearOrientation? body
  | .lam _ domain body _ =>
      if let some orientation := findAffineLinearOrientation? domain then
        return some orientation
      findAffineLinearOrientation? body
  | .letE _ type value body _ =>
      if let some orientation := findAffineLinearOrientation? type then
        return some orientation
      if let some orientation := findAffineLinearOrientation? value then
        return some orientation
      findAffineLinearOrientation? body
  | .proj _ _ body => findAffineLinearOrientation? body
  | _ => none

private def affineLinearOrientationOfEvidence (label : String) (evidence : Syntax) :
    TacticM AffinePowOrientation := withMainContext do
  let evidenceExpr ← Lean.Elab.Tactic.elabTerm evidence none
  let evidenceType ← instantiateMVars (← inferType evidenceExpr)
  match findAffineLinearOrientation? evidenceType with
  | some orientation => pure orientation
  | none =>
      throwError
        "rr_product checked affine auto: no affine factor found in {label}"

private def affinePowOrientationOfEvidence (label : String) (evidence : Syntax) :
    TacticM AffinePowOrientation := withMainContext do
  let evidenceExpr ← Lean.Elab.Tactic.elabTerm evidence none
  let evidenceType ← instantiateMVars (← inferType evidenceExpr)
  match findAffinePowOrientation? evidenceType with
  | some orientation => pure orientation
  | none =>
      throwError
        "rr_product checked affine-power auto: no affine-power factor found in {label}"

private def scalarKindOfEvidence (label : String) (evidence : Syntax) :
    TacticM ScalarFactorKind := withMainContext do
  let evidenceExpr ← Lean.Elab.Tactic.elabTerm evidence none
  let evidenceType ← instantiateMVars (← inferType evidenceExpr)
  match findScalarTopProductKind? evidenceType with
  | some kind => pure kind
  | none =>
      throwError "rr_product checked scalar auto: no scalar factor found in {label}"

elab "rr_product_lift_checked_affine_sequence_auto" " using "
    "quotient_realrooted" ":=" hquot:term ","
    "factorization" ":=" hrow:term : tactic => do
  match ← affineLinearOrientationOfEvidence "factorization" hrow with
  | .mulXFirst =>
      evalTactic
        (← `(tactic|
          rr_product_lift_affine_sequence_auto using
            quotient_realrooted := $hquot,
            factorization := $hrow))
  | .constFirst =>
      evalTactic
        (← `(tactic|
          rr_product_lift_const_first_sequence_auto using
            quotient_realrooted := $hquot,
            factorization := $hrow))

elab "rr_product_lift_checked_affine_sequence_auto" " using "
    "base" ":=" hbase:term ","
    "quotient_realrooted" ":=" hquot:term ","
    "cutoff" ":=" N:term ","
    "factorization" ":=" hrow:term : tactic => do
  match ← affineLinearOrientationOfEvidence "factorization" hrow with
  | .mulXFirst =>
      evalTactic
        (← `(tactic|
          rr_product_lift_affine_sequence_auto using
            base := $hbase,
            quotient_realrooted := $hquot,
            cutoff := $N,
            factorization := $hrow))
  | .constFirst =>
      evalTactic
        (← `(tactic|
          rr_product_lift_const_first_sequence_auto using
            base := $hbase,
            quotient_realrooted := $hquot,
            cutoff := $N,
            factorization := $hrow))

elab "rr_product_lift_checked_affine_pow_sequence_auto" " using "
    "quotient_realrooted" ":=" hquot:term ","
    "factorization" ":=" hrow:term : tactic => do
  match ← affinePowOrientationOfEvidence "factorization" hrow with
  | .mulXFirst =>
      evalTactic
        (← `(tactic|
          rr_product_lift_affine_pow_sequence_auto using
            quotient_realrooted := $hquot,
            factorization := $hrow))
  | .constFirst =>
      evalTactic
        (← `(tactic|
          rr_product_lift_const_first_affine_pow_sequence_auto using
            quotient_realrooted := $hquot,
            factorization := $hrow))

elab "rr_product_lift_checked_affine_pow_sequence_auto" " using "
    "base" ":=" hbase:term ","
    "quotient_realrooted" ":=" hquot:term ","
    "cutoff" ":=" N:term ","
    "factorization" ":=" hrow:term : tactic => do
  match ← affinePowOrientationOfEvidence "factorization" hrow with
  | .mulXFirst =>
      evalTactic
        (← `(tactic|
          rr_product_lift_affine_pow_sequence_auto using
            base := $hbase,
            quotient_realrooted := $hquot,
            cutoff := $N,
            factorization := $hrow))
  | .constFirst =>
      evalTactic
        (← `(tactic|
          rr_product_lift_const_first_affine_pow_sequence_auto using
            base := $hbase,
            quotient_realrooted := $hquot,
            cutoff := $N,
            factorization := $hrow))

elab "rr_product_lift_checked_scalar_sequence_auto" " using "
    "quotient_realrooted" ":=" hquot:term ","
    "factorization" ":=" hrow:term : tactic => do
  match ← scalarKindOfEvidence "factorization" hrow with
  | .scalar =>
      evalTactic
        (← `(tactic|
          rr_product_lift_C_sequence_auto using
            quotient_realrooted := $hquot,
            factorization := $hrow))
  | .scalarPow =>
      evalTactic
        (← `(tactic|
          rr_product_lift_C_pow_sequence_auto using
            quotient_realrooted := $hquot,
            factorization := $hrow))

elab "rr_product_lift_checked_scalar_sequence_auto" " using "
    "base" ":=" hbase:term ","
    "quotient_realrooted" ":=" hquot:term ","
    "cutoff" ":=" N:term ","
    "factorization" ":=" hrow:term : tactic => do
  match ← scalarKindOfEvidence "factorization" hrow with
  | .scalar =>
      evalTactic
        (← `(tactic|
          rr_product_lift_C_sequence_auto using
            base := $hbase,
            quotient_realrooted := $hquot,
            cutoff := $N,
            factorization := $hrow))
  | .scalarPow =>
      evalTactic
        (← `(tactic|
          rr_product_lift_C_pow_sequence_auto using
            base := $hbase,
            quotient_realrooted := $hquot,
            cutoff := $N,
            factorization := $hrow))

elab "rr_product_checked_affine_sequence_auto" " using "
    "base" ":=" hbase:term ","
    "recurrence" ":=" hrec:term : tactic => do
  match ← affineLinearOrientationOfEvidence "recurrence" hrec with
  | .mulXFirst =>
      evalTactic
        (← `(tactic|
          rr_product_affine_sequence_auto using
            base := $hbase,
            recurrence := $hrec))
  | .constFirst =>
      evalTactic
        (← `(tactic|
          rr_product_const_first_sequence_auto using
            base := $hbase,
            recurrence := $hrec))

elab "rr_product_checked_affine_sequence_auto" " using "
    "base" ":=" hbase:term ","
    "cutoff" ":=" N:term ","
    "recurrence" ":=" hrec:term : tactic => do
  match ← affineLinearOrientationOfEvidence "recurrence" hrec with
  | .mulXFirst =>
      evalTactic
        (← `(tactic|
          rr_product_affine_sequence_auto using
            base := $hbase,
            cutoff := $N,
            recurrence := $hrec))
  | .constFirst =>
      evalTactic
        (← `(tactic|
          rr_product_const_first_sequence_auto using
            base := $hbase,
            cutoff := $N,
            recurrence := $hrec))

elab "rr_product_checked_scalar_sequence_auto" " using "
    "base" ":=" hbase:term ","
    "recurrence" ":=" hrec:term : tactic => do
  match ← scalarKindOfEvidence "recurrence" hrec with
  | .scalar =>
      evalTactic
        (← `(tactic|
          rr_product_scalar_sequence_auto using
            base := $hbase,
            recurrence := $hrec))
  | .scalarPow =>
      evalTactic
        (← `(tactic|
          rr_product_C_pow_sequence_auto using
            base := $hbase,
            recurrence := $hrec))

elab "rr_product_checked_scalar_sequence_auto" " using "
    "base" ":=" hbase:term ","
    "cutoff" ":=" N:term ","
    "recurrence" ":=" hrec:term : tactic => do
  match ← scalarKindOfEvidence "recurrence" hrec with
  | .scalar =>
      evalTactic
        (← `(tactic|
          rr_product_scalar_sequence_auto using
            base := $hbase,
            cutoff := $N,
            recurrence := $hrec))
  | .scalarPow =>
      evalTactic
        (← `(tactic|
          rr_product_C_pow_sequence_auto using
            base := $hbase,
            cutoff := $N,
            recurrence := $hrec))

elab "rr_product_checked_affine_pow_sequence_auto" " using "
    "base" ":=" hbase:term ","
    "recurrence" ":=" hrec:term : tactic => do
  match ← affinePowOrientationOfEvidence "recurrence" hrec with
  | .mulXFirst =>
      evalTactic
        (← `(tactic|
          rr_product_affine_pow_sequence_auto using
            base := $hbase,
            recurrence := $hrec))
  | .constFirst =>
      evalTactic
        (← `(tactic|
          rr_product_const_first_affine_pow_sequence_auto using
            base := $hbase,
            recurrence := $hrec))

elab "rr_product_checked_affine_pow_sequence_auto" " using "
    "base" ":=" hbase:term ","
    "cutoff" ":=" N:term ","
    "recurrence" ":=" hrec:term : tactic => do
  match ← affinePowOrientationOfEvidence "recurrence" hrec with
  | .mulXFirst =>
      evalTactic
        (← `(tactic|
          rr_product_affine_pow_sequence_auto using
            base := $hbase,
            cutoff := $N,
            recurrence := $hrec))
  | .constFirst =>
      evalTactic
        (← `(tactic|
          rr_product_const_first_affine_pow_sequence_auto using
            base := $hbase,
            cutoff := $N,
            recurrence := $hrec))

macro_rules
  | `(tactic| rr_product_nonzero) =>
      `(tactic| rr_side_ne)
  | `(tactic| rr_product_normalize using $h:term) =>
      `(tactic|
        have hcert := ($h);
        first
          | exact hcert
          | convert hcert using 2 <;> norm_num <;> ring)
  | `(rr_product_nonzero_term) =>
      `(by rr_product_nonzero)
  | `(rr_product_nonzero_seq) =>
      `(fun n => by rr_product_nonzero)
  | `(rr_product_nonzero_seq_from) =>
      `(fun n _ => by rr_product_nonzero)
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
  | `(tactic| rr_product_C using scalar_ne := $ha:term) =>
      `(tactic|
        rr_first_realrooted_or_projection (RealRooted.isRealRooted_C $ha))
  | `(tactic| rr_product_C_auto) =>
      `(tactic|
        rr_product_C using scalar_ne := rr_product_nonzero_term)
  | `(tactic|
      rr_product_C_pow using
        scalar_ne := $ha:term,
        exponent := $n:term) =>
      `(tactic|
        rr_first_realrooted_or_projection (RealRooted.isRealRooted_C_pow $ha $n))
  | `(tactic| rr_product_C_pow_auto using exponent := $n:term) =>
      `(tactic|
        rr_product_C_pow using
          scalar_ne := rr_product_nonzero_term,
          exponent := $n)
  | `(tactic| rr_product_X) =>
      `(tactic|
        rr_first_realrooted_or_projection RealRooted.isRealRooted_X)
  | `(tactic| rr_product_X_pow using exponent := $n:term) =>
      `(tactic|
        rr_first_realrooted_or_projection (RealRooted.isRealRooted_X_pow $n))
  | `(tactic| rr_product_X_add_C using constant := $t:term) =>
      `(tactic|
        rr_first_realrooted_or_projection (RealRooted.isRealRooted_X_add_C $t))
  | `(tactic|
      rr_product_X_add_C_pow using
        constant := $t:term,
        exponent := $n:term) =>
      `(tactic|
        rr_first_realrooted_or_projection (RealRooted.isRealRooted_X_add_C_pow $t $n))
  | `(tactic| rr_product_C_add_X using constant := $t:term) =>
      `(tactic|
        rr_first_realrooted_or_projection (RealRooted.isRealRooted_C_add_X $t))
  | `(tactic|
      rr_product_C_add_X_pow using
        constant := $t:term,
        exponent := $n:term) =>
      `(tactic|
        rr_first_realrooted_or_projection (RealRooted.isRealRooted_C_add_X_pow $t $n))
  | `(tactic| rr_product_affine using slope_ne := $hs:term) =>
      `(tactic|
        rr_first_realrooted_or_projection
          (RealRooted.isRealRooted_C_mul_X_add_C $hs))
  | `(tactic| rr_product_affine_auto) =>
      `(tactic|
        rr_product_affine using slope_ne := rr_product_nonzero_term)
  | `(tactic|
      rr_product_affine_pow using
        slope_ne := $hs:term,
        exponent := $n:term) =>
      `(tactic|
        rr_first_realrooted_or_projection
          (RealRooted.isRealRooted_C_mul_X_add_C_pow $hs $n))
  | `(tactic| rr_product_affine_pow_auto using exponent := $n:term) =>
      `(tactic|
        rr_product_affine_pow using
          slope_ne := rr_product_nonzero_term,
          exponent := $n)
  | `(tactic| rr_product_const_first_affine using slope_ne := $hs:term) =>
      `(tactic|
        rr_first_realrooted_or_projection
          (RealRooted.isRealRooted_C_add_C_mul_X $hs))
  | `(tactic| rr_product_const_first_affine_auto) =>
      `(tactic|
        rr_product_const_first_affine using slope_ne := rr_product_nonzero_term)
  | `(tactic|
      rr_product_const_first_affine_pow using
        slope_ne := $hs:term,
        exponent := $n:term) =>
      `(tactic|
        rr_first_realrooted_or_projection
          (RealRooted.isRealRooted_C_add_C_mul_X_pow $hs $n))
  | `(tactic| rr_product_const_first_affine_pow_auto using exponent := $n:term) =>
      `(tactic|
        rr_product_const_first_affine_pow using
          slope_ne := rr_product_nonzero_term,
          exponent := $n)
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
        rr_product_factor using $hp, rr_product_nonzero_term)
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
        rr_product_factor_const_first using $hp, rr_product_nonzero_term)
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
      rr_product_factor_sequence using
        base := $hbase:term,
        factor_realrooted := $hfactor:term,
        cutoff := $N:term,
        recurrence := $hstep:term) =>
      `(tactic|
        rr_product_two_sequence_variants
          (RealRooted.isRealRooted_of_product_factor_sequence_from
            $N $hbase $hfactor $hstep),
          (RealRooted.isRealRooted_of_product_factor_right_sequence_from
            $N $hbase $hfactor $hstep))
  | `(tactic|
      rr_product_factor_sequence using
        $hbase:term, $hfactor:term, $hstep:term) =>
      `(tactic|
        rr_product_factor_sequence using
          base := $hbase,
          factor_realrooted := $hfactor,
          recurrence := $hstep)
  | `(tactic| rr_affine_product_sequence using formula := $hroot:term) =>
      `(tactic|
        exact RealRooted.finiteLinearProductSequence_realRooted $hroot)
  | `(tactic|
      rr_j1_factorable_lag3_sequence_realrooted using
        scalar_ne_zero := $hc:term,
        root_grid := $hroot:term) =>
      `(tactic|
        exact RealRooted.finiteLinearProductScalarSequence_realRooted $hc $hroot)
  | `(tactic|
      rr_product_identity_sequence using
        base := $hbase:term,
        recurrence := $hstep:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_product_identity_sequence $hbase $hstep))
  | `(tactic|
      rr_product_identity_sequence using
        base := $hbase:term,
        cutoff := $N:term,
        recurrence := $hstep:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_product_identity_sequence_from
            $N $hbase $hstep))
  | `(tactic|
      rr_product_identity_sequence using
        $hbase:term, $hstep:term) =>
      `(tactic|
        rr_product_identity_sequence using
          base := $hbase,
          recurrence := $hstep)
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
      rr_product_root_zero_sequence using
        base := $hbase:term,
        cutoff := $N:term,
        recurrence := $hstep:term) =>
      `(tactic|
        rr_product_two_sequence_variants
          (RealRooted.isRealRooted_of_product_root_zero_sequence_from
            $N $hbase $hstep),
          (RealRooted.isRealRooted_of_product_root_zero_right_sequence_from
            $N $hbase $hstep))
  | `(tactic|
      rr_product_root_zero_sequence using
        $hbase:term, $hstep:term) =>
      `(tactic|
        rr_product_root_zero_sequence using
          base := $hbase,
          recurrence := $hstep)
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
      rr_product_period_two_sequence using
        base := $hbase:term,
        cutoff := $N:term,
        recurrence := $hstep:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_product_period_two_sequence_from
            $N $hbase $hstep))
  | `(tactic|
      rr_product_period_two_sequence using
        $hbase_zero:term, $hbase_one:term, $hstep:term) =>
      `(tactic|
        rr_product_period_two_sequence using
          base_zero := $hbase_zero,
          base_one := $hbase_one,
          recurrence := $hstep)
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
      rr_product_lift_sequence using
        base := $hbase:term,
        quotient_realrooted := $hquot:term,
        factor_realrooted := $hfactor:term,
        cutoff := $N:term,
        factorization := $hrow:term) =>
      `(tactic|
        rr_product_two_sequence_variants
          (RealRooted.isRealRooted_of_product_lift_sequence_from
            $N $hbase $hquot $hfactor $hrow),
          (RealRooted.isRealRooted_of_product_lift_right_sequence_from
            $N $hbase $hquot $hfactor $hrow))
  | `(tactic|
      rr_product_lift_sequence using
        $hquot:term, $hfactor:term, $hrow:term) =>
      `(tactic|
        rr_product_lift_sequence using
          quotient_realrooted := $hquot,
          factor_realrooted := $hfactor,
          factorization := $hrow)
  | `(tactic|
      rr_product_lift_sequence_auto using
        quotient_realrooted := $hquot:term,
        factorization := $hrow:term) =>
      `(tactic|
        first
          | rr_product_lift_X_sequence using
              quotient_realrooted := $hquot,
              factorization := $hrow
          | rr_product_lift_checked_scalar_sequence_auto using
              quotient_realrooted := $hquot,
              factorization := $hrow
          | rr_product_lift_C_sequence_auto using
              quotient_realrooted := $hquot,
              factorization := $hrow
          | rr_product_lift_checked_affine_sequence_auto using
              quotient_realrooted := $hquot,
              factorization := $hrow
          | rr_product_lift_checked_affine_pow_sequence_auto using
              quotient_realrooted := $hquot,
              factorization := $hrow
          | rr_product_lift_X_add_C_sequence using
              quotient_realrooted := $hquot,
              factorization := $hrow
          | rr_product_lift_C_add_X_sequence using
              quotient_realrooted := $hquot,
              factorization := $hrow
          | rr_product_lift_X_pow_sequence using
              quotient_realrooted := $hquot,
              factorization := $hrow
          | rr_product_lift_C_pow_sequence_auto using
              quotient_realrooted := $hquot,
              factorization := $hrow
          | rr_product_lift_X_add_C_pow_sequence using
              quotient_realrooted := $hquot,
              factorization := $hrow
          | rr_product_lift_X_add_C_row_pow_sequence using
              quotient_realrooted := $hquot,
              factorization := $hrow
          | rr_product_lift_C_add_X_pow_sequence using
              quotient_realrooted := $hquot,
              factorization := $hrow)
  | `(tactic|
      rr_product_lift_sequence_auto using
        base := $hbase:term,
        quotient_realrooted := $hquot:term,
        cutoff := $N:term,
        factorization := $hrow:term) =>
      `(tactic|
        first
          | rr_product_lift_X_sequence using
              base := $hbase,
              quotient_realrooted := $hquot,
              cutoff := $N,
              factorization := $hrow
          | rr_product_lift_checked_scalar_sequence_auto using
              base := $hbase,
              quotient_realrooted := $hquot,
              cutoff := $N,
              factorization := $hrow
          | rr_product_lift_C_sequence_auto using
              base := $hbase,
              quotient_realrooted := $hquot,
              cutoff := $N,
              factorization := $hrow
          | rr_product_lift_checked_affine_sequence_auto using
              base := $hbase,
              quotient_realrooted := $hquot,
              cutoff := $N,
              factorization := $hrow
          | rr_product_lift_checked_affine_pow_sequence_auto using
              base := $hbase,
              quotient_realrooted := $hquot,
              cutoff := $N,
              factorization := $hrow
          | rr_product_lift_X_add_C_sequence using
              base := $hbase,
              quotient_realrooted := $hquot,
              cutoff := $N,
              factorization := $hrow
          | rr_product_lift_C_add_X_sequence using
              base := $hbase,
              quotient_realrooted := $hquot,
              cutoff := $N,
              factorization := $hrow
          | rr_product_lift_X_pow_sequence using
              base := $hbase,
              quotient_realrooted := $hquot,
              cutoff := $N,
              factorization := $hrow
          | rr_product_lift_C_pow_sequence_auto using
              base := $hbase,
              quotient_realrooted := $hquot,
              cutoff := $N,
              factorization := $hrow
          | rr_product_lift_X_add_C_pow_sequence using
              base := $hbase,
              quotient_realrooted := $hquot,
              cutoff := $N,
              factorization := $hrow
          | rr_product_lift_X_add_C_row_pow_sequence using
              base := $hbase,
              quotient_realrooted := $hquot,
              cutoff := $N,
              factorization := $hrow
          | rr_product_lift_C_add_X_pow_sequence using
              base := $hbase,
              quotient_realrooted := $hquot,
              cutoff := $N,
              factorization := $hrow)
  | `(tactic|
      rr_product_lift_X_sequence using
        quotient_realrooted := $hquot:term,
        factorization := $hrow:term) =>
      `(tactic|
        rr_product_two_sequence_variants
          (RealRooted.isRealRooted_of_X_lift_sequence $hquot $hrow),
          (RealRooted.isRealRooted_of_X_lift_right_sequence $hquot $hrow))
  | `(tactic|
      rr_product_lift_X_sequence using
        base := $hbase:term,
        quotient_realrooted := $hquot:term,
        cutoff := $N:term,
        factorization := $hrow:term) =>
      `(tactic|
        rr_product_two_sequence_variants
          (RealRooted.isRealRooted_of_X_lift_sequence_from $N $hbase $hquot $hrow),
          (RealRooted.isRealRooted_of_X_lift_right_sequence_from
            $N $hbase $hquot $hrow))
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
      rr_product_lift_X_add_C_sequence using
        base := $hbase:term,
        quotient_realrooted := $hquot:term,
        cutoff := $N:term,
        factorization := $hrow:term) =>
      `(tactic|
        rr_product_two_sequence_variants
          (RealRooted.isRealRooted_of_X_add_C_lift_sequence_from
            $N $hbase $hquot $hrow),
          (RealRooted.isRealRooted_of_X_add_C_lift_right_sequence_from
            $N $hbase $hquot $hrow))
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
      rr_product_lift_C_add_X_sequence using
        base := $hbase:term,
        quotient_realrooted := $hquot:term,
        cutoff := $N:term,
        factorization := $hrow:term) =>
      `(tactic|
        rr_product_two_sequence_variants
          (RealRooted.isRealRooted_of_C_add_X_lift_sequence_from
            $N $hbase $hquot $hrow),
          (RealRooted.isRealRooted_of_C_add_X_lift_right_sequence_from
            $N $hbase $hquot $hrow))
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
      rr_product_lift_C_sequence using
        base := $hbase:term,
        quotient_realrooted := $hquot:term,
        scalar_ne := $hc:term,
        cutoff := $N:term,
        factorization := $hrow:term) =>
      `(tactic|
        rr_product_two_sequence_variants
          (RealRooted.isRealRooted_of_C_lift_sequence_from
            $N $hbase $hquot $hc $hrow),
          (RealRooted.isRealRooted_of_C_lift_right_sequence_from
            $N $hbase $hquot $hc $hrow))
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
      rr_product_lift_C_sequence_auto using
        base := $hbase:term,
        quotient_realrooted := $hquot:term,
        cutoff := $N:term,
        factorization := $hrow:term) =>
      `(tactic|
        rr_product_lift_C_sequence using
          base := $hbase,
          quotient_realrooted := $hquot,
          scalar_ne := rr_product_nonzero_seq_from,
          cutoff := $N,
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
      rr_product_lift_affine_sequence using
        base := $hbase:term,
        quotient_realrooted := $hquot:term,
        slope_ne := $hs:term,
        cutoff := $N:term,
        factorization := $hrow:term) =>
      `(tactic|
        rr_product_two_sequence_variants
          (RealRooted.isRealRooted_of_C_mul_X_add_C_lift_sequence_from
            $N $hbase $hquot $hs $hrow),
          (RealRooted.isRealRooted_of_C_mul_X_add_C_lift_right_sequence_from
            $N $hbase $hquot $hs $hrow))
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
      rr_product_lift_affine_sequence_auto using
        base := $hbase:term,
        quotient_realrooted := $hquot:term,
        cutoff := $N:term,
        factorization := $hrow:term) =>
      `(tactic|
        rr_product_lift_affine_sequence using
          base := $hbase,
          quotient_realrooted := $hquot,
          slope_ne := rr_product_nonzero_seq_from,
          cutoff := $N,
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
      rr_product_lift_const_first_sequence using
        base := $hbase:term,
        quotient_realrooted := $hquot:term,
        slope_ne := $hs:term,
        cutoff := $N:term,
        factorization := $hrow:term) =>
      `(tactic|
        rr_product_two_sequence_variants
          (RealRooted.isRealRooted_of_C_add_C_mul_X_lift_sequence_from
            $N $hbase $hquot $hs $hrow),
          (RealRooted.isRealRooted_of_C_add_C_mul_X_lift_right_sequence_from
            $N $hbase $hquot $hs $hrow))
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
      rr_product_lift_const_first_sequence_auto using
        base := $hbase:term,
        quotient_realrooted := $hquot:term,
        cutoff := $N:term,
        factorization := $hrow:term) =>
      `(tactic|
        rr_product_lift_const_first_sequence using
          base := $hbase,
          quotient_realrooted := $hquot,
          slope_ne := rr_product_nonzero_seq_from,
          cutoff := $N,
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
      rr_product_lift_C_pow_sequence using
        base := $hbase:term,
        quotient_realrooted := $hquot:term,
        scalar_ne := $hc:term,
        cutoff := $N:term,
        factorization := $hrow:term) =>
      `(tactic|
        rr_product_two_sequence_variants
          (RealRooted.isRealRooted_of_C_pow_lift_sequence_from
            $N $hbase $hquot $hc $hrow),
          (RealRooted.isRealRooted_of_C_pow_lift_right_sequence_from
            $N $hbase $hquot $hc $hrow))
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
      rr_product_lift_C_pow_sequence_auto using
        base := $hbase:term,
        quotient_realrooted := $hquot:term,
        cutoff := $N:term,
        factorization := $hrow:term) =>
      `(tactic|
        rr_product_lift_C_pow_sequence using
          base := $hbase,
          quotient_realrooted := $hquot,
          scalar_ne := rr_product_nonzero_seq_from,
          cutoff := $N,
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
      rr_product_lift_X_pow_sequence using
        base := $hbase:term,
        quotient_realrooted := $hquot:term,
        cutoff := $N:term,
        factorization := $hrow:term) =>
      `(tactic|
        rr_product_two_sequence_variants
          (RealRooted.isRealRooted_of_X_pow_lift_sequence_from
            $N $hbase $hquot $hrow),
          (RealRooted.isRealRooted_of_X_pow_lift_right_sequence_from
            $N $hbase $hquot $hrow))
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
      rr_product_lift_X_add_C_pow_sequence using
        base := $hbase:term,
        quotient_realrooted := $hquot:term,
        cutoff := $N:term,
        factorization := $hrow:term) =>
      `(tactic|
        rr_product_two_sequence_variants
          (RealRooted.isRealRooted_of_X_add_C_pow_lift_sequence_from
            $N $hbase $hquot $hrow),
          (RealRooted.isRealRooted_of_X_add_C_pow_lift_right_sequence_from
            $N $hbase $hquot $hrow))
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
      rr_product_lift_X_add_C_row_pow_sequence using
        base := $hbase:term,
        quotient_realrooted := $hquot:term,
        cutoff := $N:term,
        factorization := $hrow:term) =>
      `(tactic|
        rr_product_two_sequence_variants
          (RealRooted.isRealRooted_of_X_add_C_row_pow_lift_sequence_from
            $N $hbase $hquot $hrow),
          (RealRooted.isRealRooted_of_X_add_C_row_pow_lift_right_sequence_from
            $N $hbase $hquot $hrow))
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
      rr_product_lift_C_add_X_pow_sequence using
        base := $hbase:term,
        quotient_realrooted := $hquot:term,
        cutoff := $N:term,
        factorization := $hrow:term) =>
      `(tactic|
        rr_product_two_sequence_variants
          (RealRooted.isRealRooted_of_C_add_X_pow_lift_sequence_from
            $N $hbase $hquot $hrow),
          (RealRooted.isRealRooted_of_C_add_X_pow_lift_right_sequence_from
            $N $hbase $hquot $hrow))
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
      rr_product_lift_affine_pow_sequence using
        base := $hbase:term,
        quotient_realrooted := $hquot:term,
        slope_ne := $hs:term,
        cutoff := $N:term,
        factorization := $hrow:term) =>
      `(tactic|
        rr_product_two_sequence_variants
          (RealRooted.isRealRooted_of_C_mul_X_add_C_pow_lift_sequence_from
            $N $hbase $hquot $hs $hrow),
          (RealRooted.isRealRooted_of_C_mul_X_add_C_pow_lift_right_sequence_from
            $N $hbase $hquot $hs $hrow))
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
      rr_product_lift_affine_pow_sequence_auto using
        base := $hbase:term,
        quotient_realrooted := $hquot:term,
        cutoff := $N:term,
        factorization := $hrow:term) =>
      `(tactic|
        rr_product_lift_affine_pow_sequence using
          base := $hbase,
          quotient_realrooted := $hquot,
          slope_ne := rr_product_nonzero_seq_from,
          cutoff := $N,
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
      rr_product_lift_const_first_affine_pow_sequence using
        base := $hbase:term,
        quotient_realrooted := $hquot:term,
        slope_ne := $hs:term,
        cutoff := $N:term,
        factorization := $hrow:term) =>
      `(tactic|
        rr_product_two_sequence_variants
          (RealRooted.isRealRooted_of_C_add_C_mul_X_pow_lift_sequence_from
            $N $hbase $hquot $hs $hrow),
          (RealRooted.isRealRooted_of_C_add_C_mul_X_pow_lift_right_sequence_from
            $N $hbase $hquot $hs $hrow))
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
      rr_product_lift_const_first_affine_pow_sequence_auto using
        base := $hbase:term,
        quotient_realrooted := $hquot:term,
        cutoff := $N:term,
        factorization := $hrow:term) =>
      `(tactic|
        rr_product_lift_const_first_affine_pow_sequence using
          base := $hbase,
          quotient_realrooted := $hquot,
          slope_ne := rr_product_nonzero_seq_from,
          cutoff := $N,
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
      rr_product_affine_sequence using
        base := $hbase:term,
        slope_ne := $hs:term,
        cutoff := $N:term,
        recurrence := $hstep:term) =>
      `(tactic|
        rr_product_two_sequence_variants
          (RealRooted.isRealRooted_of_product_affine_sequence_from
            $N $hbase $hs $hstep),
          (RealRooted.isRealRooted_of_product_affine_right_sequence_from
            $N $hbase $hs $hstep))
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
      rr_product_affine_sequence_auto using
        base := $hbase:term,
        cutoff := $N:term,
        recurrence := $hstep:term) =>
      `(tactic|
        rr_product_affine_sequence using
          base := $hbase,
          slope_ne := rr_product_nonzero_seq,
          cutoff := $N,
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
      rr_product_const_first_sequence using
        base := $hbase:term,
        slope_ne := $hs:term,
        cutoff := $N:term,
        recurrence := $hstep:term) =>
      `(tactic|
        rr_product_two_sequence_variants
          (RealRooted.isRealRooted_of_product_const_first_affine_sequence_from
            $N $hbase $hs $hstep),
          (RealRooted.isRealRooted_of_product_const_first_affine_right_sequence_from
            $N $hbase $hs $hstep))
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
      rr_product_const_first_sequence_auto using
        base := $hbase:term,
        cutoff := $N:term,
        recurrence := $hstep:term) =>
      `(tactic|
        rr_product_const_first_sequence using
          base := $hbase,
          slope_ne := rr_product_nonzero_seq,
          cutoff := $N,
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
      rr_product_X_sequence using
        base := $hbase:term,
        cutoff := $N:term,
        recurrence := $hstep:term) =>
      `(tactic|
        rr_product_two_sequence_variants
          (RealRooted.isRealRooted_of_product_X_add_C_sequence_from
            $N $hbase $hstep),
          (RealRooted.isRealRooted_of_product_X_add_C_right_sequence_from
            $N $hbase $hstep))
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
      rr_product_C_add_X_sequence using
        base := $hbase:term,
        cutoff := $N:term,
        recurrence := $hstep:term) =>
      `(tactic|
        rr_product_two_sequence_variants
          (RealRooted.isRealRooted_of_product_C_add_X_sequence_from
            $N $hbase $hstep),
          (RealRooted.isRealRooted_of_product_C_add_X_right_sequence_from
            $N $hbase $hstep))
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
      rr_product_C_pow_sequence using
        base := $hbase:term,
        scalar_ne := $hc:term,
        cutoff := $N:term,
        recurrence := $hstep:term) =>
      `(tactic|
        rr_product_two_sequence_variants
          (RealRooted.isRealRooted_of_product_C_pow_sequence_from
            $N $hbase $hc $hstep),
          (RealRooted.isRealRooted_of_product_C_pow_right_sequence_from
            $N $hbase $hc $hstep))
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
      rr_product_C_pow_sequence_auto using
        base := $hbase:term,
        cutoff := $N:term,
        recurrence := $hstep:term) =>
      `(tactic|
        rr_product_C_pow_sequence using
          base := $hbase,
          scalar_ne := rr_product_nonzero_seq,
          cutoff := $N,
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
      rr_product_X_pow_sequence using
        base := $hbase:term,
        cutoff := $N:term,
        recurrence := $hstep:term) =>
      `(tactic|
        rr_product_two_sequence_variants
          (RealRooted.isRealRooted_of_product_X_pow_sequence_from
            $N $hbase $hstep),
          (RealRooted.isRealRooted_of_product_X_pow_right_sequence_from
            $N $hbase $hstep))
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
      rr_product_X_add_C_pow_sequence using
        base := $hbase:term,
        cutoff := $N:term,
        recurrence := $hstep:term) =>
      `(tactic|
        rr_product_two_sequence_variants
          (RealRooted.isRealRooted_of_product_X_add_C_pow_sequence_from
            $N $hbase $hstep),
          (RealRooted.isRealRooted_of_product_X_add_C_pow_right_sequence_from
            $N $hbase $hstep))
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
      rr_product_C_add_X_pow_sequence using
        base := $hbase:term,
        cutoff := $N:term,
        recurrence := $hstep:term) =>
      `(tactic|
        rr_product_two_sequence_variants
          (RealRooted.isRealRooted_of_product_C_add_X_pow_sequence_from
            $N $hbase $hstep),
          (RealRooted.isRealRooted_of_product_C_add_X_pow_right_sequence_from
            $N $hbase $hstep))
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
      rr_product_affine_pow_sequence using
        base := $hbase:term,
        slope_ne := $hs:term,
        cutoff := $N:term,
        recurrence := $hstep:term) =>
      `(tactic|
        rr_product_two_sequence_variants
          (RealRooted.isRealRooted_of_product_C_mul_X_add_C_pow_sequence_from
            $N $hbase $hs $hstep),
          (RealRooted.isRealRooted_of_product_C_mul_X_add_C_pow_right_sequence_from
            $N $hbase $hs $hstep))
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
      rr_product_affine_pow_sequence_auto using
        base := $hbase:term,
        cutoff := $N:term,
        recurrence := $hstep:term) =>
      `(tactic|
        rr_product_affine_pow_sequence using
          base := $hbase,
          slope_ne := rr_product_nonzero_seq,
          cutoff := $N,
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
      rr_product_const_first_affine_pow_sequence using
        base := $hbase:term,
        slope_ne := $hs:term,
        cutoff := $N:term,
        recurrence := $hstep:term) =>
      `(tactic|
        rr_product_two_sequence_variants
          (RealRooted.isRealRooted_of_product_C_add_C_mul_X_pow_sequence_from
            $N $hbase $hs $hstep),
          (RealRooted.isRealRooted_of_product_C_add_C_mul_X_pow_right_sequence_from
            $N $hbase $hs $hstep))
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
      rr_product_const_first_affine_pow_sequence_auto using
        base := $hbase:term,
        cutoff := $N:term,
        recurrence := $hstep:term) =>
      `(tactic|
        rr_product_const_first_affine_pow_sequence using
          base := $hbase,
          slope_ne := rr_product_nonzero_seq,
          cutoff := $N,
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
      rr_product_scalar_sequence using
        base := $hbase:term,
        scalar_ne := $ha:term,
        cutoff := $N:term,
        recurrence := $hstep:term) =>
      `(tactic|
        rr_product_two_sequence_variants
          (RealRooted.isRealRooted_of_product_scalar_sequence_from
            $N $hbase $ha $hstep),
          (RealRooted.isRealRooted_of_product_scalar_right_sequence_from
            $N $hbase $ha $hstep))
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
      rr_product_scalar_sequence_auto using
        base := $hbase:term,
        cutoff := $N:term,
        recurrence := $hstep:term) =>
      `(tactic|
        rr_product_scalar_sequence using
          base := $hbase,
          scalar_ne := rr_product_nonzero_seq,
          cutoff := $N,
          recurrence := $hstep)
  | `(tactic|
      rr_product_scalar_linear_sequence using
        base := $hbase:term,
        scalar_ne := $ha:term,
        cutoff := $N:term,
        scalar_step := $hscalar:term,
        linear_step := $hlinear:term) =>
      `(tactic|
        rr_product_four_sequence_variants
          (RealRooted.isRealRooted_of_product_scalar_linear_sequence_from
            $N $hbase $ha $hscalar $hlinear),
          (RealRooted.isRealRooted_of_product_scalar_linear_right_sequence_from
            $N $hbase $ha $hscalar $hlinear),
          (RealRooted.isRealRooted_of_product_scalar_linear_scalar_right_sequence_from
            $N $hbase $ha $hscalar $hlinear),
          (RealRooted.isRealRooted_of_product_scalar_linear_scalar_right_linear_right_sequence_from
            $N $hbase $ha $hscalar $hlinear))
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
        cutoff := $N:term,
        scalar_step := $hscalar:term,
        linear_step := $hlinear:term) =>
      `(tactic|
        rr_product_scalar_linear_sequence using
          base := $hbase,
          scalar_ne := rr_product_nonzero_seq_from,
          cutoff := $N,
          scalar_step := $hscalar,
          linear_step := $hlinear)
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
        cutoff := $N:term,
        scalar_step := $hscalar:term,
        linear_step := $hlinear:term) =>
      `(tactic|
        rr_product_four_sequence_variants
          (RealRooted.isRealRooted_of_product_scalar_C_add_X_sequence_from
            $N $hbase $ha $hscalar $hlinear),
          (RealRooted.isRealRooted_of_product_scalar_C_add_X_right_sequence_from
            $N $hbase $ha $hscalar $hlinear),
          (RealRooted.isRealRooted_of_product_scalar_C_add_X_scalar_right_sequence_from
            $N $hbase $ha $hscalar $hlinear),
          (RealRooted.isRealRooted_of_product_scalar_C_add_X_scalar_right_linear_right_sequence_from
            $N $hbase $ha $hscalar $hlinear))
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
        cutoff := $N:term,
        scalar_step := $hscalar:term,
        linear_step := $hlinear:term) =>
      `(tactic|
        rr_product_scalar_C_add_X_sequence using
          base := $hbase,
          scalar_ne := rr_product_nonzero_seq_from,
          cutoff := $N,
          scalar_step := $hscalar,
          linear_step := $hlinear)
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
        cutoff := $N:term,
        scalar_step := $hscalar:term,
        factor_step := $hstep:term) =>
      `(tactic|
        rr_product_four_sequence_variants
          (RealRooted.isRealRooted_of_product_scalar_factor_sequence_from
            $N $hbase $ha $hfactor $hscalar $hstep),
          (RealRooted.isRealRooted_of_product_scalar_factor_right_sequence_from
            $N $hbase $ha $hfactor $hscalar $hstep),
          (RealRooted.isRealRooted_of_product_scalar_factor_scalar_right_sequence_from
            $N $hbase $ha $hfactor $hscalar $hstep),
          (RealRooted.isRealRooted_of_product_scalar_factor_scalar_right_factor_right_sequence_from
            $N $hbase $ha $hfactor $hscalar $hstep))
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
        cutoff := $N:term,
        scalar_step := $hscalar:term,
        factor_step := $hstep:term) =>
      `(tactic|
        rr_product_scalar_factor_sequence using
          base := $hbase,
          scalar_ne := rr_product_nonzero_seq_from,
          factor_realrooted := $hfactor,
          cutoff := $N,
          scalar_step := $hscalar,
          factor_step := $hstep)
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
        cutoff := $N:term,
        scalar_step := $hscalar:term,
        factor_step := $hstep:term) =>
      `(tactic|
        rr_product_four_sequence_variants
          (RealRooted.isRealRooted_of_product_scalar_X_pow_sequence_from
            $N $hbase $ha $hscalar $hstep),
          (RealRooted.isRealRooted_of_product_scalar_X_pow_right_sequence_from
            $N $hbase $ha $hscalar $hstep),
          (RealRooted.isRealRooted_of_product_scalar_X_pow_scalar_right_sequence_from
            $N $hbase $ha $hscalar $hstep),
          (RealRooted.isRealRooted_of_product_scalar_X_pow_scalar_right_factor_right_sequence_from
            $N $hbase $ha $hscalar $hstep))
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
        cutoff := $N:term,
        scalar_step := $hscalar:term,
        factor_step := $hstep:term) =>
      `(tactic|
        rr_product_scalar_X_pow_sequence using
          base := $hbase,
          scalar_ne := rr_product_nonzero_seq_from,
          cutoff := $N,
          scalar_step := $hscalar,
          factor_step := $hstep)
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
        cutoff := $N:term,
        scalar_step := $hscalar:term,
        factor_step := $hstep:term) =>
      `(tactic|
        rr_product_four_sequence_variants
          (RealRooted.isRealRooted_of_product_scalar_X_add_C_pow_sequence_from
            $N $hbase $ha $hscalar $hstep),
          (RealRooted.isRealRooted_of_product_scalar_X_add_C_pow_right_sequence_from
            $N $hbase $ha $hscalar $hstep),
          (RealRooted.isRealRooted_of_product_scalar_X_add_C_pow_scalar_right_sequence_from
            $N $hbase $ha $hscalar $hstep),
          (isRealRooted_of_product_scalar_X_add_C_pow_scalar_right_factor_right_sequence_from
            $N $hbase $ha $hscalar $hstep))
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
        cutoff := $N:term,
        scalar_step := $hscalar:term,
        factor_step := $hstep:term) =>
      `(tactic|
        rr_product_scalar_X_add_C_pow_sequence using
          base := $hbase,
          scalar_ne := rr_product_nonzero_seq_from,
          cutoff := $N,
          scalar_step := $hscalar,
          factor_step := $hstep)
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
        cutoff := $N:term,
        scalar_step := $hscalar:term,
        factor_step := $hstep:term) =>
      `(tactic|
        rr_product_four_sequence_variants
          (RealRooted.isRealRooted_of_product_scalar_C_add_X_pow_sequence_from
            $N $hbase $ha $hscalar $hstep),
          (RealRooted.isRealRooted_of_product_scalar_C_add_X_pow_right_sequence_from
            $N $hbase $ha $hscalar $hstep),
          (RealRooted.isRealRooted_of_product_scalar_C_add_X_pow_scalar_right_sequence_from
            $N $hbase $ha $hscalar $hstep),
          (isRealRooted_of_product_scalar_C_add_X_pow_scalar_right_factor_right_sequence_from
            $N $hbase $ha $hscalar $hstep))
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
        cutoff := $N:term,
        scalar_step := $hscalar:term,
        factor_step := $hstep:term) =>
      `(tactic|
        rr_product_scalar_C_add_X_pow_sequence using
          base := $hbase,
          scalar_ne := rr_product_nonzero_seq_from,
          cutoff := $N,
          scalar_step := $hscalar,
          factor_step := $hstep)
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
