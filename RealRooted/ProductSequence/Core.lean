import RealRooted.ProductSequence.Factors
import RealRooted.SequenceClosure

/-!
# Generic product-sequence recurrence shells

Reusable induction, finite-product, period-two, and quotient-model shells with
caller-supplied real-rooted factor certificates.
-/

open Polynomial
open scoped BigOperators

namespace RealRooted

open ProductSequenceInternal

/-- Sequence shell for first-order product recurrences with a supplied factor certificate. -/
theorem isRealRooted_of_product_factor_sequence
    {P F : Nat → ℝ[X]}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hfactor : ∀ n : Nat, F n ≠ 0 ∧ (F n).Splits)
    (hstep : ∀ n : Nat, P (n + 1) = F n * P n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  sequence_of_base_and_step hbase fun n hP => by
    have hnext : F n * P n ≠ 0 ∧ (F n * P n).Splits :=
      isRealRooted_mul_of_isRealRooted (hfactor n) hP
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
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  sequence_of_base_interval_and_step_from N hbase fun n hn hP =>
    have hnext : F n * P n ≠ 0 ∧ (F n * P n).Splits :=
      isRealRooted_mul_of_isRealRooted (hfactor n hn) hP
    by simpa [Nat.succ_eq_add_one, hstep n hn] using hnext

/-- Right-factor variant of `isRealRooted_of_product_factor_sequence`. -/
theorem isRealRooted_of_product_factor_right_sequence
    {P F : Nat → ℝ[X]}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hfactor : ∀ n : Nat, F n ≠ 0 ∧ (F n).Splits)
    (hstep : ∀ n : Nat, P (n + 1) = P n * F n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_factor_sequence hbase hfactor
    (fun n => by rw [hstep n, mul_comm])

/-- Sequence shell for lag-two product recurrences with supplied factor certificates. -/
theorem isRealRooted_of_lag_product_factor_sequence
    {P F : Nat → ℝ[X]}
    (hbase_zero : P 0 ≠ 0 ∧ (P 0).Splits)
    (hbase_one : P 1 ≠ 0 ∧ (P 1).Splits)
    (hfactor : ∀ n : Nat, F n ≠ 0 ∧ (F n).Splits)
    (hstep : ∀ n : Nat, P (n + 2) = F n * P n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  sequence_of_base_pair_and_step_two hbase_zero hbase_one fun n hP => by
    have hnext : F n * P n ≠ 0 ∧ (F n * P n).Splits :=
      isRealRooted_mul_of_isRealRooted (hfactor n) hP
    simpa [hstep n] using hnext

/-- Right-factor variant of `isRealRooted_of_lag_product_factor_sequence`. -/
theorem isRealRooted_of_lag_product_factor_right_sequence
    {P F : Nat → ℝ[X]}
    (hbase_zero : P 0 ≠ 0 ∧ (P 0).Splits)
    (hbase_one : P 1 ≠ 0 ∧ (P 1).Splits)
    (hfactor : ∀ n : Nat, F n ≠ 0 ∧ (F n).Splits)
    (hstep : ∀ n : Nat, P (n + 2) = P n * F n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_lag_product_factor_sequence hbase_zero hbase_one hfactor
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
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_factor_sequence (F := fun _ => (1 : ℝ[X]))
    hbase isRealRooted_one_sequence (fun n => by simpa [one_mul] using hstep n)

/-- Tail-start sequence shell for identity product recurrences. -/
theorem isRealRooted_of_product_identity_sequence_from
    {P : Nat → ℝ[X]}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hstep : ∀ n : Nat, N ≤ n → P (n + 1) = P n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_factor_sequence_from (F := fun _ => (1 : ℝ[X]))
    N hbase (fun n _ => isRealRooted_one_sequence n)
    (fun n hn => by simpa [one_mul] using hstep n hn)

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
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  sequence_of_base_pair_and_step_two hbase_zero hbase_one fun n hP => by
    simpa [hstep n] using hP

/-- Tail-start sequence shell for period-two product recurrences.  The
recurrence starts at row `N`, so the finite base interval must include rows
through `N + 1`. -/
theorem isRealRooted_of_product_period_two_sequence_from
    {P : Nat → ℝ[X]}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N + 1 → P n ≠ 0 ∧ (P n).Splits)
    (hstep : ∀ n : Nat, N ≤ n → P (n + 2) = P n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  sequence_of_base_interval_and_step_two_from N hbase fun n hn hP => by
    simpa [hstep n hn] using hP


end RealRooted

