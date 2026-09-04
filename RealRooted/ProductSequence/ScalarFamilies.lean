import RealRooted.ProductSequence.Lifts

/-!
# Alternating scalar/product recurrence families

Degree-plateau and alternating scalar/product recurrence shells, including
left/right factor and tail-start variants.
-/

open Polynomial
open scoped BigOperators

namespace RealRooted

open ProductSequenceInternal

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
  have heven : ∀ n : Nat, P (2 * n) ≠ 0 ∧ (P (2 * n)).Splits :=
    sequence_of_base_and_step (by simpa using hbase) fun n hP => by
      have hodd : P (2 * n + 1) ≠ 0 ∧ (P (2 * n + 1)).Splits := by
        simpa [hscalar n] using isRealRooted_C_mul_of_isRealRooted hP (ha n)
      have hnext :
          (F n * P (2 * n + 1) ≠ 0 ∧ (F n * P (2 * n + 1)).Splits) :=
        isRealRooted_mul_of_isRealRooted (hfactor n) hodd
      simpa [Nat.mul_succ, Nat.succ_eq_add_one, Nat.add_assoc] using
        (by simpa [hstep n] using hnext)
  have hodd : ∀ n : Nat, P (2 * n + 1) ≠ 0 ∧ (P (2 * n + 1)).Splits :=
    isRealRooted_of_C_lift_sequence heven ha hscalar
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
  have heven : ∀ n : Nat, P (2 * n) ≠ 0 ∧ (P (2 * n)).Splits :=
    sequence_of_base_interval_and_step_from N
      (fun n hn => hbase (2 * n) (by lia)) fun n hn hP => by
        have hodd : P (2 * n + 1) ≠ 0 ∧ (P (2 * n + 1)).Splits := by
          simpa [hscalar n hn] using
            isRealRooted_C_mul_of_isRealRooted hP (ha n hn)
        have hnext :
            (F n * P (2 * n + 1) ≠ 0 ∧
              (F n * P (2 * n + 1)).Splits) :=
          isRealRooted_mul_of_isRealRooted (hfactor n hn) hodd
        simpa [Nat.mul_succ, Nat.succ_eq_add_one, Nat.add_assoc] using
          (by simpa [hstep n hn] using hnext)
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


end RealRooted
