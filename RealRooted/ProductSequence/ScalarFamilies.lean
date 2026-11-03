module

public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.Basic.Real.Basic
import RealRooted.ProductSequence.Lifts
import RealRooted.ProductSequence.Core
import RealRooted.ProductSequence.Factors
import RealRooted.SequenceClosure
import RealRooted.Linear

/-!
# Alternating scalar/product recurrence families

Degree-plateau and alternating scalar/product recurrence shells: a scalar step
followed by a supplied real-rooted factor, a unit-slope linear factor, or a powered
unit-slope linear factor.  Right-factor and tail-start variants follow from
`isRealRooted_of_product_factor_right_sequence` and `isRealRooted_of_product_factor_sequence_from`
in `RealRooted.ProductSequence.Core`.
-/

public section

open Polynomial
open scoped BigOperators

namespace RealRooted

open ProductSequence

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
      simpa [Nat.mul_succ, Nat.succ_eq_add_one, Nat.add_assoc] using
        (by simpa [hstep n] using isRealRooted_mul_of_isRealRooted (hfactor n) hodd)
  have hodd : ∀ n : Nat, P (2 * n + 1) ≠ 0 ∧ (P (2 * n + 1)).Splits :=
    isRealRooted_of_C_lift_sequence heven ha hscalar
  exact isRealRooted_of_even_odd_sequence heven hodd

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

end RealRooted
