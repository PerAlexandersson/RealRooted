module

public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.Basic.Real.Basic
import RealRooted.ProductSequence.Core
import RealRooted.ProductSequence.Factors

/-!
# Specialized product-factor recurrence families

First-order affine, unit-slope affine, and powered unit-slope affine recurrence
shells derived from the generic product-sequence core.  Right-factor and tail-start
variants follow from `isRealRooted_of_product_factor_right_sequence` and
`isRealRooted_of_product_factor_sequence_from` in `RealRooted.ProductSequence.Core`.
-/

public section

open Polynomial
open scoped BigOperators

namespace RealRooted

open ProductSequence

/-- Sequence shell for first-order affine-product recurrences. -/
theorem isRealRooted_of_product_affine_sequence
    {P : Nat → ℝ[X]} {s t : Nat → ℝ}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hs : ∀ n : Nat, s n ≠ 0)
    (hstep : ∀ n : Nat, P (n + 1) = (C (s n) * X + C (t n)) * P n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_factor_sequence hbase (isRealRooted_C_mul_X_add_C_sequence hs) hstep

/-- Sequence shell for unit-slope factors `X + C t`. -/
theorem isRealRooted_of_product_X_add_C_sequence
    {P : Nat → ℝ[X]} {t : Nat → ℝ}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hstep : ∀ n : Nat, P (n + 1) = (X + C (t n)) * P n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_factor_sequence hbase (isRealRooted_X_add_C_one_sequence t) hstep

/-- Sequence shell for product recurrences with factors `(X + C t_n) ^ m_n`. -/
theorem isRealRooted_of_product_X_add_C_pow_sequence
    {P : Nat → ℝ[X]} {t : Nat → ℝ} {m : Nat → Nat}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hstep : ∀ n : Nat, P (n + 1) = (X + C (t n)) ^ (m n) * P n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_factor_sequence hbase (isRealRooted_X_add_C_pow_sequence t m) hstep

end RealRooted
