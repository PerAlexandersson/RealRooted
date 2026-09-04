import RealRooted.ProductSequence.Core

/-!
# Specialized product-factor recurrence families

First-order affine, monomial-power, scalar-power, and powered-affine recurrence
shells derived from the generic product-sequence core.
-/

open Polynomial
open scoped BigOperators

namespace RealRooted

open ProductSequenceInternal

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


end RealRooted

