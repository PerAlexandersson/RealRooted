import RealRooted.Tactic.Examples.Product.Basic
import RealRooted.Tactic.Examples.Product.Lifts
import RealRooted.Tactic.Product

/-!
# `rr_product_factor` examples

Regression tests for OEIS recurrences where `P_n` is a real linear factor
times `P_{n-1}`.
-/

open Polynomial
open scoped BigOperators

namespace RealRooted
namespace Tactic

/-- Endpoint quotient with `A_{n+1}=A_n+B_n`,
`B_{n+1}=B_n+X A_{n+1}`. -/
example {A B : Nat → ℝ[X]}
    (hbase : Prec (A 0) (B 0))
    (hA0_nonneg : HasNonnegCoeffs (A 0))
    (hB0_nonneg : HasNonnegCoeffs (B 0))
    (hstepA : ∀ n : Nat, A (n + 1) = A n + B n)
    (hstepB : ∀ n : Nat, B (n + 1) = B n + X * A (n + 1))
    (hcop : ∀ n : Nat, IsCoprime (B n) (X * A (n + 1))) :
    ∀ n : Nat, Prec (A n) (B n) := by
  rr_endpoint_sum_then_X_pair_sequence using
    base := hbase,
    left_nonneg := hA0_nonneg,
    right_nonneg := hB0_nonneg,
    sum_step := hstepA,
    x_step := hstepB,
    coprime := hcop

/-- Real-rootedness endpoint for the same sum-then-`X` quotient parity. -/
example {A B : Nat → ℝ[X]}
    (hbase : Prec (A 0) (B 0))
    (hA0_nonneg : HasNonnegCoeffs (A 0))
    (hB0_nonneg : HasNonnegCoeffs (B 0))
    (hstepA : ∀ n : Nat, A (n + 1) = A n + B n)
    (hstepB : ∀ n : Nat, B (n + 1) = B n + X * A (n + 1))
    (hcop : ∀ n : Nat, IsCoprime (B n) (X * A (n + 1))) :
    ∀ n : Nat, (A n ≠ 0 ∧ (A n).Splits) ∧ (B n ≠ 0 ∧ (B n).Splits) := by
  rr_endpoint_sum_then_X_pair_sequence_realrooted using
    base := hbase,
    left_nonneg := hA0_nonneg,
    right_nonneg := hB0_nonneg,
    sum_step := hstepA,
    x_step := hstepB,
    coprime := hcop

/-- Endpoint quotient with the parity reversed:
`B_{n+1}=B_n+X A_n`, `A_{n+1}=A_n+B_{n+1}`. -/
example {A B : Nat → ℝ[X]}
    (hbase : Prec (A 0) (B 0))
    (hA0_nonneg : HasNonnegCoeffs (A 0))
    (hB0_nonneg : HasNonnegCoeffs (B 0))
    (hstepB : ∀ n : Nat, B (n + 1) = B n + X * A n)
    (hstepA : ∀ n : Nat, A (n + 1) = A n + B (n + 1))
    (hcop : ∀ n : Nat, IsCoprime (B n) (X * A n)) :
    ∀ n : Nat, Prec (A n) (B n) := by
  rr_endpoint_X_then_sum_pair_sequence using
    base := hbase,
    left_nonneg := hA0_nonneg,
    right_nonneg := hB0_nonneg,
    x_step := hstepB,
    sum_step := hstepA,
    coprime := hcop

/-- Real-rootedness endpoint for the reversed endpoint quotient parity. -/
example {A B : Nat → ℝ[X]}
    (hbase : Prec (A 0) (B 0))
    (hA0_nonneg : HasNonnegCoeffs (A 0))
    (hB0_nonneg : HasNonnegCoeffs (B 0))
    (hstepB : ∀ n : Nat, B (n + 1) = B n + X * A n)
    (hstepA : ∀ n : Nat, A (n + 1) = A n + B (n + 1))
    (hcop : ∀ n : Nat, IsCoprime (B n) (X * A n)) :
    ∀ n : Nat, (A n ≠ 0 ∧ (A n).Splits) ∧ (B n ≠ 0 ∧ (B n).Splits) := by
  rr_endpoint_X_then_sum_pair_sequence_realrooted using
    base := hbase,
    left_nonneg := hA0_nonneg,
    right_nonneg := hB0_nonneg,
    x_step := hstepB,
    sum_step := hstepA,
    coprime := hcop

/-- Single-row endpoint-factor shell: even/odd rows are endpoint powers times
the sum-then-`X` quotient pair. -/
example {P A B : Nat → ℝ[X]} {mA mB : Nat → Nat}
    (hbase : Prec (A 0) (B 0))
    (hA0_nonneg : HasNonnegCoeffs (A 0))
    (hB0_nonneg : HasNonnegCoeffs (B 0))
    (hstepA : ∀ n : Nat, A (n + 1) = A n + B n)
    (hstepB : ∀ n : Nat, B (n + 1) = B n + X * A (n + 1))
    (hcop : ∀ n : Nat, IsCoprime (B n) (X * A (n + 1)))
    (hrowA : ∀ n : Nat, P (2 * n) = (X + C (1 : ℝ)) ^ (mA n) * A n)
    (hrowB : ∀ n : Nat, P (2 * n + 1) = (X + C (1 : ℝ)) ^ (mB n) * B n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_endpoint_sum_then_X_pair_lift_sequence using
    base := hbase,
    left_nonneg := hA0_nonneg,
    right_nonneg := hB0_nonneg,
    sum_step := hstepA,
    x_step := hstepB,
    coprime := hcop,
    even_factorization := hrowA,
    odd_factorization := hrowB

/-- Single-row endpoint-factor shell for the reversed quotient parity. -/
example {P A B : Nat → ℝ[X]} {mA mB : Nat → Nat}
    (hbase : Prec (A 0) (B 0))
    (hA0_nonneg : HasNonnegCoeffs (A 0))
    (hB0_nonneg : HasNonnegCoeffs (B 0))
    (hstepB : ∀ n : Nat, B (n + 1) = B n + X * A n)
    (hstepA : ∀ n : Nat, A (n + 1) = A n + B (n + 1))
    (hcop : ∀ n : Nat, IsCoprime (B n) (X * A n))
    (hrowA : ∀ n : Nat, P (2 * n) = (X + C (1 : ℝ)) ^ (mA n) * A n)
    (hrowB : ∀ n : Nat, P (2 * n + 1) = (X + C (1 : ℝ)) ^ (mB n) * B n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_endpoint_X_then_sum_pair_lift_sequence using
    base := hbase,
    left_nonneg := hA0_nonneg,
    right_nonneg := hB0_nonneg,
    x_step := hstepB,
    sum_step := hstepA,
    coprime := hcop,
    even_factorization := hrowA,
    odd_factorization := hrowB

/-- Single-row endpoint-factor shell for the reversed quotient parity when
even rows use the `B` quotient and odd rows use the `A` quotient. -/
example {P A B : Nat → ℝ[X]} {mA mB : Nat → Nat}
    (hbase : Prec (A 0) (B 0))
    (hA0_nonneg : HasNonnegCoeffs (A 0))
    (hB0_nonneg : HasNonnegCoeffs (B 0))
    (hstepB : ∀ n : Nat, B (n + 1) = B n + X * A n)
    (hstepA : ∀ n : Nat, A (n + 1) = A n + B (n + 1))
    (hcop : ∀ n : Nat, IsCoprime (B n) (X * A n))
    (hrowB : ∀ n : Nat, P (2 * n) = (X + C (1 : ℝ)) ^ (mB n) * B n)
    (hrowA : ∀ n : Nat, P (2 * n + 1) = (X + C (1 : ℝ)) ^ (mA n) * A n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_endpoint_X_then_sum_pair_lift_swapped_sequence using
    base := hbase,
    left_nonneg := hA0_nonneg,
    right_nonneg := hB0_nonneg,
    x_step := hstepB,
    sum_step := hstepA,
    coprime := hcop,
    even_factorization := hrowB,
    odd_factorization := hrowA

/-- `t^2`-factor recurrence, representative of stage records with repeated zero roots. -/
example {P : Nat → ℝ[X]}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hrec : ∀ n : Nat, P (n + 1) = ((X : ℝ[X]) ^ 2) * P n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_X_pow_sequence using
    base := hbase,
    recurrence := hrec

/-- `A054654`-style factor `1 + 2t - n t`. -/
example {p : ℝ[X]} {n : ℕ}
    (hp : p ≠ 0 ∧ p.Splits) (hn : (2 : ℝ) - (n : ℝ) ≠ 0) :
    ((C ((2 : ℝ) - (n : ℝ)) * X + C 1) * p ≠ 0 ∧
      ((C ((2 : ℝ) - (n : ℝ)) * X + C 1) * p).Splits) := by
  rr_product_factor using hp, hn

/-- `A161198`-style positive-slope factor `1 + 2n + 2t`. -/
example {p : ℝ[X]} {n : ℕ} (hp : p ≠ 0 ∧ p.Splits) :
    ((C (2 : ℝ) * X + C (1 + 2 * (n : ℝ))) * p ≠ 0 ∧
      ((C (2 : ℝ) * X + C (1 + 2 * (n : ℝ))) * p).Splits) := by
  rr_product_factor_auto using hp

/-- `A038220`-style report order `3 + 2t`. -/
example {p : ℝ[X]} (hp : p ≠ 0 ∧ p.Splits) :
    ((C (3 : ℝ) + C (2 : ℝ) * X) * p ≠ 0 ∧
      ((C (3 : ℝ) + C (2 : ℝ) * X) * p).Splits) := by
  rr_product_factor_const_first_auto using hp

/-- `A038226`-style report order `3 + 8t`. -/
example {p : ℝ[X]} (hp : p ≠ 0 ∧ p.Splits) :
    ((C (3 : ℝ) + C (8 : ℝ) * X) * p ≠ 0 ∧
      ((C (3 : ℝ) + C (8 : ℝ) * X) * p).Splits) := by
  rr_product_factor_const_first_auto using hp

/-- `A204579`-style unit-slope factor `t - 1 - 2n - n^2`. -/
example {p : ℝ[X]} {n : ℕ} (hp : p ≠ 0 ∧ p.Splits) :
    ((X + C (-1 - 2 * (n : ℝ) - (n : ℝ) ^ 2)) * p ≠ 0 ∧
      ((X + C (-1 - 2 * (n : ℝ) - (n : ℝ) ^ 2)) * p).Splits) := by
  rr_product_factor_X using hp

/-- Sequence-level affine product recurrence. -/
example {P : Nat → ℝ[X]} {s t : Nat → ℝ}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hs : ∀ n : Nat, s n ≠ 0)
    (hrec : ∀ n : Nat, P (n + 1) = (C (s n) * X + C (t n)) * P n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_affine_sequence using
    base := hbase,
    slope_ne := hs,
    recurrence := hrec

/-- The affine sequence macro also accepts the factor on the right. -/
example {P : Nat → ℝ[X]} {s t : Nat → ℝ}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hs : ∀ n : Nat, s n ≠ 0)
    (hrec : ∀ n : Nat, P (n + 1) = P n * (C (s n) * X + C (t n))) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_affine_sequence using
    base := hbase,
    slope_ne := hs,
    recurrence := hrec

/-- Report-order sequence recurrence with factor `C t + C s * X`. -/
example {P : Nat → ℝ[X]} {s t : Nat → ℝ}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hs : ∀ n : Nat, s n ≠ 0)
    (hrec : ∀ n : Nat, P (n + 1) = (C (t n) + C (s n) * X) * P n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_const_first_sequence using
    base := hbase,
    slope_ne := hs,
    recurrence := hrec

/-- The report-order sequence macro also accepts the factor on the right. -/
example {P : Nat → ℝ[X]} {s t : Nat → ℝ}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hs : ∀ n : Nat, s n ≠ 0)
    (hrec : ∀ n : Nat, P (n + 1) = P n * (C (t n) + C (s n) * X)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_const_first_sequence using
    base := hbase,
    slope_ne := hs,
    recurrence := hrec

/-- Automatic slope certificate for report-order product sequences. -/
example {P : Nat → ℝ[X]}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hrec : ∀ n : Nat,
      P (n + 1) = (C ((n : ℝ) + 1) + C ((n : ℝ) + 2) * X) * P n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_const_first_sequence_auto using
    base := hbase,
    recurrence := hrec

/-- Unit-slope sequence recurrence with factor `X+C t_n`. -/
example {P : Nat → ℝ[X]} {t : Nat → ℝ}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hrec : ∀ n : Nat, P (n + 1) = (X + C (t n)) * P n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_X_sequence using
    base := hbase,
    recurrence := hrec

/-- The unit-slope sequence macro accepts the factor on the right. -/
example {P : Nat → ℝ[X]} {t : Nat → ℝ}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hrec : ∀ n : Nat, P (n + 1) = P n * (X + C (t n))) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_X_sequence using
    base := hbase,
    recurrence := hrec

/-- Unit-slope product recurrences can start after finitely many base rows. -/
example {P : Nat → ℝ[X]} {t : Nat → ℝ}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hrec : ∀ n : Nat, N ≤ n → P (n + 1) = P n * (X + C (t n))) :
    ∀ n : Nat, (P n).Splits := by
  rr_product_X_sequence using
    base := hbase,
    cutoff := N,
    recurrence := hrec

/-- Constant-first unit-slope recurrence with factor `C t_n+X`. -/
example {P : Nat → ℝ[X]} {t : Nat → ℝ}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hrec : ∀ n : Nat, P (n + 1) = (C (t n) + X) * P n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_C_add_X_sequence using
    base := hbase,
    recurrence := hrec

/-- The constant-first unit-slope recurrence accepts the factor on the right. -/
example {P : Nat → ℝ[X]} {t : Nat → ℝ}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hrec : ∀ n : Nat, P (n + 1) = P n * (C (t n) + X)) :
    ∀ n : Nat, (P n).Splits := by
  rr_product_C_add_X_sequence using
    base := hbase,
    recurrence := hrec

/-- Constant-first unit-slope recurrences also accept a cutoff row. -/
example {P : Nat → ℝ[X]} {t : Nat → ℝ}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hrec : ∀ n : Nat, N ≤ n → P (n + 1) = (C (t n) + X) * P n) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_product_C_add_X_sequence using
    base := hbase,
    cutoff := N,
    recurrence := hrec

/-- Product recurrence with powers of the root-at-zero factor. -/
example {P : Nat → ℝ[X]} {m : Nat → Nat}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hrec : ∀ n : Nat, P (n + 1) = X ^ (m n) * P n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_X_pow_sequence using
    base := hbase,
    recurrence := hrec

/-- Root-zero-power recurrences also accept a cutoff row. -/
example {P : Nat → ℝ[X]} {m : Nat → Nat}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hrec : ∀ n : Nat, N ≤ n → P (n + 1) = P n * X ^ (m n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_X_pow_sequence using
    base := hbase,
    cutoff := N,
    recurrence := hrec

/-- Powered unit-slope recurrences accept the factor on the right. -/
example {P : Nat → ℝ[X]} {t : Nat → ℝ} {m : Nat → Nat}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hrec : ∀ n : Nat, P (n + 1) = P n * (X + C (t n)) ^ (m n)) :
    ∀ n : Nat, (P n).Splits := by
  rr_product_X_add_C_pow_sequence using
    base := hbase,
    recurrence := hrec

/-- Powered unit-slope recurrences can start from a cutoff row. -/
example {P : Nat → ℝ[X]} {t : Nat → ℝ} {m : Nat → Nat}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hrec : ∀ n : Nat,
      N ≤ n → P (n + 1) = (X + C (t n)) ^ (m n) * P n) :
    ∀ n : Nat, (P n).Splits := by
  rr_product_X_add_C_pow_sequence using
    base := hbase,
    cutoff := N,
    recurrence := hrec

/-- Powered constant-first unit-slope recurrences accept right factors. -/
example {P : Nat → ℝ[X]} {t : Nat → ℝ} {m : Nat → Nat}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hrec : ∀ n : Nat, P (n + 1) = P n * (C (t n) + X) ^ (m n)) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_product_C_add_X_pow_sequence using
    base := hbase,
    recurrence := hrec

/-- Powered constant-first unit-slope recurrences accept cutoff rows. -/
example {P : Nat → ℝ[X]} {t : Nat → ℝ} {m : Nat → Nat}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hrec : ∀ n : Nat,
      N ≤ n → P (n + 1) = P n * (C (t n) + X) ^ (m n)) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_product_C_add_X_pow_sequence using
    base := hbase,
    cutoff := N,
    recurrence := hrec

/-- Product recurrence with nonzero scalar-power factors. -/
example {P : Nat → ℝ[X]} {c : Nat → ℝ} {m : Nat → Nat}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hc : ∀ n : Nat, c n ≠ 0)
    (hrec : ∀ n : Nat, P (n + 1) = (C (c n) : ℝ[X]) ^ (m n) * P n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_C_pow_sequence using
    base := hbase,
    scalar_ne := hc,
    recurrence := hrec

/-- Positive scalar-power factors can be certified automatically. -/
example {P : Nat → ℝ[X]} {m : Nat → Nat}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hrec : ∀ n : Nat, P (n + 1) = P n * (C ((n : ℝ) + 1) : ℝ[X]) ^ (m n)) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_product_C_pow_sequence_auto using
    base := hbase,
    recurrence := hrec

/-- Scalar-power product recurrences can start from a cutoff row. -/
example {P : Nat → ℝ[X]} {c : Nat → ℝ} {m : Nat → Nat}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hc : ∀ n : Nat, c n ≠ 0)
    (hrec : ∀ n : Nat,
      N ≤ n → P (n + 1) = P n * (C (c n) : ℝ[X]) ^ (m n)) :
    ∀ n : Nat, (P n).Splits := by
  rr_product_C_pow_sequence using
    base := hbase,
    scalar_ne := hc,
    cutoff := N,
    recurrence := hrec

/-- Positive scalar-power factors are inferred from a cutoff row too. -/
example {P : Nat → ℝ[X]} {m : Nat → Nat}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hrec : ∀ n : Nat,
      N ≤ n → P (n + 1) = (C ((n : ℝ) + 1) : ℝ[X]) ^ (m n) * P n) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_product_C_pow_sequence_auto using
    base := hbase,
    cutoff := N,
    recurrence := hrec

/-- Product recurrence with powered affine factors. -/
example {P : Nat → ℝ[X]} {s t : Nat → ℝ} {m : Nat → Nat}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hs : ∀ n : Nat, s n ≠ 0)
    (hrec :
      ∀ n : Nat, P (n + 1) = (C (s n) * X + C (t n)) ^ (m n) * P n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_affine_pow_sequence using
    base := hbase,
    slope_ne := hs,
    recurrence := hrec

/-- Powered affine product recurrences can start from a cutoff row. -/
example {P : Nat → ℝ[X]} {s t : Nat → ℝ} {m : Nat → Nat}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hs : ∀ n : Nat, s n ≠ 0)
    (hrec : ∀ n : Nat,
      N ≤ n → P (n + 1) = P n * (C (s n) * X + C (t n)) ^ (m n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_affine_pow_sequence using
    base := hbase,
    slope_ne := hs,
    cutoff := N,
    recurrence := hrec

/-- Positive slopes in powered affine product recurrences are inferred. -/
example {P : Nat → ℝ[X]} {t : Nat → ℝ} {m : Nat → Nat}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hrec : ∀ n : Nat,
      P (n + 1) = (C ((n : ℝ) + 1) * X + C (t n)) ^ (m n) * P n) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_product_affine_pow_sequence_auto using
    base := hbase,
    recurrence := hrec

/-- Powered affine positive slopes are inferred from a cutoff row. -/
example {P : Nat → ℝ[X]} {t : Nat → ℝ} {m : Nat → Nat}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hrec : ∀ n : Nat,
      N ≤ n →
        P (n + 1) = (C ((n : ℝ) + 1) * X + C (t n)) ^ (m n) * P n) :
    ∀ n : Nat, (P n).Splits := by
  rr_product_affine_pow_sequence_auto using
    base := hbase,
    cutoff := N,
    recurrence := hrec

/-- Report-order powered affine recurrences also accept explicit slopes. -/
example {P : Nat → ℝ[X]} {s t : Nat → ℝ} {m : Nat → Nat}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hs : ∀ n : Nat, s n ≠ 0)
    (hrec :
      ∀ n : Nat, P (n + 1) = (C (t n) + C (s n) * X) ^ (m n) * P n) :
    ∀ n : Nat, (P n).Splits := by
  rr_product_const_first_affine_pow_sequence using
    base := hbase,
    slope_ne := hs,
    recurrence := hrec

/-- Report-order powered affine recurrences accept cutoff rows. -/
example {P : Nat → ℝ[X]} {s t : Nat → ℝ} {m : Nat → Nat}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hs : ∀ n : Nat, s n ≠ 0)
    (hrec : ∀ n : Nat,
      N ≤ n → P (n + 1) = P n * (C (t n) + C (s n) * X) ^ (m n)) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_product_const_first_affine_pow_sequence using
    base := hbase,
    slope_ne := hs,
    cutoff := N,
    recurrence := hrec

/-- Report-order powered affine recurrences also have an auto-positive form. -/
example {P : Nat → ℝ[X]} {t : Nat → ℝ} {m : Nat → Nat}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hrec : ∀ n : Nat,
      P (n + 1) = P n * (C (t n) + C ((n : ℝ) + 1) * X) ^ (m n)) :
    ∀ n : Nat, (P n).Splits := by
  rr_product_const_first_affine_pow_sequence_auto using
    base := hbase,
    recurrence := hrec

/-- Report-order powered affine auto routes accept cutoff rows. -/
example {P : Nat → ℝ[X]} {t : Nat → ℝ} {m : Nat → Nat}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hrec : ∀ n : Nat,
      N ≤ n →
        P (n + 1) = P n * (C (t n) + C ((n : ℝ) + 1) * X) ^ (m n)) :
    ∀ n : Nat, (P n).Splits := by
  rr_product_const_first_affine_pow_sequence_auto using
    base := hbase,
    cutoff := N,
    recurrence := hrec

/-- Sequence-level scalar product recurrence. -/
example {P : Nat → ℝ[X]} {a : Nat → ℝ}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (ha : ∀ n : Nat, a n ≠ 0)
    (hrec : ∀ n : Nat, P (n + 1) = C (a n) * P n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_scalar_sequence using
    base := hbase,
    scalar_ne := ha,
    recurrence := hrec

/-- Scalar product recurrences can start from a cutoff row. -/
example {P : Nat → ℝ[X]} {a : Nat → ℝ}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (ha : ∀ n : Nat, a n ≠ 0)
    (hrec : ∀ n : Nat, N ≤ n → P (n + 1) = C (a n) * P n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_scalar_sequence using
    base := hbase,
    scalar_ne := ha,
    cutoff := N,
    recurrence := hrec

/-- The scalar product recurrence also accepts the factor on the right. -/
example {P : Nat → ℝ[X]} {a : Nat → ℝ}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (ha : ∀ n : Nat, a n ≠ 0)
    (hrec : ∀ n : Nat, P (n + 1) = P n * C (a n)) :
    ∀ n : Nat, (P n).Splits := by
  rr_product_scalar_sequence using
    base := hbase,
    scalar_ne := ha,
    recurrence := hrec

/-- Automatic scalar certificate for positive product recurrences. -/
example {P : Nat → ℝ[X]}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hrec : ∀ n : Nat, P (n + 1) = C ((n : ℝ) + 1) * P n) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_product_scalar_sequence_auto using
    base := hbase,
    recurrence := hrec

/-- Automatic scalar certificates can start from a cutoff row. -/
example {P : Nat → ℝ[X]}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hrec : ∀ n : Nat, N ≤ n → P (n + 1) = P n * C ((n : ℝ) + 1)) :
    ∀ n : Nat, (P n).Splits := by
  rr_product_scalar_sequence_auto using
    base := hbase,
    cutoff := N,
    recurrence := hrec

/-- `A204420`: permutations of degree `2n` by number of even cycles.
Zero-based generator indexing gives
`P_{n+1}=((2n+1)t+(2n+1)(2n))P_n`. -/
example {P : Nat → ℝ[X]}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hrec : ∀ n : Nat,
      P (n + 1) =
        (C (2 * (n : ℝ) + 1) * X + C ((2 * (n : ℝ) + 1) * (2 * (n : ℝ)))) *
          P n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_affine_sequence_auto using
    base := hbase,
    recurrence := hrec

/-- Affine product recurrences can start from a cutoff row. -/
example {P : Nat → ℝ[X]} {s t : Nat → ℝ}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hs : ∀ n : Nat, s n ≠ 0)
    (hrec : ∀ n : Nat,
      N ≤ n → P (n + 1) = (C (s n) * X + C (t n)) * P n) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_product_affine_sequence using
    base := hbase,
    slope_ne := hs,
    cutoff := N,
    recurrence := hrec

/-- Automatic affine product recurrences can start from a cutoff row. -/
example {P : Nat → ℝ[X]} {t : Nat → ℝ}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hrec : ∀ n : Nat,
      N ≤ n → P (n + 1) = P n * (C ((n : ℝ) + 1) * X + C (t n))) :
    ∀ n : Nat, (P n).Splits := by
  rr_product_affine_sequence_auto using
    base := hbase,
    cutoff := N,
    recurrence := hrec

/-- Constant-first affine product recurrences accept cutoff rows. -/
example {P : Nat → ℝ[X]} {s t : Nat → ℝ}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hs : ∀ n : Nat, s n ≠ 0)
    (hrec : ∀ n : Nat,
      N ≤ n → P (n + 1) = (C (t n) + C (s n) * X) * P n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_const_first_sequence using
    base := hbase,
    slope_ne := hs,
    cutoff := N,
    recurrence := hrec

/-- Constant-first automatic affine recurrences accept cutoff rows. -/
example {P : Nat → ℝ[X]} {t : Nat → ℝ}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hrec : ∀ n : Nat,
      N ≤ n → P (n + 1) = P n * (C (t n) + C ((n : ℝ) + 1) * X)) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_product_const_first_sequence_auto using
    base := hbase,
    cutoff := N,
    recurrence := hrec

/-- Alternating scalar/linear product shell:
`P_{2m+1}=a_m P_{2m}` and `P_{2m+2}=(X+b_m)P_{2m+1}`. -/
example {P : Nat → ℝ[X]} {a b : Nat → ℝ}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (ha : ∀ n : Nat, a n ≠ 0)
    (hscalar : ∀ n : Nat, P (2 * n + 1) = C (a n) * P (2 * n))
    (hlinear : ∀ n : Nat, P (2 * n + 2) = (X + C (b n)) * P (2 * n + 1)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_scalar_linear_sequence using
    base := hbase,
    scalar_ne := ha,
    scalar_step := hscalar,
    linear_step := hlinear

/-- Alternating scalar/linear shell with report-order factors `C b_m + X`. -/
example {P : Nat → ℝ[X]} {a b : Nat → ℝ}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (ha : ∀ n : Nat, a n ≠ 0)
    (hscalar : ∀ n : Nat, P (2 * n + 1) = C (a n) * P (2 * n))
    (hlinear : ∀ n : Nat, P (2 * n + 2) = (C (b n) + X) * P (2 * n + 1)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_scalar_C_add_X_sequence using
    base := hbase,
    scalar_ne := ha,
    scalar_step := hscalar,
    linear_step := hlinear

/-- The constant-first alternating shell accepts right-side scalar and linear
steps. -/
example {P : Nat → ℝ[X]} {a b : Nat → ℝ}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (ha : ∀ n : Nat, a n ≠ 0)
    (hscalar : ∀ n : Nat, P (2 * n + 1) = P (2 * n) * C (a n))
    (hlinear : ∀ n : Nat, P (2 * n + 2) = P (2 * n + 1) * (C (b n) + X)) :
    ∀ n : Nat, (P n).Splits := by
  rr_product_scalar_C_add_X_sequence using
    base := hbase,
    scalar_ne := ha,
    scalar_step := hscalar,
    linear_step := hlinear

/-- Positive scalar steps in the constant-first alternating shell are inferred
automatically. -/
example {P : Nat → ℝ[X]} {b : Nat → ℝ}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hscalar : ∀ n : Nat,
      P (2 * n + 1) = C ((n : ℝ) + 1) * P (2 * n))
    (hlinear : ∀ n : Nat, P (2 * n + 2) = (C (b n) + X) * P (2 * n + 1)) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_product_scalar_C_add_X_sequence_auto using
    base := hbase,
    scalar_step := hscalar,
    linear_step := hlinear

/-- Alternating scalar/supplied-factor product shell. -/
example {P F : Nat → ℝ[X]} {a : Nat → ℝ}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (ha : ∀ n : Nat, a n ≠ 0)
    (hfactor : ∀ n : Nat, F n ≠ 0 ∧ (F n).Splits)
    (hscalar : ∀ n : Nat, P (2 * n + 1) = C (a n) * P (2 * n))
    (hstep : ∀ n : Nat, P (2 * n + 2) = F n * P (2 * n + 1)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_scalar_factor_sequence using
    base := hbase,
    scalar_ne := ha,
    factor_realrooted := hfactor,
    scalar_step := hscalar,
    factor_step := hstep

/-- The supplied-factor shell also has an automatic positive scalar form. -/
example {P F : Nat → ℝ[X]}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hfactor : ∀ n : Nat, F n ≠ 0 ∧ (F n).Splits)
    (hscalar : ∀ n : Nat,
      P (2 * n + 1) = C ((n : ℝ) + 1) * P (2 * n))
    (hstep : ∀ n : Nat, P (2 * n + 2) = F n * P (2 * n + 1)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_scalar_factor_sequence_auto using
    base := hbase,
    factor_realrooted := hfactor,
    scalar_step := hscalar,
    factor_step := hstep

/-- Alternating scalar/supplied-factor product shells can start from a cutoff. -/
example {P F : Nat → ℝ[X]} {a : Nat → ℝ}
    (N : Nat)
    (hbase : ∀ k : Nat, k ≤ 2 * N → P k ≠ 0 ∧ (P k).Splits)
    (ha : ∀ n : Nat, N ≤ n → a n ≠ 0)
    (hfactor : ∀ n : Nat, N ≤ n → F n ≠ 0 ∧ (F n).Splits)
    (hscalar : ∀ n : Nat, N ≤ n → P (2 * n + 1) = C (a n) * P (2 * n))
    (hstep : ∀ n : Nat, N ≤ n → P (2 * n + 2) = P (2 * n + 1) * F n) :
    ∀ n : Nat, (P n).Splits := by
  rr_product_scalar_factor_sequence using
    base := hbase,
    scalar_ne := ha,
    factor_realrooted := hfactor,
    cutoff := N,
    scalar_step := hscalar,
    factor_step := hstep

/-- The cutoff supplied-factor shell also has an automatic positive scalar form. -/
example {P F : Nat → ℝ[X]}
    (N : Nat)
    (hbase : ∀ k : Nat, k ≤ 2 * N → P k ≠ 0 ∧ (P k).Splits)
    (hfactor : ∀ n : Nat, N ≤ n → F n ≠ 0 ∧ (F n).Splits)
    (hscalar : ∀ n : Nat, N ≤ n →
      P (2 * n + 1) = C ((n : ℝ) + 1) * P (2 * n))
    (hstep : ∀ n : Nat, N ≤ n → P (2 * n + 2) = F n * P (2 * n + 1)) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_product_scalar_factor_sequence_auto using
    base := hbase,
    factor_realrooted := hfactor,
    cutoff := N,
    scalar_step := hscalar,
    factor_step := hstep

/-- The alternating scalar/supplied-factor shell accepts right scalar steps. -/
example {P F : Nat → ℝ[X]} {a : Nat → ℝ}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (ha : ∀ n : Nat, a n ≠ 0)
    (hfactor : ∀ n : Nat, F n ≠ 0 ∧ (F n).Splits)
    (hscalar : ∀ n : Nat, P (2 * n + 1) = P (2 * n) * C (a n))
    (hstep : ∀ n : Nat, P (2 * n + 2) = P (2 * n + 1) * F n) :
    ∀ n : Nat, (P n).Splits := by
  rr_product_scalar_factor_sequence using
    base := hbase,
    scalar_ne := ha,
    factor_realrooted := hfactor,
    scalar_step := hscalar,
    factor_step := hstep

/-- The alternating scalar/supplied-factor shell also accepts the factor on the right. -/
example {P F : Nat → ℝ[X]} {a : Nat → ℝ}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (ha : ∀ n : Nat, a n ≠ 0)
    (hfactor : ∀ n : Nat, F n ≠ 0 ∧ (F n).Splits)
    (hscalar : ∀ n : Nat, P (2 * n + 1) = C (a n) * P (2 * n))
    (hstep : ∀ n : Nat, P (2 * n + 2) = P (2 * n + 1) * F n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_scalar_factor_sequence using
    base := hbase,
    scalar_ne := ha,
    factor_realrooted := hfactor,
    scalar_step := hscalar,
    factor_step := hstep

/-- The alternating scalar/linear shell accepts right-side scalar and linear steps. -/
example {P : Nat → ℝ[X]} {a b : Nat → ℝ}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (ha : ∀ n : Nat, a n ≠ 0)
    (hscalar : ∀ n : Nat, P (2 * n + 1) = P (2 * n) * C (a n))
    (hlinear : ∀ n : Nat, P (2 * n + 2) = P (2 * n + 1) * (X + C (b n))) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_scalar_linear_sequence using
    base := hbase,
    scalar_ne := ha,
    scalar_step := hscalar,
    linear_step := hlinear

/-- The alternating scalar/unit-linear shell can start from a cutoff. -/
example {P : Nat → ℝ[X]} {a b : Nat → ℝ}
    (N : Nat)
    (hbase : ∀ k : Nat, k ≤ 2 * N → P k ≠ 0 ∧ (P k).Splits)
    (ha : ∀ n : Nat, N ≤ n → a n ≠ 0)
    (hscalar : ∀ n : Nat, N ≤ n → P (2 * n + 1) = C (a n) * P (2 * n))
    (hlinear :
      ∀ n : Nat, N ≤ n → P (2 * n + 2) = P (2 * n + 1) * (X + C (b n))) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_product_scalar_linear_sequence using
    base := hbase,
    scalar_ne := ha,
    cutoff := N,
    scalar_step := hscalar,
    linear_step := hlinear

/-- The cutoff scalar/unit-linear shell has an automatic positive scalar form. -/
example {P : Nat → ℝ[X]} {b : Nat → ℝ}
    (N : Nat)
    (hbase : ∀ k : Nat, k ≤ 2 * N → P k ≠ 0 ∧ (P k).Splits)
    (hscalar : ∀ n : Nat, N ≤ n →
      P (2 * n + 1) = C ((n : ℝ) + 1) * P (2 * n))
    (hlinear :
      ∀ n : Nat, N ≤ n → P (2 * n + 2) = (C (b n) + X) * P (2 * n + 1)) :
    ∀ n : Nat, (P n).Splits := by
  rr_product_scalar_C_add_X_sequence_auto using
    base := hbase,
    cutoff := N,
    scalar_step := hscalar,
    linear_step := hlinear

/-- Degree-plateau product shell with a repeated-zero factor on the growth step. -/
example {P : Nat → ℝ[X]}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hscalar : ∀ n : Nat,
      P (2 * n + 1) = C (2 * (n : ℝ) + 1) * P (2 * n))
    (hstep : ∀ n : Nat, P (2 * n + 2) = ((X : ℝ[X]) ^ 2) * P (2 * n + 1)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_scalar_X_pow_sequence_auto using
    base := hbase,
    scalar_step := hscalar,
    factor_step := hstep

/-- The repeated-zero alternating shell also accepts explicit scalar
certificates and right-side steps. -/
example {P : Nat → ℝ[X]} {a : Nat → ℝ} {m : Nat → Nat}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (ha : ∀ n : Nat, a n ≠ 0)
    (hscalar : ∀ n : Nat, P (2 * n + 1) = P (2 * n) * C (a n))
    (hstep : ∀ n : Nat, P (2 * n + 2) = P (2 * n + 1) * X ^ (m n)) :
    ∀ n : Nat, (P n).Splits := by
  rr_product_scalar_X_pow_sequence using
    base := hbase,
    scalar_ne := ha,
    scalar_step := hscalar,
    factor_step := hstep

/-- The repeated-zero alternating shell can start from a cutoff. -/
example {P : Nat → ℝ[X]} {m : Nat → Nat}
    (N : Nat)
    (hbase : ∀ k : Nat, k ≤ 2 * N → P k ≠ 0 ∧ (P k).Splits)
    (hscalar : ∀ n : Nat, N ≤ n →
      P (2 * n + 1) = C ((n : ℝ) + 1) * P (2 * n))
    (hstep : ∀ n : Nat, N ≤ n → P (2 * n + 2) = P (2 * n + 1) * X ^ (m n)) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_product_scalar_X_pow_sequence_auto using
    base := hbase,
    cutoff := N,
    scalar_step := hscalar,
    factor_step := hstep

/-- Alternating scalar/powered unit-linear shell. -/
example {P : Nat → ℝ[X]} {a b : Nat → ℝ} {m : Nat → Nat}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (ha : ∀ n : Nat, a n ≠ 0)
    (hscalar : ∀ n : Nat, P (2 * n + 1) = C (a n) * P (2 * n))
    (hstep : ∀ n : Nat,
      P (2 * n + 2) = (X + C (b n)) ^ (m n) * P (2 * n + 1)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_scalar_X_add_C_pow_sequence using
    base := hbase,
    scalar_ne := ha,
    scalar_step := hscalar,
    factor_step := hstep

/-- Powered unit-linear shells can start from a cutoff. -/
example {P : Nat → ℝ[X]} {a b : Nat → ℝ} {m : Nat → Nat}
    (N : Nat)
    (hbase : ∀ k : Nat, k ≤ 2 * N → P k ≠ 0 ∧ (P k).Splits)
    (ha : ∀ n : Nat, N ≤ n → a n ≠ 0)
    (hscalar : ∀ n : Nat, N ≤ n → P (2 * n + 1) = P (2 * n) * C (a n))
    (hstep : ∀ n : Nat, N ≤ n →
      P (2 * n + 2) = P (2 * n + 1) * (X + C (b n)) ^ (m n)) :
    ∀ n : Nat, (P n).Splits := by
  rr_product_scalar_X_add_C_pow_sequence using
    base := hbase,
    scalar_ne := ha,
    cutoff := N,
    scalar_step := hscalar,
    factor_step := hstep

/-- Positive scalar steps in the powered unit-linear shell are inferred. -/
example {P : Nat → ℝ[X]} {b : Nat → ℝ} {m : Nat → Nat}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hscalar : ∀ n : Nat,
      P (2 * n + 1) = C ((n : ℝ) + 1) * P (2 * n))
    (hstep : ∀ n : Nat,
      P (2 * n + 2) = (X + C (b n)) ^ (m n) * P (2 * n + 1)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_scalar_X_add_C_pow_sequence_auto using
    base := hbase,
    scalar_step := hscalar,
    factor_step := hstep

/-- Alternating scalar/powered constant-first shell. -/
example {P : Nat → ℝ[X]} {a b : Nat → ℝ} {m : Nat → Nat}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (ha : ∀ n : Nat, a n ≠ 0)
    (hscalar : ∀ n : Nat, P (2 * n + 1) = C (a n) * P (2 * n))
    (hstep : ∀ n : Nat,
      P (2 * n + 2) = (C (b n) + X) ^ (m n) * P (2 * n + 1)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_scalar_C_add_X_pow_sequence using
    base := hbase,
    scalar_ne := ha,
    scalar_step := hscalar,
    factor_step := hstep

/-- The powered constant-first shell accepts automatic positive scalar
certificates and right-side growth factors. -/
example {P : Nat → ℝ[X]} {b : Nat → ℝ} {m : Nat → Nat}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hscalar : ∀ n : Nat,
      P (2 * n + 1) = C (2 * (n : ℝ) + 1) * P (2 * n))
    (hstep : ∀ n : Nat,
      P (2 * n + 2) = P (2 * n + 1) * (C (b n) + X) ^ (m n)) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_product_scalar_C_add_X_pow_sequence_auto using
    base := hbase,
    scalar_step := hscalar,
    factor_step := hstep

/-- Powered constant-first shells have cutoff automatic scalar support. -/
example {P : Nat → ℝ[X]} {b : Nat → ℝ} {m : Nat → Nat}
    (N : Nat)
    (hbase : ∀ k : Nat, k ≤ 2 * N → P k ≠ 0 ∧ (P k).Splits)
    (hscalar : ∀ n : Nat, N ≤ n →
      P (2 * n + 1) = C (2 * (n : ℝ) + 1) * P (2 * n))
    (hstep : ∀ n : Nat, N ≤ n →
      P (2 * n + 2) = (C (b n) + X) ^ (m n) * P (2 * n + 1)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_scalar_C_add_X_pow_sequence_auto using
    base := hbase,
    cutoff := N,
    scalar_step := hscalar,
    factor_step := hstep

/-- Parity lift for product exits where odd rows are scalar multiples of
`X` times the even quotient. -/
example {P Q : Nat → ℝ[X]} {a : Nat → ℝ}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (ha : ∀ n : Nat, a n ≠ 0)
    (heven : ∀ n : Nat, P (2 * n) = Q n)
    (hodd : ∀ n : Nat, P (2 * n + 1) = C (a n) * X * Q n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_even_product_odd_X_scalar_sequence using
    even_realrooted := hquot,
    scalar_ne := ha,
    even_factorization := heven,
    odd_factorization := hodd

/-- A137477-style route: prove the even quotient by supplied product factors,
then lift the odd rows by the parity scalar-`X` wrapper. -/
example {P Q F : Nat → ℝ[X]} {a : Nat → ℝ}
    (hbase : Q 0 ≠ 0 ∧ (Q 0).Splits)
    (hfactor : ∀ n : Nat, F n ≠ 0 ∧ (F n).Splits)
    (hstep : ∀ n : Nat, Q (n + 1) = F n * Q n)
    (ha : ∀ n : Nat, a n ≠ 0)
    (heven : ∀ n : Nat, P (2 * n) = Q n)
    (hodd : ∀ n : Nat, P (2 * n + 1) = C (a n) * X * Q n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  have hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits := by
    rr_product_factor_sequence using
      base := hbase,
      factor_realrooted := hfactor,
      recurrence := hstep
  rr_even_product_odd_X_scalar_sequence using
    even_realrooted := hquot,
    scalar_ne := ha,
    even_factorization := heven,
    odd_factorization := hodd

/-- `A060523`: permutations by number of even cycles.  In product form,
`P_{2m+1}=(2m+1)P_{2m}` and
`P_{2m+2}=(X+(2m+1))P_{2m+1}`. -/
example {P : Nat → ℝ[X]}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hscalar : ∀ n : Nat,
      P (2 * n + 1) = C (2 * (n : ℝ) + 1) * P (2 * n))
    (hlinear : ∀ n : Nat,
      P (2 * n + 2) = (X + C (2 * (n : ℝ) + 1)) * P (2 * n + 1)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_scalar_linear_sequence_auto using
    base := hbase,
    scalar_step := hscalar,
    linear_step := hlinear

end Tactic
end RealRooted
