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

example {c : ℝ} (hc : c ≠ 0) : c ≠ 0 := by
  rr_product_nonzero

example {n : Nat} : (n : ℝ) + 1 ≠ 0 := by
  rr_product_nonzero

example {n : Nat} : 2 * (n : ℝ) + 1 ≠ 0 := by
  rr_product_nonzero

example {a : ℝ} (ha : a ≠ 0) :
    (C a : ℝ[X]) ≠ 0 ∧ (C a : ℝ[X]).Splits := by
  rr_product_C using scalar_ne := ha

example {a : ℝ} (ha : a ≠ 0) :
    (C a : ℝ[X]).Splits := by
  rr_product_C using scalar_ne := ha

example {n : Nat} :
    (C ((n : ℝ) + 1) : ℝ[X]) ≠ 0 := by
  rr_product_C_auto

example {a : ℝ} (ha : a ≠ 0) :
    ((C a : ℝ[X]) ^ 2).Splits := by
  rr_product_C_pow using
    scalar_ne := ha,
    exponent := 2

example :
    (X : ℝ[X]) ≠ 0 ∧ (X : ℝ[X]).Splits := by
  rr_product_X

example {n : Nat} :
    ((X : ℝ[X]) ^ n).Splits := by
  rr_product_X_pow using exponent := n

example :
    (X + X ^ 2 : ℝ[X]) ≠ 0 ∧ (X + X ^ 2 : ℝ[X]).Splits := by
  rr_product_normalize using
    RealRooted.isRealRooted_mul_X_add_C
      (p := (X : ℝ[X])) (t := (1 : ℝ)) RealRooted.isRealRooted_X

example {p q : ℝ[X]} (hp : p ≠ 0 ∧ p.Splits) (hq : q ≠ 0 ∧ q.Splits) :
    p * q ≠ 0 ∧ (p * q).Splits := by
  rr_mul_realrooted using hp, hq

example {p q : ℝ[X]} (hp : p ≠ 0 ∧ p.Splits) (hq : q ≠ 0 ∧ q.Splits) :
    (p * q).Splits := by
  rr_mul_realrooted using
    left := hp,
    right := hq

example {p q : ℝ[X]} (hp : p ≠ 0 ∧ p.Splits) (hq : q ≠ 0 ∧ q.Splits) :
    q * p ≠ 0 ∧ (q * p).Splits := by
  rr_mul_realrooted using
    left := hp,
    right := hq

example {p : ℝ[X]} {n : Nat} (hp : p ≠ 0 ∧ p.Splits) :
    p ^ n ≠ 0 ∧ (p ^ n).Splits := by
  rr_pow_realrooted using
    realrooted := hp,
    exponent := n

example {p : ℝ[X]} {n : Nat} (hp : p ≠ 0 ∧ p.Splits) :
    (p ^ n).Splits := by
  rr_pow_realrooted using
    realrooted := hp,
    exponent := n

example {p : ℝ[X]} {n : Nat} (hp : p ≠ 0 ∧ p.Splits) :
    p ^ n ≠ 0 := by
  rr_pow_realrooted using
    realrooted := hp,
    exponent := n

example {t : ℝ} :
    (X + C t : ℝ[X]).Splits := by
  rr_product_X_add_C using constant := t

example {t : ℝ} :
    (C t + X : ℝ[X]) ≠ 0 := by
  rr_product_C_add_X using constant := t

example {t : ℝ} :
    ((X + C t : ℝ[X]) ^ 3 ≠ 0 ∧ ((X + C t : ℝ[X]) ^ 3).Splits) := by
  rr_product_X_add_C_pow using
    constant := t,
    exponent := 3

example :
    (1 + 3 * X + 3 * X ^ 2 + X ^ 3 : ℝ[X]) ≠ 0 ∧
      (1 + 3 * X + 3 * X ^ 2 + X ^ 3 : ℝ[X]).Splits := by
  rr_product_normalize using
    RealRooted.isRealRooted_X_add_C_pow (1 : ℝ) 3

example {s t : ℝ} (hs : s ≠ 0) :
    (C s * X + C t : ℝ[X]).Splits := by
  rr_product_affine using slope_ne := hs

example {s t : ℝ} (hs : s ≠ 0) :
    (C t + C s * X : ℝ[X]) ≠ 0 := by
  rr_product_const_first_affine using slope_ne := hs

example {t : ℝ} :
    (C (2 : ℝ) * X + C t : ℝ[X]).Splits := by
  rr_product_affine_auto

example {s t : ℝ} (hs : s ≠ 0) :
    ((C s * X + C t : ℝ[X]) ^ 2).Splits := by
  rr_product_affine_pow using
    slope_ne := hs,
    exponent := 2

example {t : ℝ} :
    ((C t + C (3 : ℝ) * X : ℝ[X]) ^ 2) ≠ 0 := by
  rr_product_const_first_affine_pow_auto using exponent := 2

example {p : ℝ[X]} {s t : ℝ} (hp : p ≠ 0 ∧ p.Splits) (hs : s ≠ 0) :
    ((C s * X + C t) * p ≠ 0 ∧ ((C s * X + C t) * p).Splits) := by
  rr_product_factor using hp, hs

example {p : ℝ[X]} {s t : ℝ} (hp : p ≠ 0 ∧ p.Splits) (hs : s ≠ 0) :
    (C s * X + C t) * p ≠ 0 := by
  rr_product_factor using hp, hs

example {p : ℝ[X]} {s t : ℝ} (hp : p ≠ 0 ∧ p.Splits) (hs : s ≠ 0) :
    ((C s * X + C t) * p).Splits := by
  rr_product_factor using hp, hs

example {p : ℝ[X]} {s t : ℝ} (hp : p ≠ 0 ∧ p.Splits) (hs : s ≠ 0) :
    (p * (C s * X + C t) ≠ 0 ∧ (p * (C s * X + C t)).Splits) := by
  rr_product_factor using
    realrooted := hp,
    slope_ne := hs

example {p : ℝ[X]} {s t : ℝ} (hp : p ≠ 0 ∧ p.Splits) (hs : s ≠ 0) :
    ((C t + C s * X) * p ≠ 0 ∧ ((C t + C s * X) * p).Splits) := by
  rr_product_factor_const_first using hp, hs

example {p : ℝ[X]} {s t : ℝ} (hp : p ≠ 0 ∧ p.Splits) (hs : s ≠ 0) :
    (p * (C t + C s * X) ≠ 0 ∧ (p * (C t + C s * X)).Splits) := by
  rr_product_factor_const_first using
    realrooted := hp,
    slope_ne := hs

example {p : ℝ[X]} {t : ℝ} (hp : p ≠ 0 ∧ p.Splits) :
    ((X + C t) * p ≠ 0 ∧ ((X + C t) * p).Splits) := by
  rr_product_factor_X using hp

example {p : ℝ[X]} {t : ℝ} (hp : p ≠ 0 ∧ p.Splits) :
    (p * (X + C t) ≠ 0 ∧ (p * (X + C t)).Splits) := by
  rr_product_factor_X using
    realrooted := hp

example {p : ℝ[X]} {t : ℝ} (hp : p ≠ 0 ∧ p.Splits) :
    ((C t + X) * p ≠ 0 ∧ ((C t + X) * p).Splits) := by
  rr_product_factor_C_add_X using hp

example {p : ℝ[X]} {t : ℝ} (hp : p ≠ 0 ∧ p.Splits) :
    (p * (C t + X) ≠ 0 ∧ (p * (C t + X)).Splits) := by
  rr_product_factor_C_add_X using
    realrooted := hp

/-- Sequence-level product recurrence with supplied real-rooted factors. -/
example {P F : Nat → ℝ[X]}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hfactor : ∀ n : Nat, F n ≠ 0 ∧ (F n).Splits)
    (hrec : ∀ n : Nat, P (n + 1) = F n * P n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_factor_sequence using hbase, hfactor, hrec

example {P F : Nat → ℝ[X]}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hfactor : ∀ n : Nat, F n ≠ 0 ∧ (F n).Splits)
    (hrec : ∀ n : Nat, P (n + 1) = F n * P n) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_product_factor_sequence using
    base := hbase,
    factor_realrooted := hfactor,
    recurrence := hrec

example {P F : Nat → ℝ[X]}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hfactor : ∀ n : Nat, F n ≠ 0 ∧ (F n).Splits)
    (hrec : ∀ n : Nat, P (n + 1) = F n * P n) :
    ∀ n : Nat, (P n).Splits := by
  rr_product_factor_sequence using
    base := hbase,
    factor_realrooted := hfactor,
    recurrence := hrec

/-- The supplied-factor sequence macro also accepts the factor on the right. -/
example {P F : Nat → ℝ[X]}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hfactor : ∀ n : Nat, F n ≠ 0 ∧ (F n).Splits)
    (hrec : ∀ n : Nat, P (n + 1) = P n * F n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_factor_sequence using
    base := hbase,
    factor_realrooted := hfactor,
    recurrence := hrec

/-- Supplied-factor product recurrences can start after finitely many base rows. -/
example {P F : Nat → ℝ[X]}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hfactor : ∀ n : Nat, N ≤ n → F n ≠ 0 ∧ (F n).Splits)
    (hrec : ∀ n : Nat, N ≤ n → P (n + 1) = F n * P n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_factor_sequence using
    base := hbase,
    factor_realrooted := hfactor,
    cutoff := N,
    recurrence := hrec

/-- Tail-start supplied-factor product recurrences accept right factors too. -/
example {P F : Nat → ℝ[X]}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hfactor : ∀ n : Nat, N ≤ n → F n ≠ 0 ∧ (F n).Splits)
    (hrec : ∀ n : Nat, N ≤ n → P (n + 1) = P n * F n) :
    ∀ n : Nat, (P n).Splits := by
  rr_product_factor_sequence using
    base := hbase,
    factor_realrooted := hfactor,
    cutoff := N,
    recurrence := hrec

/-- Direct finite-product formula route. -/
example {P : Nat → ℝ[X]} {root : Nat → Nat → ℝ}
    (hroot : ∀ n : Nat,
      P n = ∏ j ∈ Finset.range n, (X - C (root n j))) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_affine_product_sequence using formula := hroot

/-- Scalar finite-product formula route, used by factorable J1 shells. -/
example {P : Nat → ℝ[X]} {c : Nat → ℝ} {rootCount : Nat → Nat}
    {roots : Nat → Nat → ℝ}
    (hc : ∀ n : Nat, c n ≠ 0)
    (hroot : ∀ n : Nat,
      P n = C (c n) *
        ∏ j ∈ Finset.range (rootCount n), (X - C (roots n j))) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_j1_factorable_lag3_sequence_realrooted using
    scalar_ne_zero := hc,
    root_grid := hroot

/-- `A010054`-style product exit: the active rows are constant in `n`. -/
example {P : Nat → ℝ[X]}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hrec : ∀ n : Nat, P (n + 1) = P n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_identity_sequence using hbase, hrec

/-- Projection endpoint for the identity product exit. -/
example {P : Nat → ℝ[X]}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hrec : ∀ n : Nat, P (n + 1) = P n) :
    ∀ n : Nat, (P n).Splits := by
  rr_product_identity_sequence using
    base := hbase,
    recurrence := hrec

/-- Nonzero projection endpoint for the identity product exit. -/
example {P : Nat → ℝ[X]}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hrec : ∀ n : Nat, P (n + 1) = P n) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_product_identity_sequence using
    base := hbase,
    recurrence := hrec

/-- Identity product exits can start after finitely many base rows. -/
example {P : Nat → ℝ[X]}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hrec : ∀ n : Nat, N ≤ n → P (n + 1) = P n) :
    ∀ n : Nat, (P n).Splits := by
  rr_product_identity_sequence using
    base := hbase,
    cutoff := N,
    recurrence := hrec

/-- `A103451`-style product exit: each active row gains one root at zero. -/
example {P : Nat → ℝ[X]}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hrec : ∀ n : Nat, P (n + 1) = X * P n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_root_zero_sequence using hbase, hrec

/-- Nonzero projection endpoint for root-zero product exits. -/
example {P : Nat → ℝ[X]}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hrec : ∀ n : Nat, P (n + 1) = X * P n) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_product_root_zero_sequence using
    base := hbase,
    recurrence := hrec

/-- Splitting projection endpoint for root-zero product exits. -/
example {P : Nat → ℝ[X]}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hrec : ∀ n : Nat, P (n + 1) = X * P n) :
    ∀ n : Nat, (P n).Splits := by
  rr_product_root_zero_sequence using
    base := hbase,
    recurrence := hrec

/-- `A122431`-style product exit, accepting the root-zero factor on the right. -/
example {P : Nat → ℝ[X]}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hrec : ∀ n : Nat, P (n + 1) = P n * X) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_product_root_zero_sequence using
    base := hbase,
    recurrence := hrec

/-- Splitting projection endpoint for right root-zero product exits. -/
example {P : Nat → ℝ[X]}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hrec : ∀ n : Nat, P (n + 1) = P n * X) :
    ∀ n : Nat, (P n).Splits := by
  rr_product_root_zero_sequence using
    base := hbase,
    recurrence := hrec

/-- Root-zero product exits can start after finitely many base rows. -/
example {P : Nat → ℝ[X]}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hrec : ∀ n : Nat, N ≤ n → P (n + 1) = P n * X) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_root_zero_sequence using
    base := hbase,
    cutoff := N,
    recurrence := hrec

/-- `A266178`-style product exit: two real-rooted base parities repeat. -/
example {P : Nat → ℝ[X]}
    (hbase_zero : P 0 ≠ 0 ∧ (P 0).Splits)
    (hbase_one : P 1 ≠ 0 ∧ (P 1).Splits)
    (hrec : ∀ n : Nat, P (n + 2) = P n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_period_two_sequence using hbase_zero, hbase_one, hrec

/-- Projection endpoint for two-periodic product exits. -/
example {P : Nat → ℝ[X]}
    (hbase_zero : P 0 ≠ 0 ∧ (P 0).Splits)
    (hbase_one : P 1 ≠ 0 ∧ (P 1).Splits)
    (hrec : ∀ n : Nat, P (n + 2) = P n) :
    ∀ n : Nat, (P n).Splits := by
  rr_product_period_two_sequence using
    base_zero := hbase_zero,
    base_one := hbase_one,
    recurrence := hrec

/-- Nonzero projection endpoint for two-periodic product exits. -/
example {P : Nat → ℝ[X]}
    (hbase_zero : P 0 ≠ 0 ∧ (P 0).Splits)
    (hbase_one : P 1 ≠ 0 ∧ (P 1).Splits)
    (hrec : ∀ n : Nat, P (n + 2) = P n) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_product_period_two_sequence using
    base_zero := hbase_zero,
    base_one := hbase_one,
    recurrence := hrec

/-- Period-two product exits can start from any finite cutoff row. -/
example {P : Nat → ℝ[X]}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N + 1 → P n ≠ 0 ∧ (P n).Splits)
    (hrec : ∀ n : Nat, N ≤ n → P (n + 2) = P n) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_product_period_two_sequence using
    base := hbase,
    cutoff := N,
    recurrence := hrec

/-- Row-wise product lift from a proved quotient sequence. -/
example {P Q F : Nat → ℝ[X]}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hfactor : ∀ n : Nat, F n ≠ 0 ∧ (F n).Splits)
    (hrow : ∀ n : Nat, P n = F n * Q n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_lift_sequence using hquot, hfactor, hrow

/-- The product lift also accepts the quotient factor on the left. -/
example {P Q F : Nat → ℝ[X]}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hfactor : ∀ n : Nat, F n ≠ 0 ∧ (F n).Splits)
    (hrow : ∀ n : Nat, P n = Q n * F n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_lift_sequence using
    quotient_realrooted := hquot,
    factor_realrooted := hfactor,
    factorization := hrow

/-- Product lifts can start after a finite base interval. -/
example {P Q F : Nat → ℝ[X]}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hquot : ∀ n : Nat, N ≤ n → Q n ≠ 0 ∧ (Q n).Splits)
    (hfactor : ∀ n : Nat, N ≤ n → F n ≠ 0 ∧ (F n).Splits)
    (hrow : ∀ n : Nat, N ≤ n → P n = Q n * F n) :
    ∀ n : Nat, (P n).Splits := by
  rr_product_lift_sequence using
    base := hbase,
    quotient_realrooted := hquot,
    factor_realrooted := hfactor,
    cutoff := N,
    factorization := hrow

/-- `A155112`-style persistent root at zero: `P_n = X Q_n`. -/
example {P Q : Nat → ℝ[X]}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, P n = X * Q n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_lift_X_sequence using
    quotient_realrooted := hquot,
    factorization := hrow

/-- Persistent root-at-zero lifts can start after a finite base interval. -/
example {P Q : Nat → ℝ[X]}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hquot : ∀ n : Nat, N ≤ n → Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, N ≤ n → P n = Q n * X) :
    ∀ n : Nat, (P n).Splits := by
  rr_product_lift_X_sequence using
    base := hbase,
    quotient_realrooted := hquot,
    cutoff := N,
    factorization := hrow

/-- Row-wise unit-slope linear lift for rows `P_n = (X+t_n) Q_n`. -/
example {P Q : Nat → ℝ[X]} {t : Nat → ℝ}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, P n = (X + C (t n)) * Q n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_lift_X_add_C_sequence using
    quotient_realrooted := hquot,
    factorization := hrow

/-- Unit-slope linear lifts also accept the quotient factor on the left. -/
example {P Q : Nat → ℝ[X]} {t : Nat → ℝ}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, P n = Q n * (X + C (t n))) :
    ∀ n : Nat, (P n).Splits := by
  rr_product_lift_X_add_C_sequence using
    quotient_realrooted := hquot,
    factorization := hrow

/-- Unit-slope linear lifts can start after a finite base interval. -/
example {P Q : Nat → ℝ[X]} {t : Nat → ℝ}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hquot : ∀ n : Nat, N ≤ n → Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, N ≤ n → P n = (X + C (t n)) * Q n) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_product_lift_X_add_C_sequence using
    base := hbase,
    quotient_realrooted := hquot,
    cutoff := N,
    factorization := hrow

/-- Constant-first unit-slope lifts accept rows `P_n = (t_n+X) Q_n`. -/
example {P Q : Nat → ℝ[X]} {t : Nat → ℝ}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, P n = (C (t n) + X) * Q n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_lift_C_add_X_sequence using
    quotient_realrooted := hquot,
    factorization := hrow

/-- Constant-first unit-slope lifts also accept the factor on the right. -/
example {P Q : Nat → ℝ[X]} {t : Nat → ℝ}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, P n = Q n * (C (t n) + X)) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_product_lift_C_add_X_sequence using
    quotient_realrooted := hquot,
    factorization := hrow

/-- Constant-first unit-slope lifts can also start from a cutoff. -/
example {P Q : Nat → ℝ[X]} {t : Nat → ℝ}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hquot : ∀ n : Nat, N ≤ n → Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, N ≤ n → P n = Q n * (C (t n) + X)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_lift_C_add_X_sequence using
    base := hbase,
    quotient_realrooted := hquot,
    cutoff := N,
    factorization := hrow

/-- Nonzero scalar lift for rows `P_n = c_n Q_n`. -/
example {P Q : Nat → ℝ[X]} {c : Nat → ℝ}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hc : ∀ n : Nat, c n ≠ 0)
    (hrow : ∀ n : Nat, P n = C (c n) * Q n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_lift_C_sequence using
    quotient_realrooted := hquot,
    scalar_ne := hc,
    factorization := hrow

/-- The scalar lift also accepts the quotient factor on the left. -/
example {P Q : Nat → ℝ[X]} {c : Nat → ℝ}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hc : ∀ n : Nat, c n ≠ 0)
    (hrow : ∀ n : Nat, P n = Q n * C (c n)) :
    ∀ n : Nat, (P n).Splits := by
  rr_product_lift_C_sequence using
    quotient_realrooted := hquot,
    scalar_ne := hc,
    factorization := hrow

/-- Automatic scalar certificate for positive scalar lifts. -/
example {P Q : Nat → ℝ[X]}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, P n = C ((n : ℝ) + 1) * Q n) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_product_lift_C_sequence_auto using
    quotient_realrooted := hquot,
    factorization := hrow

/-- Automatic scalar certificates also work when the scalar is on the right. -/
example {P Q : Nat → ℝ[X]}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, P n = Q n * C ((n : ℝ) + 1)) :
    ∀ n : Nat, (P n).Splits := by
  rr_product_lift_C_sequence_auto using
    quotient_realrooted := hquot,
    factorization := hrow

/-- Row-wise affine linear lift for rows `P_n = (s_n X+t_n) Q_n`. -/
example {P Q : Nat → ℝ[X]} {s t : Nat → ℝ}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hs : ∀ n : Nat, s n ≠ 0)
    (hrow : ∀ n : Nat, P n = (C (s n) * X + C (t n)) * Q n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_lift_affine_sequence using
    quotient_realrooted := hquot,
    slope_ne := hs,
    factorization := hrow

/-- Constant-first affine linear lifts accept the quotient factor on the left. -/
example {P Q : Nat → ℝ[X]} {s t : Nat → ℝ}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hs : ∀ n : Nat, s n ≠ 0)
    (hrow : ∀ n : Nat, P n = Q n * (C (t n) + C (s n) * X)) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_product_lift_const_first_sequence using
    quotient_realrooted := hquot,
    slope_ne := hs,
    factorization := hrow

/-- Positive row-wise affine slopes can be certified automatically. -/
example {P Q : Nat → ℝ[X]} {t : Nat → ℝ}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, P n = (C ((n : ℝ) + 1) * X + C (t n)) * Q n) :
    ∀ n : Nat, (P n).Splits := by
  rr_product_lift_affine_sequence_auto using
    quotient_realrooted := hquot,
    factorization := hrow

/-- Positive row-wise affine slopes are also inferred for right factors. -/
example {P Q : Nat → ℝ[X]} {t : Nat → ℝ}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, P n = Q n * (C ((n : ℝ) + 1) * X + C (t n))) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_product_lift_affine_sequence_auto using
    quotient_realrooted := hquot,
    factorization := hrow

/-- Constant-first positive slopes use the same automatic certificate path. -/
example {P Q : Nat → ℝ[X]} {t : Nat → ℝ}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, P n = (C (t n) + C ((n : ℝ) + 1) * X) * Q n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_lift_const_first_sequence_auto using
    quotient_realrooted := hquot,
    factorization := hrow

/-- Nonzero scalar-power lift for rows `P_n = c_n^{m_n} Q_n`. -/
example {P Q : Nat → ℝ[X]} {c : Nat → ℝ} {m : Nat → Nat}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hc : ∀ n : Nat, c n ≠ 0)
    (hrow : ∀ n : Nat, P n = (C (c n) : ℝ[X]) ^ (m n) * Q n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_lift_C_pow_sequence using
    quotient_realrooted := hquot,
    scalar_ne := hc,
    factorization := hrow

/-- The scalar-power lift also accepts the quotient factor on the left. -/
example {P Q : Nat → ℝ[X]} {c : Nat → ℝ} {m : Nat → Nat}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hc : ∀ n : Nat, c n ≠ 0)
    (hrow : ∀ n : Nat, P n = Q n * (C (c n) : ℝ[X]) ^ (m n)) :
    ∀ n : Nat, (P n).Splits := by
  rr_product_lift_C_pow_sequence using
    quotient_realrooted := hquot,
    scalar_ne := hc,
    factorization := hrow

/-- Automatic scalar certificate for positive scalar-power lifts. -/
example {P Q : Nat → ℝ[X]} {m : Nat → Nat}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, P n = (C ((n : ℝ) + 1) : ℝ[X]) ^ (m n) * Q n) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_product_lift_C_pow_sequence_auto using
    quotient_realrooted := hquot,
    factorization := hrow

/-- Automatic scalar certificates also work for right scalar-power lifts. -/
example {P Q : Nat → ℝ[X]} {m : Nat → Nat}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, P n = Q n * (C ((n : ℝ) + 1) : ℝ[X]) ^ (m n)) :
    ∀ n : Nat, (P n).Splits := by
  rr_product_lift_C_pow_sequence_auto using
    quotient_realrooted := hquot,
    factorization := hrow

/-- Scalar lifts can start after a finite base interval. -/
example {P Q : Nat → ℝ[X]} {c : Nat → ℝ}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hquot : ∀ n : Nat, N ≤ n → Q n ≠ 0 ∧ (Q n).Splits)
    (hc : ∀ n : Nat, N ≤ n → c n ≠ 0)
    (hrow : ∀ n : Nat, N ≤ n → P n = Q n * C (c n)) :
    ∀ n : Nat, (P n).Splits := by
  rr_product_lift_C_sequence using
    base := hbase,
    quotient_realrooted := hquot,
    scalar_ne := hc,
    cutoff := N,
    factorization := hrow

/-- Automatic scalar certificates also work after a cutoff. -/
example {P Q : Nat → ℝ[X]}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hquot : ∀ n : Nat, N ≤ n → Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, N ≤ n → P n = C ((n : ℝ) + 1) * Q n) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_product_lift_C_sequence_auto using
    base := hbase,
    quotient_realrooted := hquot,
    cutoff := N,
    factorization := hrow

/-- Affine linear lifts can start after a finite base interval. -/
example {P Q : Nat → ℝ[X]} {s t : Nat → ℝ}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hquot : ∀ n : Nat, N ≤ n → Q n ≠ 0 ∧ (Q n).Splits)
    (hs : ∀ n : Nat, N ≤ n → s n ≠ 0)
    (hrow : ∀ n : Nat, N ≤ n → P n = (C (s n) * X + C (t n)) * Q n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_lift_affine_sequence using
    base := hbase,
    quotient_realrooted := hquot,
    slope_ne := hs,
    cutoff := N,
    factorization := hrow

/-- Automatic affine-slope certificates also work after a cutoff. -/
example {P Q : Nat → ℝ[X]} {t : Nat → ℝ}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hquot : ∀ n : Nat, N ≤ n → Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat,
      N ≤ n → P n = Q n * (C ((n : ℝ) + 1) * X + C (t n))) :
    ∀ n : Nat, (P n).Splits := by
  rr_product_lift_affine_sequence_auto using
    base := hbase,
    quotient_realrooted := hquot,
    cutoff := N,
    factorization := hrow

/-- Constant-first affine lifts have the same cutoff route. -/
example {P Q : Nat → ℝ[X]} {s t : Nat → ℝ}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hquot : ∀ n : Nat, N ≤ n → Q n ≠ 0 ∧ (Q n).Splits)
    (hs : ∀ n : Nat, N ≤ n → s n ≠ 0)
    (hrow : ∀ n : Nat, N ≤ n → P n = Q n * (C (t n) + C (s n) * X)) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_product_lift_const_first_sequence using
    base := hbase,
    quotient_realrooted := hquot,
    slope_ne := hs,
    cutoff := N,
    factorization := hrow

/-- Constant-first automatic slopes are also inferred after a cutoff. -/
example {P Q : Nat → ℝ[X]} {t : Nat → ℝ}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hquot : ∀ n : Nat, N ≤ n → Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat,
      N ≤ n → P n = (C (t n) + C ((n : ℝ) + 1) * X) * Q n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_lift_const_first_sequence_auto using
    base := hbase,
    quotient_realrooted := hquot,
    cutoff := N,
    factorization := hrow

/-- Scalar-power lifts can start after a finite base interval. -/
example {P Q : Nat → ℝ[X]} {c : Nat → ℝ} {m : Nat → Nat}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hquot : ∀ n : Nat, N ≤ n → Q n ≠ 0 ∧ (Q n).Splits)
    (hc : ∀ n : Nat, N ≤ n → c n ≠ 0)
    (hrow : ∀ n : Nat, N ≤ n → P n = (C (c n) : ℝ[X]) ^ (m n) * Q n) :
    ∀ n : Nat, (P n).Splits := by
  rr_product_lift_C_pow_sequence using
    base := hbase,
    quotient_realrooted := hquot,
    scalar_ne := hc,
    cutoff := N,
    factorization := hrow

/-- Automatic scalar-power certificates also work after a cutoff. -/
example {P Q : Nat → ℝ[X]} {m : Nat → Nat}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hquot : ∀ n : Nat, N ≤ n → Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat,
      N ≤ n → P n = Q n * (C ((n : ℝ) + 1) : ℝ[X]) ^ (m n)) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_product_lift_C_pow_sequence_auto using
    base := hbase,
    quotient_realrooted := hquot,
    cutoff := N,
    factorization := hrow

/-- Root-at-zero power lift for rows `P_n = X^{m_n} Q_n`. -/
example {P Q : Nat → ℝ[X]} {m : Nat → Nat}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, P n = X ^ (m n) * Q n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_lift_X_pow_sequence using
    quotient_realrooted := hquot,
    factorization := hrow

/-- The `X^{m_n}` lift also accepts the quotient factor on the left. -/
example {P Q : Nat → ℝ[X]} {m : Nat → Nat}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, P n = Q n * X ^ (m n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_lift_X_pow_sequence using
    quotient_realrooted := hquot,
    factorization := hrow

/-- Root-at-zero power lifts can start after a finite base interval. -/
example {P Q : Nat → ℝ[X]} {m : Nat → Nat}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hquot : ∀ n : Nat, N ≤ n → Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, N ≤ n → P n = X ^ (m n) * Q n) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_product_lift_X_pow_sequence using
    base := hbase,
    quotient_realrooted := hquot,
    cutoff := N,
    factorization := hrow

/-- Projection endpoint for the `X^{m_n}` product lift. -/
example {P Q : Nat → ℝ[X]} {m : Nat → Nat}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, P n = X ^ (m n) * Q n) :
    ∀ n : Nat, (P n).Splits := by
  rr_product_lift_X_pow_sequence using
    quotient_realrooted := hquot,
    factorization := hrow

/-- Nonzero projection endpoint for the right-factor `X^{m_n}` product lift. -/
example {P Q : Nat → ℝ[X]} {m : Nat → Nat}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, P n = Q n * X ^ (m n)) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_product_lift_X_pow_sequence using
    quotient_realrooted := hquot,
    factorization := hrow

/-- Endpoint-factor lift for rows `P_n = (X+1)^{m_n} Q_n`. -/
example {P Q : Nat → ℝ[X]} {m : Nat → Nat}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, P n = (X + C (1 : ℝ)) ^ (m n) * Q n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_lift_X_add_C_pow_sequence using
    quotient_realrooted := hquot,
    factorization := hrow

/-- Row-wise endpoint-factor lift for rows `P_n = (X+t_n)^{m_n} Q_n`. -/
example {P Q : Nat → ℝ[X]} {t : Nat → ℝ} {m : Nat → Nat}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, P n = (X + C (t n)) ^ (m n) * Q n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_lift_X_add_C_row_pow_sequence using
    quotient_realrooted := hquot,
    factorization := hrow

/-- Row-wise endpoint lifts also accept the quotient factor on the left. -/
example {P Q : Nat → ℝ[X]} {t : Nat → ℝ} {m : Nat → Nat}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, P n = Q n * (X + C (t n)) ^ (m n)) :
    ∀ n : Nat, (P n).Splits := by
  rr_product_lift_X_add_C_row_pow_sequence using
    quotient_realrooted := hquot,
    factorization := hrow

/-- Constant-first endpoint powers accept rows `P_n = (t_n+X)^{m_n} Q_n`. -/
example {P Q : Nat → ℝ[X]} {t : Nat → ℝ} {m : Nat → Nat}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, P n = (C (t n) + X) ^ (m n) * Q n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_lift_C_add_X_pow_sequence using
    quotient_realrooted := hquot,
    factorization := hrow

/-- General affine-power lift for rows
`P_n = (s_n X + t_n)^{m_n} Q_n`. -/
example {P Q : Nat → ℝ[X]} {s t : Nat → ℝ} {m : Nat → Nat}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hs : ∀ n : Nat, s n ≠ 0)
    (hrow : ∀ n : Nat, P n = (C (s n) * X + C (t n)) ^ (m n) * Q n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_lift_affine_pow_sequence using
    quotient_realrooted := hquot,
    slope_ne := hs,
    factorization := hrow

/-- The affine-power lift also accepts the quotient factor on the left. -/
example {P Q : Nat → ℝ[X]} {s t : Nat → ℝ} {m : Nat → Nat}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hs : ∀ n : Nat, s n ≠ 0)
    (hrow : ∀ n : Nat, P n = Q n * (C (s n) * X + C (t n)) ^ (m n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_lift_affine_pow_sequence using
    quotient_realrooted := hquot,
    slope_ne := hs,
    factorization := hrow

/-- The same lift accepts constant-first linear factors. -/
example {P Q : Nat → ℝ[X]} {s t : Nat → ℝ} {m : Nat → Nat}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hs : ∀ n : Nat, s n ≠ 0)
    (hrow : ∀ n : Nat, P n = (C (t n) + C (s n) * X) ^ (m n) * Q n) :
    ∀ n : Nat, (P n).Splits := by
  rr_product_lift_const_first_affine_pow_sequence using
    quotient_realrooted := hquot,
    slope_ne := hs,
    factorization := hrow

/-- Nonzero projection endpoint for the right constant-first affine lift. -/
example {P Q : Nat → ℝ[X]} {s t : Nat → ℝ} {m : Nat → Nat}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hs : ∀ n : Nat, s n ≠ 0)
    (hrow : ∀ n : Nat, P n = Q n * (C (t n) + C (s n) * X) ^ (m n)) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_product_lift_const_first_affine_pow_sequence using
    quotient_realrooted := hquot,
    slope_ne := hs,
    factorization := hrow

/-- Automatic slope certificate for positive row-wise affine-power factors. -/
example {P Q : Nat → ℝ[X]} {t : Nat → ℝ} {m : Nat → Nat}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat,
      P n = (C ((n : ℝ) + 1) * X + C (t n)) ^ (m n) * Q n) :
    ∀ n : Nat, (P n).Splits := by
  rr_product_lift_affine_pow_sequence_auto using
    quotient_realrooted := hquot,
    factorization := hrow

/-- Automatic slope certificate for constant-first affine-power factors. -/
example {P Q : Nat → ℝ[X]} {t : Nat → ℝ} {m : Nat → Nat}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat,
      P n = Q n * (C (t n) + C ((n : ℝ) + 1) * X) ^ (m n)) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_product_lift_const_first_affine_pow_sequence_auto using
    quotient_realrooted := hquot,
    factorization := hrow

/-- Fixed endpoint-factor powers can start after a cutoff. -/
example {P Q : Nat → ℝ[X]} {m : Nat → Nat}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hquot : ∀ n : Nat, N ≤ n → Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, N ≤ n → P n = Q n * (X + C (1 : ℝ)) ^ (m n)) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_product_lift_X_add_C_pow_sequence using
    base := hbase,
    quotient_realrooted := hquot,
    cutoff := N,
    factorization := hrow

/-- Row-wise endpoint-factor powers can start after a cutoff. -/
example {P Q : Nat → ℝ[X]} {t : Nat → ℝ} {m : Nat → Nat}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hquot : ∀ n : Nat, N ≤ n → Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, N ≤ n → P n = (X + C (t n)) ^ (m n) * Q n) :
    ∀ n : Nat, (P n).Splits := by
  rr_product_lift_X_add_C_row_pow_sequence using
    base := hbase,
    quotient_realrooted := hquot,
    cutoff := N,
    factorization := hrow

/-- Constant-first endpoint powers can start after a cutoff. -/
example {P Q : Nat → ℝ[X]} {t : Nat → ℝ} {m : Nat → Nat}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hquot : ∀ n : Nat, N ≤ n → Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, N ≤ n → P n = Q n * (C (t n) + X) ^ (m n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_lift_C_add_X_pow_sequence using
    base := hbase,
    quotient_realrooted := hquot,
    cutoff := N,
    factorization := hrow

/-- Affine-power lifts can start after a finite base interval. -/
example {P Q : Nat → ℝ[X]} {s t : Nat → ℝ} {m : Nat → Nat}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hquot : ∀ n : Nat, N ≤ n → Q n ≠ 0 ∧ (Q n).Splits)
    (hs : ∀ n : Nat, N ≤ n → s n ≠ 0)
    (hrow : ∀ n : Nat,
      N ≤ n → P n = (C (s n) * X + C (t n)) ^ (m n) * Q n) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_product_lift_affine_pow_sequence using
    base := hbase,
    quotient_realrooted := hquot,
    slope_ne := hs,
    cutoff := N,
    factorization := hrow

/-- Automatic affine-power slope certificates also work after a cutoff. -/
example {P Q : Nat → ℝ[X]} {t : Nat → ℝ} {m : Nat → Nat}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hquot : ∀ n : Nat, N ≤ n → Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat,
      N ≤ n → P n = Q n * (C ((n : ℝ) + 1) * X + C (t n)) ^ (m n)) :
    ∀ n : Nat, (P n).Splits := by
  rr_product_lift_affine_pow_sequence_auto using
    base := hbase,
    quotient_realrooted := hquot,
    cutoff := N,
    factorization := hrow

/-- Constant-first affine-power lifts can start after a cutoff. -/
example {P Q : Nat → ℝ[X]} {s t : Nat → ℝ} {m : Nat → Nat}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hquot : ∀ n : Nat, N ≤ n → Q n ≠ 0 ∧ (Q n).Splits)
    (hs : ∀ n : Nat, N ≤ n → s n ≠ 0)
    (hrow : ∀ n : Nat,
      N ≤ n → P n = Q n * (C (t n) + C (s n) * X) ^ (m n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_lift_const_first_affine_pow_sequence using
    base := hbase,
    quotient_realrooted := hquot,
    slope_ne := hs,
    cutoff := N,
    factorization := hrow

/-- Automatic constant-first affine powers are inferred after a cutoff. -/
example {P Q : Nat → ℝ[X]} {t : Nat → ℝ} {m : Nat → Nat}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hquot : ∀ n : Nat, N ≤ n → Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat,
      N ≤ n → P n = (C (t n) + C ((n : ℝ) + 1) * X) ^ (m n) * Q n) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_product_lift_const_first_affine_pow_sequence_auto using
    base := hbase,
    quotient_realrooted := hquot,
    cutoff := N,
    factorization := hrow

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
