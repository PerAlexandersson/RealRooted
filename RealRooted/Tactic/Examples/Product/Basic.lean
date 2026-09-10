import RealRooted.Tactic.Product.Rules

/-!
# Basic product tactic regression examples

Smoke tests for product nonzeroness, splitting, factorization, finite-product,
and period-two dispatcher forms.
-/

open Polynomial
open scoped BigOperators

namespace RealRooted
namespace Tactic

example {c : ℝ} (hc : c ≠ 0) : c ≠ 0 := by rr_product_nonzero

example {n : Nat} : (n : ℝ) + 1 ≠ 0 := by rr_product_nonzero

example {n : Nat} : 2 * (n : ℝ) + 1 ≠ 0 := by rr_product_nonzero

example : ∀ n : Nat, 2 ≤ n → (n : ℝ) + 1 ≠ 0 :=
  rr_product_nonzero_seq_from

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

/-- A separate base row can precede an independently factorized tail. -/
example {P Q F : Nat → ℝ[X]}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hfactor : ∀ n : Nat, F n ≠ 0 ∧ (F n).Splits)
    (hrow : ∀ n : Nat, P (n + 1) = F n * Q n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_tail_sequence using hbase, hquot, hfactor, hrow

example {P Q F : Nat → ℝ[X]}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hfactor : ∀ n : Nat, F n ≠ 0 ∧ (F n).Splits)
    (hrow : ∀ n : Nat, P (n + 1) = Q n * F n) :
    ∀ n : Nat, (P n).Splits := by
  rr_product_tail_sequence using
    base := hbase,
    quotient_realrooted := hquot,
    factor_realrooted := hfactor,
    factorization := hrow

/-- Scalar multiples of linear-factor tails reduce to their supplied core family. -/
example {P Q : Nat → ℝ[X]} {c t : Nat → ℝ}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hc : ∀ n : Nat, c n ≠ 0)
    (hbase : P 0 = C (c 0))
    (hrow :
      ∀ n : Nat, P (n + 1) = C (c (n + 1)) * ((X + C (t n)) * Q n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_tail_sequence using
    base := by simpa [hbase] using isRealRooted_C (hc 0),
    quotient_realrooted := fun n => isRealRooted_X_add_C_mul (hquot n),
    factor_realrooted := fun n => isRealRooted_C (hc (n + 1)),
    factorization := hrow

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

/-- The recurrence fixes the family and factor; local certificates are inferred. -/
example {P F Q G : Nat → ℝ[X]}
    (_hdecoyBase : Q 0 ≠ 0 ∧ (Q 0).Splits)
    (_hdecoyFactor : ∀ n : Nat, G n ≠ 0 ∧ (G n).Splits)
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hfactor : ∀ n : Nat, F n ≠ 0 ∧ (F n).Splits)
    (hrec : ∀ n : Nat, P (n + 1) = F n * P n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_factor_sequence using recurrence := hrec

/-- Recurrence inference also detects right-factor orientation and projections. -/
example {P F Q G : Nat → ℝ[X]}
    (_hdecoyBase : Q 0 ≠ 0 ∧ (Q 0).Splits)
    (_hdecoyFactor : ∀ n : Nat, G n ≠ 0 ∧ (G n).Splits)
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hfactor : ∀ n : Nat, F n ≠ 0 ∧ (F n).Splits)
    (hrec : ∀ n : Nat, P (n + 1) = P n * F n) :
    ∀ n : Nat, (P n).Splits := by
  rr_product_factor_sequence using recurrence := hrec

/-- Lag-two product recurrences advance the even and odd subsequences together. -/
example {P F : Nat → ℝ[X]}
    (hbase_zero : P 0 ≠ 0 ∧ (P 0).Splits)
    (hbase_one : P 1 ≠ 0 ∧ (P 1).Splits)
    (hfactor : ∀ n : Nat, F n ≠ 0 ∧ (F n).Splits)
    (hrec : ∀ n : Nat, P (n + 2) = F n * P n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_lag_product_factor_sequence using hbase_zero, hbase_one, hfactor, hrec

/-- Splitting projection endpoint for lag-two product recurrences. -/
example {P F : Nat → ℝ[X]}
    (hbase_zero : P 0 ≠ 0 ∧ (P 0).Splits)
    (hbase_one : P 1 ≠ 0 ∧ (P 1).Splits)
    (hfactor : ∀ n : Nat, F n ≠ 0 ∧ (F n).Splits)
    (hrec : ∀ n : Nat, P (n + 2) = F n * P n) :
    ∀ n : Nat, (P n).Splits := by
  rr_lag_product_factor_sequence using
    base_zero := hbase_zero,
    base_one := hbase_one,
    factor_realrooted := hfactor,
    recurrence := hrec

/-- Lag-two recurrence inference fixes both families and finds all certificates. -/
example {P F Q G : Nat → ℝ[X]}
    (_hdecoyZero : Q 0 ≠ 0 ∧ (Q 0).Splits)
    (_hdecoyOne : P 2 ≠ 0 ∧ (P 2).Splits)
    (_hdecoyFactor : ∀ n : Nat, G n ≠ 0 ∧ (G n).Splits)
    (hbase_zero : P 0 ≠ 0 ∧ (P 0).Splits)
    (hbase_one : P 1 ≠ 0 ∧ (P 1).Splits)
    (hfactor : ∀ n : Nat, F n ≠ 0 ∧ (F n).Splits)
    (hrec : ∀ n : Nat, P (n + 2) = F n * P n) :
    ∀ n : Nat, P n = 0 ∨ (P n).Splits := by
  rr_lag_product_factor_sequence using recurrence := hrec

/-- Lag-two inference also detects right factors and indexed projections. -/
example {P F Q G : Nat → ℝ[X]}
    (_hdecoyZero : Q 0 ≠ 0 ∧ (Q 0).Splits)
    (_hdecoyFactor : ∀ n : Nat, G n ≠ 0 ∧ (G n).Splits)
    (hbase_zero : P 0 ≠ 0 ∧ (P 0).Splits)
    (hbase_one : P 1 ≠ 0 ∧ (P 1).Splits)
    (hfactor : ∀ n : Nat, F n ≠ 0 ∧ (F n).Splits)
    (hrec : ∀ n : Nat, P (n + 2) = P n * F n) :
    (P 4).Splits := by
  rr_lag_product_factor_sequence using recurrence := hrec

/-- Lag-two product recurrences also accept the supplied factor on the right. -/
example {P F : Nat → ℝ[X]}
    (hbase_zero : P 0 ≠ 0 ∧ (P 0).Splits)
    (hbase_one : P 1 ≠ 0 ∧ (P 1).Splits)
    (hfactor : ∀ n : Nat, F n ≠ 0 ∧ (F n).Splits)
    (hrec : ∀ n : Nat, P (n + 2) = P n * F n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_lag_product_factor_sequence using
    base_zero := hbase_zero,
    base_one := hbase_one,
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

/-- Tail recurrence inference keeps the cutoff explicit and finds interval certificates. -/
example {P F Q G : Nat → ℝ[X]}
    (N : Nat)
    (_hdecoyBase : ∀ n : Nat, n ≤ N → Q n ≠ 0 ∧ (Q n).Splits)
    (_hdecoyFactor : ∀ n : Nat, N ≤ n → G n ≠ 0 ∧ (G n).Splits)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hfactor : ∀ n : Nat, N ≤ n → F n ≠ 0 ∧ (F n).Splits)
    (hrec : ∀ n : Nat, N ≤ n → P (n + 1) = F n * P n) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_product_factor_sequence using cutoff := N, recurrence := hrec

/-- Explicit tail cutoffs also accept right factors and indexed projections. -/
example {P F : Nat → ℝ[X]}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hfactor : ∀ n : Nat, N ≤ n → F n ≠ 0 ∧ (F n).Splits)
    (hrec : ∀ n : Nat, N ≤ n → P (n + 1) = P n * F n) :
    (P 3).Splits := by
  rr_product_factor_sequence using cutoff := N, recurrence := hrec

/-- The recurrence can determine a tail cutoff before certificate lookup. -/
example {P F Q G : Nat → ℝ[X]}
    (N : Nat)
    (_hwrongCutoff : ∀ n : Nat, n ≤ N + 1 → P n ≠ 0 ∧ (P n).Splits)
    (_hdecoyBase : ∀ n : Nat, n ≤ N → Q n ≠ 0 ∧ (Q n).Splits)
    (_hdecoyFactor : ∀ n : Nat, N ≤ n → G n ≠ 0 ∧ (G n).Splits)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hfactor : ∀ n : Nat, N ≤ n → F n ≠ 0 ∧ (F n).Splits)
    (hrec : ∀ n : Nat, N ≤ n → P (n + 1) = F n * P n) :
    ∀ n : Nat, P n = 0 ∨ (P n).Splits := by
  rr_product_factor_sequence using recurrence := hrec

/-- Inferred tail cutoffs also accept right factors and indexed projections. -/
example {P F Q G : Nat → ℝ[X]}
    (N : Nat)
    (_hdecoyBase : ∀ n : Nat, n ≤ N → Q n ≠ 0 ∧ (Q n).Splits)
    (_hdecoyFactor : ∀ n : Nat, N ≤ n → G n ≠ 0 ∧ (G n).Splits)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hfactor : ∀ n : Nat, N ≤ n → F n ≠ 0 ∧ (F n).Splits)
    (hrec : ∀ n : Nat, N ≤ n → P (n + 1) = P n * F n) :
    (P 3).Splits := by
  rr_product_factor_sequence using recurrence := hrec

/-- Direct finite-product formula route. -/
example {P : Nat → ℝ[X]} {root : Nat → Nat → ℝ}
    (hroot : ∀ n : Nat,
      P n = ∏ j ∈ Finset.range n, (X - C (root n j))) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_affine_product_sequence using formula := hroot

/-- Scalar finite-product formula route. -/
example {P : Nat → ℝ[X]} {c : Nat → ℝ} {rootCount : Nat → Nat}
    {roots : Nat → Nat → ℝ}
    (hc : ∀ n : Nat, c n ≠ 0)
    (hroot : ∀ n : Nat,
      P n = C (c n) *
        ∏ j ∈ Finset.range (rootCount n), (X - C (roots n j))) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_finite_linear_product_scalar_sequence using
    scalar_ne := hc,
    factorization := hroot

/-- The scalar finite-product route supports projected endpoints. -/
example {P : Nat → ℝ[X]} {c : Nat → ℝ} {rootCount : Nat → Nat}
    {roots : Nat → Nat → ℝ}
    (hc : ∀ n : Nat, c n ≠ 0)
    (hroot : ∀ n : Nat,
      P n = C (c n) *
        ∏ j ∈ Finset.range (rootCount n), (X - C (roots n j))) :
    ∀ n : Nat, (P n).Splits := by
  rr_finite_linear_product_scalar_sequence using
    scalar_ne := hc,
    factorization := hroot

/-- The older J1 spelling remains available for compatibility. -/
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


end Tactic
end RealRooted
