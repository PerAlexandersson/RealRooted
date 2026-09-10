import RealRooted.Tactic.Product.Rules

/-!
# Product-lift tactic regression examples

Smoke tests for supplied and automatic product-lift certificates, including
scalar, powered, affine, and cutoff factorization variants.
-/

open Polynomial
open scoped BigOperators

namespace RealRooted
namespace Tactic

/-- Row-wise product lift from a proved quotient sequence. -/
example {P Q F : Nat → ℝ[X]}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hfactor : ∀ n : Nat, F n ≠ 0 ∧ (F n).Splits)
    (hrow : ∀ n : Nat, P n = F n * Q n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_lift_sequence using hquot, hfactor, hrow

example {P Q : Nat → ℝ[X]}
    (hmodel : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hidentify : ∀ n : Nat, P n = Q n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_model_sequence using
    model_realrooted := hmodel,
    identification := hidentify

example {P Q : Nat → ℝ[X]}
    (hmodel : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hidentify : ∀ n : Nat, P n = Q n) :
    ∀ n : Nat, (P n).Splits := by
  rr_model_sequence using
    model_realrooted := hmodel,
    identification := hidentify

example {P Q : Nat → ℝ[X]} {c : Nat → ℝ} {m : Nat → Nat}
    (hmodel : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hc : ∀ n : Nat, c n ≠ 0)
    (hrow : ∀ n : Nat, P n = C (c n) * (X ^ (m n) * Q n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_scalar_monomial_lift_sequence using
    model_realrooted := hmodel,
    scalar_ne := hc,
    factorization := hrow

example {P Q : Nat → ℝ[X]} {c : Nat → ℝ} {m : Nat → Nat}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hmodel : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hc : ∀ n : Nat, c n ≠ 0)
    (hrow : ∀ n : Nat, P (n + 1) = C (c n) * (X ^ (m n) * Q n)) :
    ∀ n : Nat, (P n).Splits := by
  rr_scalar_monomial_tail_sequence using
    base := hbase,
    model_realrooted := hmodel,
    scalar_ne := hc,
    factorization := hrow

example {P Qeven Qodd : Nat → ℝ[X]}
    {ceven codd : Nat → ℝ} {meven modd : Nat → Nat}
    (heven_model : ∀ n : Nat, Qeven n ≠ 0 ∧ (Qeven n).Splits)
    (hodd_model : ∀ n : Nat, Qodd n ≠ 0 ∧ (Qodd n).Splits)
    (hceven : ∀ n : Nat, ceven n ≠ 0)
    (hcodd : ∀ n : Nat, codd n ≠ 0)
    (heven : ∀ n : Nat,
      P (2 * n) = C (ceven n) * (X ^ (meven n) * Qeven n))
    (hodd : ∀ n : Nat,
      P (2 * n + 1) = C (codd n) * (X ^ (modd n) * Qodd n)) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_even_odd_scalar_monomial_lift_sequence using
    even_model_realrooted := heven_model,
    odd_model_realrooted := hodd_model,
    even_scalar_ne := hceven,
    odd_scalar_ne := hcodd,
    even_factorization := heven,
    odd_factorization := hodd

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

/-- The product-lift auto router recognizes positive scalar factors. -/
example {P Q : Nat → ℝ[X]}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, P n = Q n * C ((n : ℝ) + 1)) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_product_lift_sequence_auto using
    quotient_realrooted := hquot,
    factorization := hrow

/-- The product-lift auto router reaches positive scalar-power factors. -/
example {P Q : Nat → ℝ[X]} {m : Nat → Nat}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat,
      P n = Q n * (C ((n : ℝ) + 1) : ℝ[X]) ^ (m n)) :
    ∀ n : Nat, (P n).Splits := by
  rr_product_lift_sequence_auto using
    quotient_realrooted := hquot,
    factorization := hrow

/-- The product-lift auto router reaches positive affine-power factors. -/
example {P Q : Nat → ℝ[X]} {t : Nat → ℝ} {m : Nat → Nat}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat,
      P n = Q n * (C ((n : ℝ) + 1) * X + C (t n)) ^ (m n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_lift_sequence_auto using
    quotient_realrooted := hquot,
    factorization := hrow

/-- The product-lift auto router also supports cutoff lifts. -/
example {P Q : Nat → ℝ[X]}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hquot : ∀ n : Nat, N ≤ n → Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, N ≤ n → P n = Q n * X) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_lift_sequence_auto using
    base := hbase,
    quotient_realrooted := hquot,
    cutoff := N,
    factorization := hrow

/-- The cutoff auto router reaches constant-first positive affine powers. -/
example {P Q : Nat → ℝ[X]} {t : Nat → ℝ} {m : Nat → Nat}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hquot : ∀ n : Nat, N ≤ n → Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat,
      N ≤ n → P n = (C (t n) + C (2 : ℝ) * X) ^ (m n) * Q n) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_product_lift_sequence_auto using
    base := hbase,
    quotient_realrooted := hquot,
    cutoff := N,
    factorization := hrow


end Tactic
end RealRooted
