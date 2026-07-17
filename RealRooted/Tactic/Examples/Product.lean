import RealRooted.Tactic.Product

/-!
# `rr_product_factor` examples

Regression tests for OEIS recurrences where `P_n` is a real linear factor
times `P_{n-1}`.
-/

open Polynomial

namespace RealRooted
namespace Tactic

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
  rr_product_factor_sequence using
    base := hbase,
    factor_realrooted := hfactor,
    recurrence := hrec

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

/-- Row-wise product lift from a proved quotient sequence. -/
example {P Q F : Nat → ℝ[X]}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hfactor : ∀ n : Nat, F n ≠ 0 ∧ (F n).Splits)
    (hrow : ∀ n : Nat, P n = F n * Q n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_lift_sequence using
    quotient_realrooted := hquot,
    factor_realrooted := hfactor,
    factorization := hrow

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

/-- `A155112`-style persistent root at zero: `P_n = X Q_n`. -/
example {P Q : Nat → ℝ[X]}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, P n = X * Q n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_lift_X_sequence using
    quotient_realrooted := hquot,
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
  have hfactor :
      ∀ n : Nat, ((X : ℝ[X]) ^ 2) ≠ 0 ∧ (((X : ℝ[X]) ^ 2).Splits) := by
    intro n
    simp [pow_two]
  rr_product_factor_sequence using
    base := hbase,
    factor_realrooted := hfactor,
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
  rr_product_factor using hp, (by norm_num : (2 : ℝ) ≠ 0)

/-- `A038220`-style report order `3 + 2t`. -/
example {p : ℝ[X]} (hp : p ≠ 0 ∧ p.Splits) :
    ((C (3 : ℝ) + C (2 : ℝ) * X) * p ≠ 0 ∧
      ((C (3 : ℝ) + C (2 : ℝ) * X) * p).Splits) := by
  rr_product_factor_const_first using hp, (by norm_num : (2 : ℝ) ≠ 0)

/-- `A038226`-style report order `3 + 8t`. -/
example {p : ℝ[X]} (hp : p ≠ 0 ∧ p.Splits) :
    ((C (3 : ℝ) + C (8 : ℝ) * X) * p ≠ 0 ∧
      ((C (3 : ℝ) + C (8 : ℝ) * X) * p).Splits) := by
  rr_product_factor_const_first using hp, (by norm_num : (8 : ℝ) ≠ 0)

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

/-- Product recurrence with powers of the root-at-zero factor. -/
example {P : Nat → ℝ[X]} {m : Nat → Nat}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hrec : ∀ n : Nat, P (n + 1) = X ^ (m n) * P n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_X_pow_sequence using
    base := hbase,
    recurrence := hrec

/-- Powered unit-slope recurrences accept the factor on the right. -/
example {P : Nat → ℝ[X]} {t : Nat → ℝ} {m : Nat → Nat}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hrec : ∀ n : Nat, P (n + 1) = P n * (X + C (t n)) ^ (m n)) :
    ∀ n : Nat, (P n).Splits := by
  rr_product_X_add_C_pow_sequence using
    base := hbase,
    recurrence := hrec

/-- Powered constant-first unit-slope recurrences accept right factors. -/
example {P : Nat → ℝ[X]} {t : Nat → ℝ} {m : Nat → Nat}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hrec : ∀ n : Nat, P (n + 1) = P n * (C (t n) + X) ^ (m n)) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_product_C_add_X_pow_sequence using
    base := hbase,
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

/-- Report-order powered affine recurrences also have an auto-positive form. -/
example {P : Nat → ℝ[X]} {t : Nat → ℝ} {m : Nat → Nat}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hrec : ∀ n : Nat,
      P (n + 1) = P n * (C (t n) + C ((n : ℝ) + 1) * X) ^ (m n)) :
    ∀ n : Nat, (P n).Splits := by
  rr_product_const_first_affine_pow_sequence_auto using
    base := hbase,
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

/-- Degree-plateau product shell with a repeated-zero factor on the growth step. -/
example {P : Nat → ℝ[X]}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hscalar : ∀ n : Nat,
      P (2 * n + 1) = C (2 * (n : ℝ) + 1) * P (2 * n))
    (hstep : ∀ n : Nat, P (2 * n + 2) = ((X : ℝ[X]) ^ 2) * P (2 * n + 1)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  have hfactor :
      ∀ n : Nat, ((X : ℝ[X]) ^ 2) ≠ 0 ∧ (((X : ℝ[X]) ^ 2).Splits) := by
    intro n
    simp [pow_two]
  rr_product_scalar_factor_sequence_auto using
    base := hbase,
    factor_realrooted := hfactor,
    scalar_step := hscalar,
    factor_step := hstep

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
