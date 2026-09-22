import RealRooted.Tactic.Product.Rules

/-!
# Product lift-auto shape dispatch examples

Regression examples for bounded product-lift auto dispatch.
-/

open Polynomial

namespace RealRooted
namespace Tactic

/-- Ordinary left scalar factors remain on the scalar route. -/
example {P Q : Nat → ℝ[X]}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, P n = C ((n : ℝ) + 1) * Q n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_lift_sequence_auto using
    quotient_realrooted := hquot,
    factorization := hrow

/-- Cutoff right scalar factors remain on the scalar route. -/
example {P Q : Nat → ℝ[X]} {N : Nat}
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hquot : ∀ n : Nat, N ≤ n → Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, N ≤ n → P n = Q n * C ((n : ℝ) + 1)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_lift_sequence_auto using
    base := hbase,
    quotient_realrooted := hquot,
    cutoff := N,
    factorization := hrow

/-- Ordinary right scalar-power factors remain on the scalar-power route. -/
example {P Q : Nat → ℝ[X]} {m : Nat → Nat}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, P n = Q n * (C ((n : ℝ) + 1) : ℝ[X]) ^ (m n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_lift_sequence_auto using
    quotient_realrooted := hquot,
    factorization := hrow

/-- Cutoff left scalar-power factors remain on the scalar-power route. -/
example {P Q : Nat → ℝ[X]} {m : Nat → Nat} {N : Nat}
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hquot : ∀ n : Nat, N ≤ n → Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat,
      N ≤ n → P n = (C ((n : ℝ) + 1) : ℝ[X]) ^ (m n) * Q n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_lift_sequence_auto using
    base := hbase,
    quotient_realrooted := hquot,
    cutoff := N,
    factorization := hrow

/-- Ordinary left affine factors retain checked affine dispatch. -/
example {P Q : Nat → ℝ[X]} {t : Nat → ℝ}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat,
      P n = (C ((n : ℝ) + 1) * X + C (t n)) * Q n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_lift_sequence_auto using
    quotient_realrooted := hquot,
    factorization := hrow

/-- Cutoff right constant-first affine factors retain checked affine dispatch. -/
example {P Q : Nat → ℝ[X]} {t : Nat → ℝ} {N : Nat}
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hquot : ∀ n : Nat, N ≤ n → Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat,
      N ≤ n → P n = Q n * (C (t n) + C ((n : ℝ) + 1) * X)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_lift_sequence_auto using
    base := hbase,
    quotient_realrooted := hquot,
    cutoff := N,
    factorization := hrow

/-- Ordinary right root-zero factors retain the `X` route. -/
example {P Q : Nat → ℝ[X]}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, P n = Q n * X) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_lift_sequence_auto using
    quotient_realrooted := hquot,
    factorization := hrow

/-- Cutoff left root-zero factors retain the `X` route. -/
example {P Q : Nat → ℝ[X]} {N : Nat}
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hquot : ∀ n : Nat, N ≤ n → Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, N ≤ n → P n = X * Q n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_lift_sequence_auto using
    base := hbase,
    quotient_realrooted := hquot,
    cutoff := N,
    factorization := hrow

/-- Structured quotients are compared as complete pointwise operands. -/
example {P Q0 Q1 : Nat → ℝ[X]} {t : Nat → ℝ}
    (hquot : ∀ n : Nat, Q0 n + Q1 n ≠ 0 ∧ (Q0 n + Q1 n).Splits)
    (hrow : ∀ n : Nat,
      P n = (C (t n) + C ((n : ℝ) + 1) * X) * (Q0 n + Q1 n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_lift_sequence_auto using
    quotient_realrooted := hquot,
    factorization := hrow

/-- An ordinary structured quotient containing `X` leaves an affine factor right. -/
example {P Q : Nat → ℝ[X]} {t : Nat → ℝ}
    (hquot : ∀ n : Nat, Q n + X ≠ 0 ∧ (Q n + X).Splits)
    (hrow : ∀ n : Nat,
      P n = (Q n + X) * (C (t n) + C ((n : ℝ) + 1) * X)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_lift_sequence_auto using
    quotient_realrooted := hquot,
    factorization := hrow

/-- The cutoff route preserves the same structured-quotient right-factor side. -/
example {P Q : Nat → ℝ[X]} {t : Nat → ℝ} {N : Nat}
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hquot : ∀ n : Nat, N ≤ n → Q n + X ≠ 0 ∧ (Q n + X).Splits)
    (hrow : ∀ n : Nat,
      N ≤ n → P n = (Q n + X) * (C (t n) + C ((n : ℝ) + 1) * X)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_lift_sequence_auto using
    base := hbase,
    quotient_realrooted := hquot,
    cutoff := N,
    factorization := hrow

/-- Ordinary right root-zero powers retain the `X`-power route. -/
example {P Q : Nat → ℝ[X]} {m : Nat → Nat}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, P n = Q n * X ^ (m n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_lift_sequence_auto using
    quotient_realrooted := hquot,
    factorization := hrow

/-- A fixed exponent remains a supported `X + C` row-power instance. -/
example {P Q : Nat → ℝ[X]}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, P n = (X + C (1 : ℝ)) ^ 3 * Q n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_lift_sequence_auto using
    quotient_realrooted := hquot,
    factorization := hrow

/-- Ordinary left row-dependent `X + C` powers retain their route. -/
example {P Q : Nat → ℝ[X]} {m : Nat → Nat} {t : Nat → ℝ}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, P n = (X + C (t n)) ^ (m n) * Q n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_lift_sequence_auto using
    quotient_realrooted := hquot,
    factorization := hrow

/-- Cutoff right `C + X` powers retain their route. -/
example {P Q : Nat → ℝ[X]} {m : Nat → Nat} {t : Nat → ℝ} {N : Nat}
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hquot : ∀ n : Nat, N ≤ n → Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, N ≤ n → P n = Q n * (C (t n) + X) ^ (m n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_lift_sequence_auto using
    base := hbase,
    quotient_realrooted := hquot,
    cutoff := N,
    factorization := hrow

/-- Cutoff left affine powers use the factor orientation, not quotient syntax. -/
example {P Q : Nat → ℝ[X]} {m : Nat → Nat} {t : Nat → ℝ} {N : Nat}
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hquot : ∀ n : Nat, N ≤ n → Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat,
      N ≤ n → P n = (C ((n : ℝ) + 1) * X + C (t n)) ^ (m n) * Q n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_lift_sequence_auto using
    base := hbase,
    quotient_realrooted := hquot,
    cutoff := N,
    factorization := hrow

/-- error: rr_product lift auto: factorization does not expose quotient as an outer factor -/
#guard_msgs in
example {P Q : Nat → ℝ[X]}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, P n = C ((n : ℝ) + 1) * Q (n + 1)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_lift_sequence_auto using
    quotient_realrooted := hquot,
    factorization := hrow

/-- error: rr_product lift auto: unsupported factor; use explicit factor_realrooted -/
#guard_msgs in
example {P Q F : Nat → ℝ[X]}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, P n = F n * Q n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_lift_sequence_auto using
    quotient_realrooted := hquot,
    factorization := hrow

/-- Explicit factor evidence still proves the opaque-factor lift. -/
example {P Q F : Nat → ℝ[X]}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hfactor : ∀ n : Nat, F n ≠ 0 ∧ (F n).Splits)
    (hrow : ∀ n : Nat, P n = F n * Q n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_lift_sequence using
    quotient_realrooted := hquot,
    factor_realrooted := hfactor,
    factorization := hrow

/-- error: rr_product lift auto: unsupported factor; use explicit factor_realrooted -/
#guard_msgs in
example {P Q : Nat → ℝ[X]}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, P n = (X * (1 + X)) * Q n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_lift_sequence_auto using
    quotient_realrooted := hquot,
    factorization := hrow

end Tactic
end RealRooted
