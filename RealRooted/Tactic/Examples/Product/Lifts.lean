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

/-- The generic lift router keeps a positive scalar factor on the left. -/
example {P Q : Nat → ℝ[X]}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, P n = C ((n : ℝ) + 1) * Q n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_lift_sequence_auto using
    quotient_realrooted := hquot,
    factorization := hrow

/-- The generic lift router keeps a positive scalar-power factor on the left. -/
example {P Q : Nat → ℝ[X]} {m : Nat → Nat}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, P n = (C ((n : ℝ) + 1) : ℝ[X]) ^ (m n) * Q n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_lift_sequence_auto using
    quotient_realrooted := hquot,
    factorization := hrow

/-- The generic lift router keeps a constant-first affine factor on the left. -/
example {P Q : Nat → ℝ[X]} {t : Nat → ℝ}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat,
      P n = (C (t n) + C ((n : ℝ) + 1) * X) * Q n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_lift_sequence_auto using
    quotient_realrooted := hquot,
    factorization := hrow

/-- A checked affine router refuses a scalar factor; the scalar route remains valid. -/
example {P Q : Nat → ℝ[X]}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, P n = C ((n : ℝ) + 1) * Q n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  fail_if_success
    rr_product_lift_checked_affine_sequence_auto using
      quotient_realrooted := hquot,
      factorization := hrow
  rr_product_lift_C_sequence_auto using
    quotient_realrooted := hquot,
    factorization := hrow

/-- error: rr_product checked affine auto: no affine factor found in factorization -/
#guard_msgs in
example {P Q : Nat → ℝ[X]}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, P n = C ((n : ℝ) + 1) * Q n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_lift_checked_affine_sequence_auto using
    quotient_realrooted := hquot,
    factorization := hrow

/-- Supplied evidence proves an arbitrary-factor lift outside the generic router. -/
example {P Q F : Nat → ℝ[X]}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hfactor : ∀ n : Nat, F n ≠ 0 ∧ (F n).Splits)
    (hrow : ∀ n : Nat, P n = F n * Q n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  RealRooted.isRealRooted_of_product_lift_sequence hquot hfactor hrow

/-- The checked affine router directly accepts a constant-first positive slope. -/
example {P Q : Nat → ℝ[X]} {t : Nat → ℝ}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat,
      P n = (C (t n) + C ((n : ℝ) + 1) * X) * Q n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_lift_checked_affine_sequence_auto using
    quotient_realrooted := hquot,
    factorization := hrow


end Tactic
end RealRooted
