import RealRooted.Tactic.OEIS.ProductExit
import RealRooted.Tactic.OEIS.ProductFactor

/-!
# OEIS product-router regression examples

Product exit and factor certificate router tests, including sequence,
normalization, and real-rootedness projection variants.
-/

open Polynomial
open scoped BigOperators

namespace RealRooted
namespace Tactic

/-- Product-exit router, identity branch. -/
example {P : Nat → ℝ[X]}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hrec : ∀ n : Nat, P (n + 1) = P n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_exit_sequence using
    base := hbase,
    recurrence := hrec,
    certificate := identity

/-- Product-exit router, root-zero branch with a projection endpoint. -/
example {P : Nat → ℝ[X]}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hrec : ∀ n : Nat, P (n + 1) = P n * X) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_product_exit_sequence using
    base := hbase,
    recurrence := hrec,
    certificate := rootZero

/-- Product-exit router, automatic one-step branch for constant rows. -/
example {P : Nat → ℝ[X]}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hrec : ∀ n : Nat, P (n + 1) = P n) :
    ∀ n : Nat, (P n).Splits := by
  rr_product_exit_sequence using
    base := hbase,
    recurrence := hrec,
    certificate := auto

/-- Product-exit router, automatic one-step branch for a zero-root factor. -/
example {P : Nat → ℝ[X]}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hrec : ∀ n : Nat, P (n + 1) = X * P n) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_product_exit_sequence using
    base := hbase,
    recurrence := hrec,
    certificate := auto

/-- Product-exit router, cutoff identity branch. -/
example {P : Nat → ℝ[X]}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hrec : ∀ n : Nat, N ≤ n → P (n + 1) = P n) :
    ∀ n : Nat, (P n).Splits := by
  rr_product_exit_sequence using
    base := hbase,
    cutoff := N,
    recurrence := hrec,
    certificate := identity

/-- Product-exit router, cutoff automatic zero-root branch. -/
example {P : Nat → ℝ[X]}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hrec : ∀ n : Nat, N ≤ n → P (n + 1) = P n * X) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_product_exit_sequence using
    base := hbase,
    cutoff := N,
    recurrence := hrec,
    certificate := auto

/-- Product-exit router, period-two branch. -/
example {P : Nat → ℝ[X]}
    (hbase_zero : P 0 ≠ 0 ∧ (P 0).Splits)
    (hbase_one : P 1 ≠ 0 ∧ (P 1).Splits)
    (hrec : ∀ n : Nat, P (n + 2) = P n) :
    ∀ n : Nat, (P n).Splits := by
  rr_product_exit_sequence using
    base_zero := hbase_zero,
    base_one := hbase_one,
    recurrence := hrec,
    certificate := periodTwo

/-- Product-exit router, period-two branch from a cutoff row. -/
example {P : Nat → ℝ[X]}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N + 1 → P n ≠ 0 ∧ (P n).Splits)
    (hrec : ∀ n : Nat, N ≤ n → P (n + 2) = P n) :
    ∀ n : Nat, (P n).Splits := by
  rr_product_exit_sequence using
    base := hbase,
    cutoff := N,
    recurrence := hrec,
    certificate := periodTwo

/-- Product-factor recurrence router with a supplied factor certificate. -/
example {P F : Nat → ℝ[X]}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hfactor : ∀ n : Nat, F n ≠ 0 ∧ (F n).Splits)
    (hrec : ∀ n : Nat, P (n + 1) = P n * F n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_factor_sequence using
    base := hbase,
    factor_realrooted := hfactor,
    recurrence := hrec,
    certificate := suppliedFactor

/-- Product-factor router with a supplied factor certificate from a cutoff row. -/
example {P F : Nat → ℝ[X]}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hfactor : ∀ n : Nat, N ≤ n → F n ≠ 0 ∧ (F n).Splits)
    (hrec : ∀ n : Nat, N ≤ n → P (n + 1) = P n * F n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_factor_sequence using
    base := hbase,
    factor_realrooted := hfactor,
    cutoff := N,
    recurrence := hrec,
    certificate := suppliedFactor

/-- Product-factor recurrence router, automatic affine-slope certificate. -/
example {P : Nat → ℝ[X]} {t : Nat → ℝ}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hrec : ∀ n : Nat,
      P (n + 1) = (C ((n : ℝ) + 1) * X + C (t n)) * P n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_factor_sequence using
    base := hbase,
    recurrence := hrec,
    certificate := affineAuto

/-- Product-factor recurrence router, constant-first affine factor. -/
example {P : Nat → ℝ[X]} {s t : Nat → ℝ}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hs : ∀ n : Nat, s n ≠ 0)
    (hrec : ∀ n : Nat, P (n + 1) = P n * (C (t n) + C (s n) * X)) :
    ∀ n : Nat, (P n).Splits := by
  rr_product_factor_sequence using
    base := hbase,
    slope_ne := hs,
    recurrence := hrec,
    certificate := constFirstAffine

/-- Product-factor router, affine factor from a cutoff row. -/
example {P : Nat → ℝ[X]} {s t : Nat → ℝ}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hs : ∀ n : Nat, s n ≠ 0)
    (hrec : ∀ n : Nat,
      N ≤ n → P (n + 1) = (C (s n) * X + C (t n)) * P n) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_product_factor_sequence using
    base := hbase,
    slope_ne := hs,
    cutoff := N,
    recurrence := hrec,
    certificate := affine

/-- Product-factor router, automatic affine factor from a cutoff row. -/
example {P : Nat → ℝ[X]} {t : Nat → ℝ}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hrec : ∀ n : Nat,
      N ≤ n → P (n + 1) = P n * (C ((n : ℝ) + 1) * X + C (t n))) :
    ∀ n : Nat, (P n).Splits := by
  rr_product_factor_sequence using
    base := hbase,
    cutoff := N,
    recurrence := hrec,
    certificate := affineAuto

/-- Product-factor router, constant-first affine factor from a cutoff row. -/
example {P : Nat → ℝ[X]} {s t : Nat → ℝ}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hs : ∀ n : Nat, s n ≠ 0)
    (hrec : ∀ n : Nat,
      N ≤ n → P (n + 1) = P n * (C (t n) + C (s n) * X)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_factor_sequence using
    base := hbase,
    slope_ne := hs,
    cutoff := N,
    recurrence := hrec,
    certificate := constFirstAffine

/-- Product-factor router, automatic constant-first affine cutoff branch. -/
example {P : Nat → ℝ[X]} {t : Nat → ℝ}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hrec : ∀ n : Nat,
      N ≤ n → P (n + 1) = (C (t n) + C ((n : ℝ) + 1) * X) * P n) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_product_factor_sequence using
    base := hbase,
    cutoff := N,
    recurrence := hrec,
    certificate := constFirstAffineAuto

/-- Product-factor recurrence router, unit-linear factor. -/
example {P : Nat → ℝ[X]} {t : Nat → ℝ}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hrec : ∀ n : Nat, P (n + 1) = P n * (X + C (t n))) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_product_factor_sequence using
    base := hbase,
    recurrence := hrec,
    certificate := xAddC

/-- Product-factor router, unit-linear factor from a cutoff row. -/
example {P : Nat → ℝ[X]} {t : Nat → ℝ}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hrec : ∀ n : Nat, N ≤ n → P (n + 1) = P n * (X + C (t n))) :
    ∀ n : Nat, (P n).Splits := by
  rr_product_factor_sequence using
    base := hbase,
    cutoff := N,
    recurrence := hrec,
    certificate := xAddC

/-- Product-factor router, constant-first unit-linear factor from a cutoff row. -/
example {P : Nat → ℝ[X]} {t : Nat → ℝ}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hrec : ∀ n : Nat, N ≤ n → P (n + 1) = (C (t n) + X) * P n) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_product_factor_sequence using
    base := hbase,
    cutoff := N,
    recurrence := hrec,
    certificate := cAddX

/-- Product-factor recurrence router, automatic unit-linear factor. -/
example {P : Nat → ℝ[X]} {t : Nat → ℝ}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hrec : ∀ n : Nat, P (n + 1) = (X + C (t n)) * P n) :
    ∀ n : Nat, (P n).Splits := by
  rr_product_factor_sequence using
    base := hbase,
    recurrence := hrec,
    certificate := auto

/-- Product-factor router, automatic unit-linear factor from a cutoff row. -/
example {P : Nat → ℝ[X]} {t : Nat → ℝ}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hrec : ∀ n : Nat, N ≤ n → P (n + 1) = P n * (X + C (t n))) :
    ∀ n : Nat, (P n).Splits := by
  rr_product_factor_sequence using
    base := hbase,
    cutoff := N,
    recurrence := hrec,
    certificate := auto

/-- Product-factor auto router reaches positive affine factors. -/
example {P : Nat → ℝ[X]} {t : Nat → ℝ}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hrec : ∀ n : Nat,
      P (n + 1) = (C ((n : ℝ) + 1) * X + C (t n)) * P n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_factor_sequence using
    base := hbase,
    recurrence := hrec,
    certificate := auto

/-- Product-factor auto router reaches constant-first affine factors. -/
example {P : Nat → ℝ[X]} {t : Nat → ℝ}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hrec : ∀ n : Nat,
      P (n + 1) = P n * (C (t n) + C ((n : ℝ) + 1) * X)) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_product_factor_sequence using
    base := hbase,
    recurrence := hrec,
    certificate := auto

/-- Product-factor cutoff auto reaches constant-first affine factors. -/
example {P : Nat → ℝ[X]} {t : Nat → ℝ}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hrec : ∀ n : Nat,
      N ≤ n → P (n + 1) = P n * (C (t n) + C (2 : ℝ) * X)) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_product_factor_sequence using
    base := hbase,
    cutoff := N,
    recurrence := hrec,
    certificate := auto

/-- Product-factor recurrence router, repeated root-zero factor. -/
example {P : Nat → ℝ[X]} {m : Nat → Nat}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hrec : ∀ n : Nat, P (n + 1) = X ^ (m n) * P n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_factor_sequence using
    base := hbase,
    recurrence := hrec,
    certificate := rootZeroPow

/-- Product-factor router, repeated root-zero factor from a cutoff row. -/
example {P : Nat → ℝ[X]} {m : Nat → Nat}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hrec : ∀ n : Nat, N ≤ n → P (n + 1) = P n * X ^ (m n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_factor_sequence using
    base := hbase,
    cutoff := N,
    recurrence := hrec,
    certificate := rootZeroPow

/-- Product-factor router, powered unit-linear factor from a cutoff row. -/
example {P : Nat → ℝ[X]} {t : Nat → ℝ} {m : Nat → Nat}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hrec : ∀ n : Nat,
      N ≤ n → P (n + 1) = (X + C (t n)) ^ (m n) * P n) :
    ∀ n : Nat, (P n).Splits := by
  rr_product_factor_sequence using
    base := hbase,
    cutoff := N,
    recurrence := hrec,
    certificate := xAddCPow

/-- Product-factor router, powered constant-first factor from a cutoff row. -/
example {P : Nat → ℝ[X]} {t : Nat → ℝ} {m : Nat → Nat}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hrec : ∀ n : Nat,
      N ≤ n → P (n + 1) = P n * (C (t n) + X) ^ (m n)) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_product_factor_sequence using
    base := hbase,
    cutoff := N,
    recurrence := hrec,
    certificate := cAddXPow

/-- Product-factor recurrence router, automatic repeated root-zero factor. -/
example {P : Nat → ℝ[X]} {m : Nat → Nat}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hrec : ∀ n : Nat, P (n + 1) = P n * X ^ (m n)) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_product_factor_sequence using
    base := hbase,
    recurrence := hrec,
    certificate := auto

/-- Product-factor router, automatic root-zero-power factor from a cutoff row. -/
example {P : Nat → ℝ[X]} {m : Nat → Nat}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hrec : ∀ n : Nat, N ≤ n → P (n + 1) = P n * X ^ (m n)) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_product_factor_sequence using
    base := hbase,
    cutoff := N,
    recurrence := hrec,
    certificate := auto

/-- Product-factor auto router reaches powered positive affine factors. -/
example {P : Nat → ℝ[X]} {t : Nat → ℝ} {m : Nat → Nat}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hrec : ∀ n : Nat,
      P (n + 1) = (C ((n : ℝ) + 1) * X + C (t n)) ^ (m n) * P n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_factor_sequence using
    base := hbase,
    recurrence := hrec,
    certificate := auto

/-- Product-factor cutoff auto reaches constant-first powered affine factors. -/
example {P : Nat → ℝ[X]} {t : Nat → ℝ} {m : Nat → Nat}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hrec : ∀ n : Nat,
      N ≤ n → P (n + 1) = P n * (C (t n) + C (2 : ℝ) * X) ^ (m n)) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_product_factor_sequence using
    base := hbase,
    cutoff := N,
    recurrence := hrec,
    certificate := auto

/-- Product-factor auto router reaches positive scalar factors. -/
example {P : Nat → ℝ[X]}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hrec : ∀ n : Nat, P (n + 1) = C ((n : ℝ) + 1) * P n) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_product_factor_sequence using
    base := hbase,
    recurrence := hrec,
    certificate := auto

/-- Product-factor cutoff auto reaches positive scalar-power factors. -/
example {P : Nat → ℝ[X]} {m : Nat → Nat}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hrec : ∀ n : Nat,
      N ≤ n → P (n + 1) = P n * (C ((n : ℝ) + 1) : ℝ[X]) ^ (m n)) :
    ∀ n : Nat, (P n).Splits := by
  rr_product_factor_sequence using
    base := hbase,
    cutoff := N,
    recurrence := hrec,
    certificate := auto

/-- Product-factor recurrence router, automatic scalar certificate. -/
example {P : Nat → ℝ[X]}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hrec : ∀ n : Nat, P (n + 1) = C ((n : ℝ) + 1) * P n) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_product_factor_sequence using
    base := hbase,
    recurrence := hrec,
    certificate := scalarAuto

/-- Product-factor router, scalar factor from a cutoff row. -/
example {P : Nat → ℝ[X]} {a : Nat → ℝ}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (ha : ∀ n : Nat, a n ≠ 0)
    (hrec : ∀ n : Nat, N ≤ n → P (n + 1) = P n * C (a n)) :
    ∀ n : Nat, (P n).Splits := by
  rr_product_factor_sequence using
    base := hbase,
    scalar_ne := ha,
    cutoff := N,
    recurrence := hrec,
    certificate := scalar

/-- Product-factor router, automatic scalar factor from a cutoff row. -/
example {P : Nat → ℝ[X]}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hrec : ∀ n : Nat, N ≤ n → P (n + 1) = C ((n : ℝ) + 1) * P n) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_product_factor_sequence using
    base := hbase,
    cutoff := N,
    recurrence := hrec,
    certificate := scalarAuto

/-- Product-factor recurrence router, scalar-power factor. -/
example {P : Nat → ℝ[X]} {a : Nat → ℝ} {m : Nat → Nat}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (ha : ∀ n : Nat, a n ≠ 0)
    (hrec : ∀ n : Nat, P (n + 1) = P n * (C (a n) : ℝ[X]) ^ (m n)) :
    ∀ n : Nat, (P n).Splits := by
  rr_product_factor_sequence using
    base := hbase,
    scalar_ne := ha,
    recurrence := hrec,
    certificate := scalarPow

/-- Product-factor router, scalar-power factor from a cutoff row. -/
example {P : Nat → ℝ[X]} {a : Nat → ℝ} {m : Nat → Nat}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (ha : ∀ n : Nat, a n ≠ 0)
    (hrec : ∀ n : Nat,
      N ≤ n → P (n + 1) = (C (a n) : ℝ[X]) ^ (m n) * P n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_factor_sequence using
    base := hbase,
    scalar_ne := ha,
    cutoff := N,
    recurrence := hrec,
    certificate := scalarPow

/-- Product-factor router, automatic scalar-power factor from a cutoff row. -/
example {P : Nat → ℝ[X]} {m : Nat → Nat}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hrec : ∀ n : Nat,
      N ≤ n → P (n + 1) = P n * (C ((n : ℝ) + 1) : ℝ[X]) ^ (m n)) :
    ∀ n : Nat, (P n).Splits := by
  rr_product_factor_sequence using
    base := hbase,
    cutoff := N,
    recurrence := hrec,
    certificate := scalarPowAuto

/-- Product-factor recurrence router, automatic powered affine factor. -/
example {P : Nat → ℝ[X]} {t : Nat → ℝ} {m : Nat → Nat}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hrec : ∀ n : Nat,
      P (n + 1) = (C ((n : ℝ) + 1) * X + C (t n)) ^ (m n) * P n) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_product_factor_sequence using
    base := hbase,
    recurrence := hrec,
    certificate := affinePowAuto

/-- Product-factor router, powered affine factor from a cutoff row. -/
example {P : Nat → ℝ[X]} {s t : Nat → ℝ} {m : Nat → Nat}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hs : ∀ n : Nat, s n ≠ 0)
    (hrec : ∀ n : Nat,
      N ≤ n → P (n + 1) = (C (s n) * X + C (t n)) ^ (m n) * P n) :
    ∀ n : Nat, (P n).Splits := by
  rr_product_factor_sequence using
    base := hbase,
    slope_ne := hs,
    cutoff := N,
    recurrence := hrec,
    certificate := affinePow

/-- Product-factor router, automatic powered affine factor from a cutoff row. -/
example {P : Nat → ℝ[X]} {t : Nat → ℝ} {m : Nat → Nat}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hrec : ∀ n : Nat,
      N ≤ n → P (n + 1) = P n * (C ((n : ℝ) + 1) * X + C (t n)) ^ (m n)) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_product_factor_sequence using
    base := hbase,
    cutoff := N,
    recurrence := hrec,
    certificate := affinePowAuto

/-- Product-factor recurrence router, constant-first powered affine factor. -/
example {P : Nat → ℝ[X]} {s t : Nat → ℝ} {m : Nat → Nat}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hs : ∀ n : Nat, s n ≠ 0)
    (hrec :
      ∀ n : Nat, P (n + 1) = P n * (C (t n) + C (s n) * X) ^ (m n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_factor_sequence using
    base := hbase,
    slope_ne := hs,
    recurrence := hrec,
    certificate := constFirstAffinePow

/-- Product-factor router, constant-first powered affine cutoff branch. -/
example {P : Nat → ℝ[X]} {s t : Nat → ℝ} {m : Nat → Nat}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hs : ∀ n : Nat, s n ≠ 0)
    (hrec : ∀ n : Nat,
      N ≤ n → P (n + 1) = P n * (C (t n) + C (s n) * X) ^ (m n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_factor_sequence using
    base := hbase,
    slope_ne := hs,
    cutoff := N,
    recurrence := hrec,
    certificate := constFirstAffinePow

/-- Product-factor router, automatic constant-first powered affine cutoff. -/
example {P : Nat → ℝ[X]} {t : Nat → ℝ} {m : Nat → Nat}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hrec : ∀ n : Nat,
      N ≤ n →
        P (n + 1) = (C (t n) + C ((n : ℝ) + 1) * X) ^ (m n) * P n) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_product_factor_sequence using
    base := hbase,
    cutoff := N,
    recurrence := hrec,
    certificate := constFirstAffinePowAuto

/-- Product-formula router, finite product of linear factors. -/
example {P : Nat → ℝ[X]} {roots : Nat → Nat → ℝ}
    (hroot : ∀ n : Nat,
      P n = ∏ j ∈ Finset.range n, (X - C (roots n j))) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_formula_sequence using
    formula := hroot,
    certificate := finiteLinearProduct

/-- Product-formula router, scalar finite product of linear factors. -/
example {P : Nat → ℝ[X]} {c : Nat → ℝ} {rootCount : Nat → Nat}
    {roots : Nat → Nat → ℝ}
    (hc : ∀ n : Nat, c n ≠ 0)
    (hroot : ∀ n : Nat,
      P n = C (c n) *
        ∏ j ∈ Finset.range (rootCount n), (X - C (roots n j))) :
    ∀ n : Nat, (P n).Splits := by
  rr_product_formula_sequence using
    scalar_ne_zero := hc,
    root_grid := hroot,
    certificate := scalarFiniteLinearProduct

/-- J1 factorable-row router, scalar finite product of linear factors. -/
example {P : Nat → ℝ[X]} {c : Nat → ℝ} {rootCount : Nat → Nat}
    {roots : Nat → Nat → ℝ}
    (hc : ∀ n : Nat, c n ≠ 0)
    (hroot : ∀ n : Nat,
      P n = C (c n) *
        ∏ j ∈ Finset.range (rootCount n), (X - C (roots n j))) :
    ∀ n : Nat, (P n).Splits := by
  rr_j1_factorable_sequence_realrooted using
    scalar_ne_zero := hc,
    root_grid := hroot,
    certificate := finiteLinearProduct

/-- J1 gap-3 reciprocal router from a real-rooted model family. -/
example {P R : Nat → ℝ[X]} {D : Nat → Nat}
    (hmodel : ∀ n : Nat, R n ≠ 0 ∧ (R n).Splits)
    (hdegree : ∀ n : Nat, (R n).natDegree ≤ D n)
    (hreciprocal : ∀ n : Nat, P n = reciprocalShift (D n) (R n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_j1_gap3_reciprocal_sequence_realrooted using
    model_realrooted := hmodel,
    degree := hdegree,
    reciprocal := hreciprocal,
    certificate := modelRealRooted

/-- J1 gap-3 reciprocal router from a PF-polynomial model family. -/
example {P R : Nat → ℝ[X]} {D : Nat → Nat}
    (hmodel : ∀ n : Nat, IsPFPolynomial (R n))
    (hmodel_ne : ∀ n : Nat, R n ≠ 0)
    (hdegree : ∀ n : Nat, (R n).natDegree ≤ D n)
    (hreciprocal : ∀ n : Nat, P n = reciprocalShift (D n) (R n)) :
    ∀ n : Nat, (P n).Splits := by
  rr_j1_gap3_reciprocal_sequence_realrooted using
    model_pf := hmodel,
    model_ne := hmodel_ne,
    degree := hdegree,
    reciprocal := hreciprocal,
    certificate := modelPF


end Tactic
end RealRooted
