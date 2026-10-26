import RealRooted.Tactic.LiuWang.SequenceIntervals

/-!
# Liu--Wang negative inner-window regression examples

Sequence tests for negative inner-window lag factors, including shifted,
scaled, and denominator-normalized certificate variants.
-/

open Polynomial

namespace RealRooted
namespace Tactic

/-- Scalar-denominator raw recurrence whose normalized lag is `-(1+t)`.

This is the denominator bookkeeping needed for `A124848`/`A347056`-style
records after the active-range coefficient equation is supplied. -/
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]}
    (hbase : StrictInterl (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hroot_lower : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → -1 ≤ r)
    (hraw : ∀ n : Nat,
      C (-((n : ℝ) + 1)) * P (n + 2) =
        C (-((n : ℝ) + 1)) * (A n * P (n + 1)) +
          (C ((n : ℝ) + 1) * (1 + X)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, StrictInterl (P n) (P (n + 1)) := by
  rr_lw_neg_C_mul_one_add_X_lag_sequence_den_coeff_nonneg using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    coeff := fun _ => (1 : ℝ),
    coeff_nonneg := rr_lw_coeff_nonneg_seq_term,
    root_lower := hroot_lower,
    raw_recurrence := hraw,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Automatic coefficient endpoint for the denominator-normalized `-(1+t)` lag. -/
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]}
    (hbase : StrictInterl (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hroot_lower : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → -1 ≤ r)
    (hraw : ∀ n : Nat,
      C (-((n : ℝ) + 1)) * P (n + 2) =
        C (-((n : ℝ) + 1)) * (A n * P (n + 1)) +
          (C ((n : ℝ) + 1) * (1 + X)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, StrictInterl (P n) (P (n + 1)) := by
  rr_lw_neg_C_mul_one_add_X_lag_sequence_den_coeff_nonneg_auto using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    coeff := fun _ => (1 : ℝ),
    root_lower := hroot_lower,
    raw_recurrence := hraw,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Explicit real-rootedness endpoint for the denominator-normalized
`-(1+t)` lag. -/
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]}
    (hbase : StrictInterl (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hroot_lower : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → -1 ≤ r)
    (hraw : ∀ n : Nat,
      C (-((n : ℝ) + 1)) * P (n + 2) =
        C (-((n : ℝ) + 1)) * (A n * P (n + 1)) +
          (C ((n : ℝ) + 1) * (1 + X)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_lw_neg_C_mul_one_add_X_lag_sequence_den_coeff_realrooted_nonneg using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    coeff := fun _ => (1 : ℝ),
    coeff_nonneg := rr_lw_coeff_nonneg_seq_term,
    root_lower := hroot_lower,
    raw_recurrence := hraw,
    degree_succ := hdeg_succ,
    no_common_roots := hno

example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]}
    (hbase : StrictInterl (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hroot_lower : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → -1 ≤ r)
    (hraw : ∀ n : Nat,
      C (-((n : ℝ) + 1)) * P (n + 2) =
        C (-((n : ℝ) + 1)) * (A n * P (n + 1)) +
          (C ((n : ℝ) + 1) * (1 + X)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_lw_neg_C_mul_one_add_X_lag_sequence_den_coeff_realrooted_nonneg_auto using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    coeff := fun _ => (1 : ℝ),
    root_lower := hroot_lower,
    raw_recurrence := hraw,
    degree_succ := hdeg_succ,
    no_common_roots := hno

end Tactic
end RealRooted
