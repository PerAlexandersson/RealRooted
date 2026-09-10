import RealRooted.Tactic.LiuWang.SequenceIntervals

/-!
# Liu--Wang negative inner-window regression examples

Sequence tests for negative inner-window lag factors, including shifted,
scaled, and denominator-normalized certificate variants.
-/

open Polynomial

namespace RealRooted
namespace Tactic

/-- Inner-window negative affine lag:
`P_{n+2}=A_nP_{n+1}-c_n(a_n+b_n t)P_n`, with `0 <= b_n <= a_n`. -/
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]} {c a b : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hb : ∀ n : Nat, 0 ≤ b n)
    (hba : ∀ n : Nat, b n ≤ a n)
    (hroot_lower : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → -1 ≤ r)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        A n * P (n + 1) + (-(C (c n)) * (C (a n) + C (b n) * X)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_lw_neg_C_mul_affine_inner_lag_sequence_nonneg using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    coeff_nonneg := hc,
    slope_nonneg := hb,
    slope_le_const := hba,
    root_lower := hroot_lower,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Real-rootedness endpoint for the inner-window negative affine lag. -/
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]} {c a b : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hb : ∀ n : Nat, 0 ≤ b n)
    (hba : ∀ n : Nat, b n ≤ a n)
    (hroot_lower : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → -1 ≤ r)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        A n * P (n + 1) + (-(C (c n)) * (C (a n) + C (b n) * X)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_lw_neg_C_mul_affine_inner_lag_sequence_realrooted_nonneg using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    coeff_nonneg := hc,
    slope_nonneg := hb,
    slope_le_const := hba,
    root_lower := hroot_lower,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Explicit coefficient endpoint for the `-c_n(1+t)` lag. -/
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]} {c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hroot_lower : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → -1 ≤ r)
    (hrec : ∀ n : Nat,
      P (n + 2) = A n * P (n + 1) + (-(C (c n)) * (1 + X)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_lw_neg_C_mul_one_add_X_lag_sequence_nonneg using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    coeff_nonneg := hc,
    root_lower := hroot_lower,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Automatic coefficient endpoint for the `-c_n(1+t)` lag. -/
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hroot_lower : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → -1 ≤ r)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        A n * P (n + 1) + (-(C ((n : ℝ) + 1)) * (1 + X)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_lw_neg_C_mul_one_add_X_lag_sequence_nonneg_auto using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    root_lower := hroot_lower,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Explicit real-rootedness endpoint for the `-c_n(1+t)` lag. -/
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]} {c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hroot_lower : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → -1 ≤ r)
    (hrec : ∀ n : Nat,
      P (n + 2) = A n * P (n + 1) + (-(C (c n)) * (1 + X)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_lw_neg_C_mul_one_add_X_lag_sequence_realrooted_nonneg using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    coeff_nonneg := hc,
    root_lower := hroot_lower,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- The common `-c_n(1+t)` lag has a shorter wrapper and an automatic
coefficient side-goal. -/
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hroot_lower : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → -1 ≤ r)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        A n * P (n + 1) + (-(C ((n : ℝ) + 1)) * (1 + X)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_lw_neg_C_mul_one_add_X_lag_sequence_realrooted_nonneg_auto using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    root_lower := hroot_lower,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Scalar-denominator raw recurrence whose normalized lag is `-(1+t)`.

This is the denominator bookkeeping needed for `A124848`/`A347056`-style
records after the active-range coefficient equation is supplied. -/
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hroot_lower : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → -1 ≤ r)
    (hraw : ∀ n : Nat,
      C (-((n : ℝ) + 1)) * P (n + 2) =
        C (-((n : ℝ) + 1)) * (A n * P (n + 1)) +
          (C ((n : ℝ) + 1) * (1 + X)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
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
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hroot_lower : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → -1 ≤ r)
    (hraw : ∀ n : Nat,
      C (-((n : ℝ) + 1)) * P (n + 2) =
        C (-((n : ℝ) + 1)) * (A n * P (n + 1)) +
          (C ((n : ℝ) + 1) * (1 + X)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
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
    (hbase : Prec (P 0) (P 1))
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
    (hbase : Prec (P 0) (P 1))
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

/-- The tighter affine lag `-c_n(1+2t)` only needs roots in `[-1/2,0]`;
the upper half is still derived from nonnegative coefficients. -/
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hroot_lower : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → -(1 / 2 : ℝ) ≤ r)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        A n * P (n + 1) +
          (-(C ((n : ℝ) + 1)) * (1 + C (2 : ℝ) * X)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_lw_neg_C_mul_one_add_two_X_lag_sequence_realrooted_nonneg_auto using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    root_lower_half := hroot_lower,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Explicit coefficient endpoint for the tighter `-c_n(1+2t)` lag. -/
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]} {c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hroot_lower : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → -(1 / 2 : ℝ) ≤ r)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        A n * P (n + 1) + (-(C (c n)) * (1 + C (2 : ℝ) * X)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_lw_neg_C_mul_one_add_two_X_lag_sequence_nonneg using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    coeff_nonneg := hc,
    root_lower_half := hroot_lower,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Automatic coefficient endpoint for the tighter `-c_n(1+2t)` lag. -/
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hroot_lower : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → -(1 / 2 : ℝ) ≤ r)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        A n * P (n + 1) +
          (-(C ((n : ℝ) + 1)) * (1 + C (2 : ℝ) * X)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_lw_neg_C_mul_one_add_two_X_lag_sequence_nonneg_auto using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    root_lower_half := hroot_lower,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Explicit real-rootedness endpoint for the tighter `-c_n(1+2t)` lag. -/
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]} {c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hroot_lower : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → -(1 / 2 : ℝ) ≤ r)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        A n * P (n + 1) + (-(C (c n)) * (1 + C (2 : ℝ) * X)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_lw_neg_C_mul_one_add_two_X_lag_sequence_realrooted_nonneg using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    coeff_nonneg := hc,
    root_lower_half := hroot_lower,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Compact negative-inner router for `-c_n(1+t)`. -/
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hroot_lower : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → -1 ≤ r)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        A n * P (n + 1) + (-(C ((n : ℝ) + 1)) * (1 + X)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_lw_negative_inner_lag_sequence using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    root_lower := hroot_lower,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno,
    certificate := negOneAddX

/-- Compact negative-inner router for `-c_n(1+t)`, real-rootedness endpoint. -/
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hroot_lower : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → -1 ≤ r)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        A n * P (n + 1) + (-(C ((n : ℝ) + 1)) * (1 + X)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_lw_negative_inner_lag_sequence_realrooted using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    root_lower := hroot_lower,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno,
    certificate := negOneAddX

/-- Compact negative-inner router for `-c_n(1+2t)`. -/
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hroot_lower : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → -(1 / 2 : ℝ) ≤ r)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        A n * P (n + 1) +
          (-(C ((n : ℝ) + 1)) * (1 + C (2 : ℝ) * X)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_lw_negative_inner_lag_sequence using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    root_lower := hroot_lower,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno,
    certificate := negOneAddTwoX

/-- Compact negative-inner router for `-c_n(1+2t)`, real-rootedness endpoint. -/
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hroot_lower : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → -(1 / 2 : ℝ) ≤ r)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        A n * P (n + 1) +
          (-(C ((n : ℝ) + 1)) * (1 + C (2 : ℝ) * X)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_lw_negative_inner_lag_sequence_realrooted using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    root_lower := hroot_lower,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno,
    certificate := negOneAddTwoX

/-- The expanded inner-window lag `c_n(t^2-1)` covers recurrences with
`(-1+t^2)P_n`. -/
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]} {c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hroot_lower : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → -1 ≤ r)
    (hrec : ∀ n : Nat,
      P (n + 2) = A n * P (n + 1) + (C (c n) * (X ^ 2 - 1)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_lw_C_mul_X_sq_sub_one_lag_sequence_nonneg using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    coeff_nonneg := hc,
    root_lower := hroot_lower,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Automatic coefficient endpoint for the expanded `t^2-1` lag. -/
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hroot_lower : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → -1 ≤ r)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        A n * P (n + 1) + (C ((n : ℝ) + 1) * (X ^ 2 - 1)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_lw_C_mul_X_sq_sub_one_lag_sequence_nonneg_auto using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    root_lower := hroot_lower,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Explicit-coefficient real-rootedness endpoint for the expanded `t^2-1`
lag. -/
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]} {c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hroot_lower : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → -1 ≤ r)
    (hrec : ∀ n : Nat,
      P (n + 2) = A n * P (n + 1) + (C (c n) * (X ^ 2 - 1)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_lw_C_mul_X_sq_sub_one_lag_sequence_realrooted_nonneg using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    coeff_nonneg := hc,
    root_lower := hroot_lower,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Automatic real-rootedness endpoint for the expanded inner-window lag
`c_n(t^2-1)`. -/
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hroot_lower : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → -1 ≤ r)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        A n * P (n + 1) + (C ((n : ℝ) + 1) * (X ^ 2 - 1)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_lw_C_mul_X_sq_sub_one_lag_sequence_realrooted_nonneg_auto using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    root_lower := hroot_lower,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Compact inner-window router for scalar `c_n(t^2-1)`. -/
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hroot_lower : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → -1 ≤ r)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        A n * P (n + 1) + (C ((n : ℝ) + 1) * (X ^ 2 - 1)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_lw_inner_window_lag_sequence using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    root_lower := hroot_lower,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno,
    certificate := cMulXSqSubOne

/-- Compact inner-window router for scalar `c_n(t^2-1)`, real-rooted endpoint. -/
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hroot_lower : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → -1 ≤ r)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        A n * P (n + 1) + (C ((n : ℝ) + 1) * (X ^ 2 - 1)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_lw_inner_window_lag_sequence_realrooted using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    root_lower := hroot_lower,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno,
    certificate := cMulXSqSubOne


end Tactic
end RealRooted
