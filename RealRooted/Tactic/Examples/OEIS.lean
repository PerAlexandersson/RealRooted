import RealRooted.Tactic.OEIS

/-!
# OEIS router examples

Smoke tests for OEIS-facing certificate routers.  These examples keep the
router honest: it only dispatches to existing tactic backends after the caller
names a concrete certificate branch.
-/

open Polynomial
open scoped BigOperators

namespace RealRooted
namespace Tactic

/-- Direct Family I2 half-line branch, adjacent-`Prec` endpoint. -/
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) +
          (C (2 : ℝ) * X * (1 - X)) * (P (n + 1)).derivative +
          (X * (C (2 : ℝ) - X)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_i2_derivative_lag_sequence using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    degree_two := hdeg_two,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno,
    certificate := directHalfLine

/-- Direct Family I2 half-line branch, real-rootedness endpoint. -/
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) +
          (C (2 : ℝ) * X * (1 - X)) * (P (n + 1)).derivative +
          (X * (C (2 : ℝ) - X)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_i2_derivative_lag_sequence_realrooted using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    degree_two := hdeg_two,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno,
    certificate := directHalfLine

/-- Direct Family I2 half-line branch, Narayana-style zero-lag derivative
term. -/
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]} {m : Nat}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) +
          (C (((n + 1 : Nat) : ℝ) + 2 * m + 2)⁻¹ *
              (C (2 : ℝ) * X - C (2 : ℝ) * X ^ 2)) *
            (P (n + 1)).derivative +
          0 * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_i2_derivative_lag_sequence_realrooted using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    degree_two := hdeg_two,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno,
    certificate := directHalfLine

/-- `A358623`-style Wagner gap-lag branch, adjacent-`Prec` endpoint. -/
example {P : Nat → ℝ[X]} {a c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hnonneg : ∀ k : Nat, HasNonnegCoeffs (P k))
    (hdeg : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (ha : ∀ n : Nat, 0 < a n)
    (hc : ∀ n : Nat, 0 < c n)
    (hrec : ∀ n : Nat,
      P (n + 2) = X * (C (c n) * (P (n + 1)).derivative + C (a n) * P n)) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_i2_derivative_lag_sequence using
    base := hbase,
    nonneg_coeffs := hnonneg,
    degree_two := hdeg,
    lag_coeff_pos := ha,
    derivative_coeff_pos := hc,
    recurrence := hrec,
    certificate := wagnerGap

/-- `A358623`-style Wagner gap-lag branch, real-rootedness endpoint. -/
example {P : Nat → ℝ[X]} {a c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hnonneg : ∀ k : Nat, HasNonnegCoeffs (P k))
    (hdeg : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (ha : ∀ n : Nat, 0 < a n)
    (hc : ∀ n : Nat, 0 < c n)
    (hrec : ∀ n : Nat,
      P (n + 2) = X * (C (c n) * (P (n + 1)).derivative + C (a n) * P n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_i2_derivative_lag_sequence_realrooted using
    base := hbase,
    nonneg_coeffs := hnonneg,
    degree_two := hdeg,
    lag_coeff_pos := ha,
    derivative_coeff_pos := hc,
    recurrence := hrec,
    certificate := wagnerGap

/-- Denominator-normalized direct Family I2 branch. -/
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hraw : ∀ n : Nat,
      C ((n : ℝ) + 3) * P (n + 2) =
        C ((n : ℝ) + 3) * (U n * P (n + 1)) +
          C ((n : ℝ) + 3) *
            ((C (2 : ℝ) * X * (1 - X)) * (P (n + 1)).derivative) +
          C ((n : ℝ) + 3) * ((X * (C (2 : ℝ) - X)) * P n))
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_i2_derivative_lag_sequence_den_coeff using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    degree_two := hdeg_two,
    deriv_factor := fun _ => C (2 : ℝ) * X * (1 - X),
    lag_factor := fun _ => X * (C (2 : ℝ) - X),
    norm_deriv_coeff := fun _ => (1 : ℝ),
    norm_lag_coeff := fun _ => (1 : ℝ),
    den := fun n => (n : ℝ) + 3,
    raw_deriv_coeff := fun n => (n : ℝ) + 3,
    raw_lag_coeff := fun n => (n : ℝ) + 3,
    deriv_coeff_eq := rr_scalar_coeff_all_term,
    lag_coeff_eq := rr_scalar_coeff_all_term,
    raw_recurrence := hraw,
    degree_succ := hdeg_succ,
    no_common_roots := hno,
    certificate := directHalfLine

/-- Denominator-normalized direct Family I2 branch, real-rootedness endpoint. -/
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hraw : ∀ n : Nat,
      C ((n : ℝ) + 3) * P (n + 2) =
        C ((n : ℝ) + 3) * (U n * P (n + 1)) +
          C ((n : ℝ) + 3) *
            ((C (2 : ℝ) * X * (1 - X)) * (P (n + 1)).derivative) +
          C ((n : ℝ) + 3) * ((X * (C (2 : ℝ) - X)) * P n))
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_i2_derivative_lag_sequence_den_coeff_realrooted using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    degree_two := hdeg_two,
    deriv_factor := fun _ => C (2 : ℝ) * X * (1 - X),
    lag_factor := fun _ => X * (C (2 : ℝ) - X),
    norm_deriv_coeff := fun _ => (1 : ℝ),
    norm_lag_coeff := fun _ => (1 : ℝ),
    den := fun n => (n : ℝ) + 3,
    raw_deriv_coeff := fun n => (n : ℝ) + 3,
    raw_lag_coeff := fun n => (n : ℝ) + 3,
    deriv_coeff_eq := rr_scalar_coeff_all_term,
    lag_coeff_eq := rr_scalar_coeff_all_term,
    raw_recurrence := hraw,
    degree_succ := hdeg_succ,
    no_common_roots := hno,
    certificate := directHalfLine

/-- Denominator-normalized Wagner gap-lag branch. -/
example {P : Nat → ℝ[X]} {a c d : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hnonneg : ∀ k : Nat, HasNonnegCoeffs (P k))
    (hdeg : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (ha : ∀ n : Nat, 0 < a n)
    (hc : ∀ n : Nat, 0 < c n)
    (hd : ∀ n : Nat, 0 < d n)
    (hrec : ∀ n : Nat,
      C (d n) * P (n + 2) =
        X * (C (c n) * (P (n + 1)).derivative + C (a n) * P n)) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_i2_derivative_lag_sequence_den using
    base := hbase,
    nonneg_coeffs := hnonneg,
    degree_two := hdeg,
    lag_coeff_pos := ha,
    derivative_coeff_pos := hc,
    denom_pos := hd,
    recurrence := hrec,
    certificate := wagnerGap

/-- Denominator-normalized Wagner gap-lag branch, real-rootedness endpoint. -/
example {P : Nat → ℝ[X]} {a c d : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hnonneg : ∀ k : Nat, HasNonnegCoeffs (P k))
    (hdeg : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (ha : ∀ n : Nat, 0 < a n)
    (hc : ∀ n : Nat, 0 < c n)
    (hd : ∀ n : Nat, 0 < d n)
    (hrec : ∀ n : Nat,
      C (d n) * P (n + 2) =
        X * (C (c n) * (P (n + 1)).derivative + C (a n) * P n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_i2_derivative_lag_sequence_den_realrooted using
    base := hbase,
    nonneg_coeffs := hnonneg,
    degree_two := hdeg,
    lag_coeff_pos := ha,
    derivative_coeff_pos := hc,
    denom_pos := hd,
    recurrence := hrec,
    certificate := wagnerGap

/-- Family E positive `t`-lag router, exact-current `X` branch. -/
example {P : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hrec : ∀ n : Nat,
      P (n + 2) = X * P (n + 1) + (C ((n : ℝ) + 1) * X) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_e_positive_t_lag_sequence using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno,
    certificate := currentX

/-- Family E positive `t`-lag router, exact-current `X` real-rooted endpoint. -/
example {P : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hrec : ∀ n : Nat,
      P (n + 2) = X * P (n + 1) + (C (1 : ℝ) * X) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_e_positive_t_lag_sequence_realrooted using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno,
    certificate := currentX

/-- Family E positive `t`-lag router, scalar-current `c_n X` branch. -/
example {P : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hrec : ∀ n : Nat,
      P (n + 2) =
        (C ((n : ℝ) + 2) * X) * P (n + 1) +
          (C ((n : ℝ) + 2) * X) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_e_positive_t_lag_sequence_realrooted using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno,
    certificate := currentCX

/-- Family E positive `t`-lag router, scalar-current `c_n X` Prec endpoint. -/
example {P : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hrec : ∀ n : Nat,
      P (n + 2) =
        (C ((n : ℝ) + 2) * X) * P (n + 1) +
          (C ((n : ℝ) + 2) * X) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_e_positive_t_lag_sequence using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno,
    certificate := currentCX

/-- Family E positive `t`-lag router, current factor `1 + X` branch. -/
example {P : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hrec : ∀ n : Nat,
      P (n + 2) = (1 + X : ℝ[X]) * P (n + 1) + (C (n : ℝ) * X) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_e_positive_t_lag_sequence using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno,
    certificate := currentOneAddX

/-- Family E positive `t`-lag router, current factor `1 + X` real-rooted endpoint. -/
example {P : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hrec : ∀ n : Nat,
      P (n + 2) = (1 + X : ℝ[X]) * P (n + 1) + (C ((n : ℝ) + 4) * X) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_e_positive_t_lag_sequence_realrooted using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno,
    certificate := currentOneAddX

/-- Family E positive `t`-lag router, `X * (1 - X)` lag branch. -/
example {P : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hrec : ∀ n : Nat,
      P (n + 2) = (C (2 : ℝ) * X) * P (n + 1) + (X * (1 - X)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_e_positive_t_lag_sequence using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno,
    certificate := xOneSubX

/-- Family E positive `t`-lag router, `X * (1 - X)` real-rooted endpoint. -/
example {P : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hrec : ∀ n : Nat,
      P (n + 2) = (C (2 : ℝ) * X) * P (n + 1) + (X * (1 - X)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_e_positive_t_lag_sequence_realrooted using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno,
    certificate := xOneSubX

/-- Family E positive `t`-lag router, `X * (a_n - b_n * X)` lag branch. -/
example {P : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hrec : ∀ n : Nat,
      P (n + 2) =
        (-(C ((n : ℝ) + 2)) + C (2 : ℝ) * X) * P (n + 1) +
          (X * (C (n : ℝ) - C (1 : ℝ) * X)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_e_positive_t_lag_sequence using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno,
    certificate := xCSubCMulX

/-- Family E positive `t`-lag router, `X * (a_n - b_n * X)` real-rooted endpoint. -/
example {P : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hrec : ∀ n : Nat,
      P (n + 2) =
        (-(C ((n : ℝ) + 2)) + C (2 : ℝ) * X) * P (n + 1) +
          (X * (C (n : ℝ) - C (1 : ℝ) * X)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_e_positive_t_lag_sequence_realrooted using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno,
    certificate := xCSubCMulX

/-- Family E positive `t`-lag router, `c_n * X * (a_n - b_n * X)` lag branch. -/
example {P : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hrec : ∀ n : Nat,
      P (n + 2) =
        (-(C ((n : ℝ) + 2)) + C (2 : ℝ) * X) * P (n + 1) +
          (C (1 : ℝ) * X * (C (n : ℝ) - C (1 : ℝ) * X)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_e_positive_t_lag_sequence using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno,
    certificate := cMulXCSubCMulX

/-- Family E positive `t`-lag router, scaled affine-down lag real-rooted endpoint. -/
example {P : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hrec : ∀ n : Nat,
      P (n + 2) =
        (-(C ((n : ℝ) + 2)) + C (2 : ℝ) * X) * P (n + 1) +
          (C (1 : ℝ) * X * (C (n : ℝ) - C (1 : ℝ) * X)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_e_positive_t_lag_sequence_realrooted using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno,
    certificate := cMulXCSubCMulX

/-- Family E plateau-safe positive `t`-lag router, Wagner-X branch. -/
example {P : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hrec : ∀ n : Nat, P (n + 2) = P (n + 1) + X * P n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_e_positive_t_lag_sequence_realrooted using
    base := hbase,
    nonneg_coeffs := hnonneg,
    recurrence := hrec,
    certificate := plateauX

/-- Family E plateau-safe positive `t`-lag router, Wagner-X Prec endpoint. -/
example {P : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hrec : ∀ n : Nat, P (n + 2) = P (n + 1) + X * P n) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_e_positive_t_lag_sequence using
    base := hbase,
    nonneg_coeffs := hnonneg,
    recurrence := hrec,
    certificate := plateauX

/-- Family E positive `t R_n(t)` lag router. -/
example {P : Nat → ℝ[X]} {A R : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hR : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → 0 ≤ (R n).eval r)
    (hrec : ∀ n : Nat, P (n + 2) = A n * P (n + 1) + (X * R n) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_e_positive_t_lag_sequence_realrooted using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    factor_nonneg := hR,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno,
    certificate := tR

/-- Family E positive `c_n t R_n(t)` lag router with explicit coefficient. -/
example {P : Nat → ℝ[X]} {A R : Nat → ℝ[X]} {c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hR : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → 0 ≤ (R n).eval r)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        A n * P (n + 1) + (C (c n) * X * R n) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_e_positive_t_lag_sequence using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    coeff_nonneg := hc,
    factor_nonneg := hR,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno,
    certificate := cTR

/-- Family E positive `c_n t R_n(t)` lag router with automatic coefficient. -/
example {P : Nat → ℝ[X]} {A R : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hR : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → 0 ≤ (R n).eval r)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        A n * P (n + 1) + (C ((n : ℝ) + 1) * X * R n) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, (P n).Splits := by
  rr_e_positive_t_lag_sequence_realrooted using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    factor_nonneg := hR,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno,
    certificate := cTRAuto

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

/-- Linear-power interlacing exit exposed through the OEIS facade. -/
example (n : Nat) :
    Interlaces ((C (2 : ℝ) + C 3 * X) ^ n)
      ((C (2 : ℝ) + C 3 * X) ^ (n + 1)) := by
  rr_interlaces_linear_pow using
    const := 2,
    slope := 3,
    slope_pos := by norm_num,
    index := n

/-- Linear-power nonnegative-coefficient exit exposed through the OEIS facade. -/
example (n : Nat) :
    HasNonnegCoeffs ((C (2 : ℝ) + C 3 * X) ^ n) := by
  rr_hasNonnegCoeffs_linear_pow using
    a_nonneg := by norm_num,
    b_nonneg := by norm_num,
    index := n

/-- Hadamard PF exit exposed through the OEIS facade. -/
example {p q : ℝ[X]}
    (hp : IsPFPolynomial p) (hq : IsPFPolynomial q) :
    IsPFPolynomial (hadamardProduct p q) := by
  rr_hadamard_pf using
    left_pf := hp,
    right_pf := hq

/-- Hermite--Biehler statement exit exposed through the OEIS facade. -/
example :
    hermiteBiehlerForwardPosStatement := by
  rr_hermite_biehler_forward_pos_statement

/-- Kurtz coefficient-criterion exit exposed through the OEIS facade. -/
example {p : ℝ[X]}
    (hdeg : 2 ≤ p.natDegree)
    (hpos : ∀ i ≤ p.natDegree, 0 < p.coeff i)
    (hineq : RealRooted.Challenges.Kurtz.KurtzStrictInequalities p) :
    p.Splits := by
  rr_kurtz using
    degree := hdeg,
    positive_coeffs := hpos,
    inequalities := hineq

/-- Narayana polynomial exit exposed through the OEIS facade. -/
example {m n : ℕ} :
    (narayanaPolynomial m n).Splits := by
  rr_narayana_polynomial_splits using
    parameter := m,
    degree := n

/-- Second-derivative shell exposed through the OEIS facade. -/
example {P U V : Nat → ℝ[X]} {a : Nat → ℝ}
    (hbase_zero : P 0 ≠ 0 ∧ (P 0).Splits)
    (hbase_one : P 1 ≠ 0 ∧ (P 1).Splits)
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (ha_ne : ∀ n : Nat, a n ≠ 0)
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hinner_pos : ∀ n : Nat,
      HasPosLeadingCoeff (U n * P (n + 1) + V n * (P (n + 1)).derivative))
    (hV_nonpos : ∀ n : Nat, ∀ r,
      (P (n + 1)).IsRoot r → (V n).eval r ≤ 0)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        C (a n) * (U n * P (n + 1) + V n * (P (n + 1)).derivative) +
          (U n * P (n + 1) + V n * (P (n + 1)).derivative).derivative)
    (hinner_deg_lo : ∀ n : Nat,
      (P (n + 1)).natDegree ≤
        (U n * P (n + 1) + V n * (P (n + 1)).derivative).natDegree)
    (hinner_deg_hi : ∀ n : Nat,
      (U n * P (n + 1) + V n * (P (n + 1)).derivative).natDegree ≤
        (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, (P n).Splits := by
  rr_mw_plus_derivative_sequence using
    outer := a,
    base_zero := hbase_zero,
    base_one := hbase_one,
    pos_lc := hpos,
    outer_nonzero := ha_ne,
    degree_two := hdeg_two,
    inner_pos_lc := hinner_pos,
    coeff_nonpos := hV_nonpos,
    recurrence := hrec,
    inner_degree_lower := hinner_deg_lo,
    inner_degree_upper := hinner_deg_hi

/-- Product-parity router, automatic scalar step with supplied factor. -/
example {P F : Nat → ℝ[X]}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hfactor : ∀ n : Nat, F n ≠ 0 ∧ (F n).Splits)
    (hscalar : ∀ n : Nat,
      P (2 * n + 1) = C ((n : ℝ) + 1) * P (2 * n))
    (hstep : ∀ n : Nat, P (2 * n + 2) = P (2 * n + 1) * F n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_parity_sequence using
    base := hbase,
    factor_realrooted := hfactor,
    scalar_step := hscalar,
    factor_step := hstep,
    certificate := scalarThenFactorAuto

/-- Product-parity router, supplied factor with cutoff. -/
example {P F : Nat → ℝ[X]} {a : Nat → ℝ}
    (N : Nat)
    (hbase : ∀ k : Nat, k ≤ 2 * N → P k ≠ 0 ∧ (P k).Splits)
    (ha : ∀ n : Nat, N ≤ n → a n ≠ 0)
    (hfactor : ∀ n : Nat, N ≤ n → F n ≠ 0 ∧ (F n).Splits)
    (hscalar : ∀ n : Nat, N ≤ n → P (2 * n + 1) = P (2 * n) * C (a n))
    (hstep : ∀ n : Nat, N ≤ n → P (2 * n + 2) = F n * P (2 * n + 1)) :
    ∀ n : Nat, (P n).Splits := by
  rr_product_parity_sequence using
    base := hbase,
    scalar_ne := ha,
    factor_realrooted := hfactor,
    cutoff := N,
    scalar_step := hscalar,
    factor_step := hstep,
    certificate := scalarThenFactor

/-- Product-parity router, automatic scalar supplied factor with cutoff. -/
example {P F : Nat → ℝ[X]}
    (N : Nat)
    (hbase : ∀ k : Nat, k ≤ 2 * N → P k ≠ 0 ∧ (P k).Splits)
    (hfactor : ∀ n : Nat, N ≤ n → F n ≠ 0 ∧ (F n).Splits)
    (hscalar : ∀ n : Nat, N ≤ n →
      P (2 * n + 1) = C (2 * (n : ℝ) + 1) * P (2 * n))
    (hstep : ∀ n : Nat, N ≤ n → P (2 * n + 2) = P (2 * n + 1) * F n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_parity_sequence using
    base := hbase,
    factor_realrooted := hfactor,
    cutoff := N,
    scalar_step := hscalar,
    factor_step := hstep,
    certificate := scalarThenFactorAuto

/-- Product-parity router, automatic scalar then unit-linear step. -/
example {P : Nat → ℝ[X]} {b : Nat → ℝ}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hscalar : ∀ n : Nat,
      P (2 * n + 1) = C (2 * (n : ℝ) + 1) * P (2 * n))
    (hlinear : ∀ n : Nat,
      P (2 * n + 2) = (X + C (b n)) * P (2 * n + 1)) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_product_parity_sequence using
    base := hbase,
    scalar_step := hscalar,
    linear_step := hlinear,
    certificate := scalarThenXAddCAuto

/-- Product-parity router, constant-first unit-linear step. -/
example {P : Nat → ℝ[X]} {a b : Nat → ℝ}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (ha : ∀ n : Nat, a n ≠ 0)
    (hscalar : ∀ n : Nat, P (2 * n + 1) = P (2 * n) * C (a n))
    (hlinear : ∀ n : Nat, P (2 * n + 2) = P (2 * n + 1) * (C (b n) + X)) :
    ∀ n : Nat, (P n).Splits := by
  rr_product_parity_sequence using
    base := hbase,
    scalar_ne := ha,
    scalar_step := hscalar,
    linear_step := hlinear,
    certificate := scalarThenCAddX

/-- Product-parity router, unit-linear step with cutoff. -/
example {P : Nat → ℝ[X]} {a b : Nat → ℝ}
    (N : Nat)
    (hbase : ∀ k : Nat, k ≤ 2 * N → P k ≠ 0 ∧ (P k).Splits)
    (ha : ∀ n : Nat, N ≤ n → a n ≠ 0)
    (hscalar : ∀ n : Nat, N ≤ n → P (2 * n + 1) = C (a n) * P (2 * n))
    (hlinear :
      ∀ n : Nat, N ≤ n → P (2 * n + 2) = P (2 * n + 1) * (X + C (b n))) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_parity_sequence using
    base := hbase,
    scalar_ne := ha,
    cutoff := N,
    scalar_step := hscalar,
    linear_step := hlinear,
    certificate := scalarThenXAddC

/-- Product-parity router, automatic scalar constant-first unit-linear cutoff. -/
example {P : Nat → ℝ[X]} {b : Nat → ℝ}
    (N : Nat)
    (hbase : ∀ k : Nat, k ≤ 2 * N → P k ≠ 0 ∧ (P k).Splits)
    (hscalar : ∀ n : Nat, N ≤ n →
      P (2 * n + 1) = P (2 * n) * C (2 * (n : ℝ) + 1))
    (hlinear :
      ∀ n : Nat, N ≤ n → P (2 * n + 2) = (C (b n) + X) * P (2 * n + 1)) :
    ∀ n : Nat, (P n).Splits := by
  rr_product_parity_sequence using
    base := hbase,
    cutoff := N,
    scalar_step := hscalar,
    linear_step := hlinear,
    certificate := scalarThenCAddXAuto

/-- Product-parity router, automatic scalar then root-zero powers. -/
example {P : Nat → ℝ[X]} {m : Nat → Nat}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hscalar : ∀ n : Nat,
      P (2 * n + 1) = C ((n : ℝ) + 1) * P (2 * n))
    (hstep : ∀ n : Nat, P (2 * n + 2) = P (2 * n + 1) * X ^ (m n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_parity_sequence using
    base := hbase,
    scalar_step := hscalar,
    factor_step := hstep,
    certificate := scalarThenRootZeroPowAuto

/-- Product-parity router, powered unit-linear step. -/
example {P : Nat → ℝ[X]} {a b : Nat → ℝ} {m : Nat → Nat}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (ha : ∀ n : Nat, a n ≠ 0)
    (hscalar : ∀ n : Nat, P (2 * n + 1) = C (a n) * P (2 * n))
    (hstep : ∀ n : Nat,
      P (2 * n + 2) = (X + C (b n)) ^ (m n) * P (2 * n + 1)) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_product_parity_sequence using
    base := hbase,
    scalar_ne := ha,
    scalar_step := hscalar,
    factor_step := hstep,
    certificate := scalarThenXAddCPow

/-- Product-parity router, automatic scalar then powered constant-first step. -/
example {P : Nat → ℝ[X]} {b : Nat → ℝ} {m : Nat → Nat}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hscalar : ∀ n : Nat,
      P (2 * n + 1) = C ((n : ℝ) + 1) * P (2 * n))
    (hstep : ∀ n : Nat,
      P (2 * n + 2) = P (2 * n + 1) * (C (b n) + X) ^ (m n)) :
    ∀ n : Nat, (P n).Splits := by
  rr_product_parity_sequence using
    base := hbase,
    scalar_step := hscalar,
    factor_step := hstep,
    certificate := scalarThenCAddXPowAuto

/-- Product-parity router, root-zero powers with cutoff. -/
example {P : Nat → ℝ[X]} {a : Nat → ℝ} {m : Nat → Nat}
    (N : Nat)
    (hbase : ∀ k : Nat, k ≤ 2 * N → P k ≠ 0 ∧ (P k).Splits)
    (ha : ∀ n : Nat, N ≤ n → a n ≠ 0)
    (hscalar : ∀ n : Nat, N ≤ n → P (2 * n + 1) = P (2 * n) * C (a n))
    (hstep : ∀ n : Nat, N ≤ n → P (2 * n + 2) = X ^ (m n) * P (2 * n + 1)) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_product_parity_sequence using
    base := hbase,
    scalar_ne := ha,
    cutoff := N,
    scalar_step := hscalar,
    factor_step := hstep,
    certificate := scalarThenRootZeroPow

/-- Product-parity router, powered unit-linear step with cutoff. -/
example {P : Nat → ℝ[X]} {b : Nat → ℝ} {m : Nat → Nat}
    (N : Nat)
    (hbase : ∀ k : Nat, k ≤ 2 * N → P k ≠ 0 ∧ (P k).Splits)
    (hscalar : ∀ n : Nat, N ≤ n →
      P (2 * n + 1) = C ((n : ℝ) + 1) * P (2 * n))
    (hstep : ∀ n : Nat, N ≤ n →
      P (2 * n + 2) = P (2 * n + 1) * (X + C (b n)) ^ (m n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_parity_sequence using
    base := hbase,
    cutoff := N,
    scalar_step := hscalar,
    factor_step := hstep,
    certificate := scalarThenXAddCPowAuto

/-- Product-parity router, powered constant-first step with cutoff. -/
example {P : Nat → ℝ[X]} {a b : Nat → ℝ} {m : Nat → Nat}
    (N : Nat)
    (hbase : ∀ k : Nat, k ≤ 2 * N → P k ≠ 0 ∧ (P k).Splits)
    (ha : ∀ n : Nat, N ≤ n → a n ≠ 0)
    (hscalar : ∀ n : Nat, N ≤ n → P (2 * n + 1) = C (a n) * P (2 * n))
    (hstep : ∀ n : Nat, N ≤ n →
      P (2 * n + 2) = (C (b n) + X) ^ (m n) * P (2 * n + 1)) :
    ∀ n : Nat, (P n).Splits := by
  rr_product_parity_sequence using
    base := hbase,
    scalar_ne := ha,
    cutoff := N,
    scalar_step := hscalar,
    factor_step := hstep,
    certificate := scalarThenCAddXPow

/-- Product-parity lift router, odd rows are scalar multiples of `X` times
the even quotient. -/
example {P Q : Nat → ℝ[X]} {a : Nat → ℝ}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (ha : ∀ n : Nat, a n ≠ 0)
    (heven : ∀ n : Nat, P (2 * n) = Q n)
    (hodd : ∀ n : Nat, P (2 * n + 1) = C (a n) * X * Q n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_parity_lift_sequence using
    even_realrooted := hquot,
    scalar_ne := ha,
    even_factorization := heven,
    odd_factorization := hodd,
    certificate := scalarXOdd

/-- Endpoint-pair router, sum-then-`X` branch. -/
example {A B : Nat → ℝ[X]}
    (hbase : Prec (A 0) (B 0))
    (hA0_nonneg : HasNonnegCoeffs (A 0))
    (hB0_nonneg : HasNonnegCoeffs (B 0))
    (hstepA : ∀ n : Nat, A (n + 1) = A n + B n)
    (hstepB : ∀ n : Nat, B (n + 1) = B n + X * A (n + 1))
    (hcop : ∀ n : Nat, IsCoprime (B n) (X * A (n + 1))) :
    ∀ n : Nat, Prec (A n) (B n) := by
  rr_endpoint_pair_sequence using
    base := hbase,
    left_nonneg := hA0_nonneg,
    right_nonneg := hB0_nonneg,
    sum_step := hstepA,
    x_step := hstepB,
    coprime := hcop,
    certificate := sumThenX

/-- Endpoint-pair router, real-rootedness endpoint for the reversed branch. -/
example {A B : Nat → ℝ[X]}
    (hbase : Prec (A 0) (B 0))
    (hA0_nonneg : HasNonnegCoeffs (A 0))
    (hB0_nonneg : HasNonnegCoeffs (B 0))
    (hstepB : ∀ n : Nat, B (n + 1) = B n + X * A n)
    (hstepA : ∀ n : Nat, A (n + 1) = A n + B (n + 1))
    (hcop : ∀ n : Nat, IsCoprime (B n) (X * A n)) :
    ∀ n : Nat, (A n ≠ 0 ∧ (A n).Splits) ∧ (B n ≠ 0 ∧ (B n).Splits) := by
  rr_endpoint_pair_sequence_realrooted using
    base := hbase,
    left_nonneg := hA0_nonneg,
    right_nonneg := hB0_nonneg,
    x_step := hstepB,
    sum_step := hstepA,
    coprime := hcop,
    certificate := xThenSum

/-- Endpoint-pair lift router, sum-then-`X` branch. -/
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
  rr_endpoint_pair_lift_sequence using
    base := hbase,
    left_nonneg := hA0_nonneg,
    right_nonneg := hB0_nonneg,
    sum_step := hstepA,
    x_step := hstepB,
    coprime := hcop,
    even_factorization := hrowA,
    odd_factorization := hrowB,
    certificate := sumThenX

/-- Endpoint-pair lift router, reversed branch. -/
example {P A B : Nat → ℝ[X]} {mA mB : Nat → Nat}
    (hbase : Prec (A 0) (B 0))
    (hA0_nonneg : HasNonnegCoeffs (A 0))
    (hB0_nonneg : HasNonnegCoeffs (B 0))
    (hstepB : ∀ n : Nat, B (n + 1) = B n + X * A n)
    (hstepA : ∀ n : Nat, A (n + 1) = A n + B (n + 1))
    (hcop : ∀ n : Nat, IsCoprime (B n) (X * A n))
    (hrowA : ∀ n : Nat, P (2 * n) = (X + C (1 : ℝ)) ^ (mA n) * A n)
    (hrowB : ∀ n : Nat, P (2 * n + 1) = (X + C (1 : ℝ)) ^ (mB n) * B n) :
    ∀ n : Nat, (P n).Splits := by
  rr_endpoint_pair_lift_sequence using
    base := hbase,
    left_nonneg := hA0_nonneg,
    right_nonneg := hB0_nonneg,
    x_step := hstepB,
    sum_step := hstepA,
    coprime := hcop,
    even_factorization := hrowA,
    odd_factorization := hrowB,
    certificate := xThenSum

/-- Endpoint-pair lift router, reversed branch with swapped row quotient. -/
example {P A B : Nat → ℝ[X]} {mA mB : Nat → Nat}
    (hbase : Prec (A 0) (B 0))
    (hA0_nonneg : HasNonnegCoeffs (A 0))
    (hB0_nonneg : HasNonnegCoeffs (B 0))
    (hstepB : ∀ n : Nat, B (n + 1) = B n + X * A n)
    (hstepA : ∀ n : Nat, A (n + 1) = A n + B (n + 1))
    (hcop : ∀ n : Nat, IsCoprime (B n) (X * A n))
    (hrowB : ∀ n : Nat, P (2 * n) = (X + C (1 : ℝ)) ^ (mB n) * B n)
    (hrowA : ∀ n : Nat, P (2 * n + 1) = (X + C (1 : ℝ)) ^ (mA n) * A n) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_endpoint_pair_lift_sequence using
    base := hbase,
    left_nonneg := hA0_nonneg,
    right_nonneg := hB0_nonneg,
    x_step := hstepB,
    sum_step := hstepA,
    coprime := hcop,
    even_factorization := hrowB,
    odd_factorization := hrowA,
    certificate := xThenSumSwapped

/-- Product-lift router with a supplied factor certificate. -/
example {P Q F : Nat → ℝ[X]}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hfactor : ∀ n : Nat, F n ≠ 0 ∧ (F n).Splits)
    (hrow : ∀ n : Nat, P n = Q n * F n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_lift_sequence using
    quotient_realrooted := hquot,
    factor_realrooted := hfactor,
    factorization := hrow,
    certificate := suppliedFactor

/-- Product-lift router with supplied factor and cutoff. -/
example {P Q F : Nat → ℝ[X]}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hquot : ∀ n : Nat, N ≤ n → Q n ≠ 0 ∧ (Q n).Splits)
    (hfactor : ∀ n : Nat, N ≤ n → F n ≠ 0 ∧ (F n).Splits)
    (hrow : ∀ n : Nat, N ≤ n → P n = F n * Q n) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_product_lift_sequence using
    base := hbase,
    quotient_realrooted := hquot,
    factor_realrooted := hfactor,
    cutoff := N,
    factorization := hrow,
    certificate := suppliedFactor

/-- Product-lift router, repeated root-zero factor. -/
example {P Q : Nat → ℝ[X]} {m : Nat → Nat}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, P n = Q n * X ^ (m n)) :
    ∀ n : Nat, (P n).Splits := by
  rr_product_lift_sequence using
    quotient_realrooted := hquot,
    factorization := hrow,
    certificate := rootZeroPow

/-- Product-lift router, root-zero factor with cutoff. -/
example {P Q : Nat → ℝ[X]}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hquot : ∀ n : Nat, N ≤ n → Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, N ≤ n → P n = X * Q n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_lift_sequence using
    base := hbase,
    quotient_realrooted := hquot,
    cutoff := N,
    factorization := hrow,
    certificate := rootZero

/-- Product-lift router, root-zero powers with cutoff. -/
example {P Q : Nat → ℝ[X]} {m : Nat → Nat}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hquot : ∀ n : Nat, N ≤ n → Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, N ≤ n → P n = Q n * X ^ (m n)) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_product_lift_sequence using
    base := hbase,
    quotient_realrooted := hquot,
    cutoff := N,
    factorization := hrow,
    certificate := rootZeroPow

/-- Product-lift router, row-wise unit linear factor. -/
example {P Q : Nat → ℝ[X]} {t : Nat → ℝ}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, P n = (X + C (t n)) * Q n) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_product_lift_sequence using
    quotient_realrooted := hquot,
    factorization := hrow,
    certificate := xAddC

/-- Product-lift router, row-wise unit linear factor with cutoff. -/
example {P Q : Nat → ℝ[X]} {t : Nat → ℝ}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hquot : ∀ n : Nat, N ≤ n → Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, N ≤ n → P n = Q n * (X + C (t n))) :
    ∀ n : Nat, (P n).Splits := by
  rr_product_lift_sequence using
    base := hbase,
    quotient_realrooted := hquot,
    cutoff := N,
    factorization := hrow,
    certificate := xAddC

/-- Product-lift router, row-wise unit linear power. -/
example {P Q : Nat → ℝ[X]} {t : Nat → ℝ} {m : Nat → Nat}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, P n = Q n * (X + C (t n)) ^ (m n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_lift_sequence using
    quotient_realrooted := hquot,
    factorization := hrow,
    certificate := rowXAddCPow

/-- Product-lift router, automatic scalar certificate. -/
example {P Q : Nat → ℝ[X]}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, P n = C ((n : ℝ) + 1) * Q n) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_product_lift_sequence using
    quotient_realrooted := hquot,
    factorization := hrow,
    certificate := scalarAuto

/-- Product-lift router, automatic affine-slope certificate. -/
example {P Q : Nat → ℝ[X]} {t : Nat → ℝ}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, P n = Q n * (C ((n : ℝ) + 1) * X + C (t n))) :
    ∀ n : Nat, (P n).Splits := by
  rr_product_lift_sequence using
    quotient_realrooted := hquot,
    factorization := hrow,
    certificate := affineAuto

/-- Product-lift router, constant-first unit linear factor. -/
example {P Q : Nat → ℝ[X]} {t : Nat → ℝ}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, P n = Q n * (C (t n) + X)) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_product_lift_sequence using
    quotient_realrooted := hquot,
    factorization := hrow,
    certificate := cAddX

/-- Product-lift router, constant-first unit linear factor with cutoff. -/
example {P Q : Nat → ℝ[X]} {t : Nat → ℝ}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hquot : ∀ n : Nat, N ≤ n → Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, N ≤ n → P n = (C (t n) + X) * Q n) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_product_lift_sequence using
    base := hbase,
    quotient_realrooted := hquot,
    cutoff := N,
    factorization := hrow,
    certificate := cAddX

/-- Product-lift router, fixed unit-linear power. -/
example {P Q : Nat → ℝ[X]} {m : Nat → Nat}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, P n = (X + C (1 : ℝ)) ^ (m n) * Q n) :
    ∀ n : Nat, (P n).Splits := by
  rr_product_lift_sequence using
    quotient_realrooted := hquot,
    factorization := hrow,
    certificate := fixedXAddCPow

/-- Product-lift router, row-wise constant-first unit-linear power. -/
example {P Q : Nat → ℝ[X]} {t : Nat → ℝ} {m : Nat → Nat}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, P n = (C (t n) + X) ^ (m n) * Q n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_lift_sequence using
    quotient_realrooted := hquot,
    factorization := hrow,
    certificate := cAddXPow

/-- Product-lift router, scalar-power factor. -/
example {P Q : Nat → ℝ[X]} {c : Nat → ℝ} {m : Nat → Nat}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hc : ∀ n : Nat, c n ≠ 0)
    (hrow : ∀ n : Nat, P n = Q n * (C (c n) : ℝ[X]) ^ (m n)) :
    ∀ n : Nat, (P n).Splits := by
  rr_product_lift_sequence using
    quotient_realrooted := hquot,
    scalar_ne := hc,
    factorization := hrow,
    certificate := scalarPow

/-- Product-lift router, automatic scalar-power factor. -/
example {P Q : Nat → ℝ[X]} {m : Nat → Nat}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, P n = (C ((n : ℝ) + 1) : ℝ[X]) ^ (m n) * Q n) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_product_lift_sequence using
    quotient_realrooted := hquot,
    factorization := hrow,
    certificate := scalarPowAuto

/-- Product-lift router, scalar factor with cutoff. -/
example {P Q : Nat → ℝ[X]} {c : Nat → ℝ}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hquot : ∀ n : Nat, N ≤ n → Q n ≠ 0 ∧ (Q n).Splits)
    (hc : ∀ n : Nat, N ≤ n → c n ≠ 0)
    (hrow : ∀ n : Nat, N ≤ n → P n = C (c n) * Q n) :
    ∀ n : Nat, (P n).Splits := by
  rr_product_lift_sequence using
    base := hbase,
    quotient_realrooted := hquot,
    scalar_ne := hc,
    cutoff := N,
    factorization := hrow,
    certificate := scalar

/-- Product-lift router, automatic scalar factor with cutoff. -/
example {P Q : Nat → ℝ[X]}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hquot : ∀ n : Nat, N ≤ n → Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, N ≤ n → P n = Q n * C ((n : ℝ) + 1)) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_product_lift_sequence using
    base := hbase,
    quotient_realrooted := hquot,
    cutoff := N,
    factorization := hrow,
    certificate := scalarAuto

/-- Product-lift router, scalar-power factor with cutoff. -/
example {P Q : Nat → ℝ[X]} {c : Nat → ℝ} {m : Nat → Nat}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hquot : ∀ n : Nat, N ≤ n → Q n ≠ 0 ∧ (Q n).Splits)
    (hc : ∀ n : Nat, N ≤ n → c n ≠ 0)
    (hrow : ∀ n : Nat, N ≤ n → P n = Q n * (C (c n) : ℝ[X]) ^ (m n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_lift_sequence using
    base := hbase,
    quotient_realrooted := hquot,
    scalar_ne := hc,
    cutoff := N,
    factorization := hrow,
    certificate := scalarPow

/-- Product-lift router, automatic scalar-power factor with cutoff. -/
example {P Q : Nat → ℝ[X]} {m : Nat → Nat}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hquot : ∀ n : Nat, N ≤ n → Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat,
      N ≤ n → P n = (C ((n : ℝ) + 1) : ℝ[X]) ^ (m n) * Q n) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_product_lift_sequence using
    base := hbase,
    quotient_realrooted := hquot,
    cutoff := N,
    factorization := hrow,
    certificate := scalarPowAuto

/-- Product-lift router, affine factor with cutoff. -/
example {P Q : Nat → ℝ[X]} {s t : Nat → ℝ}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hquot : ∀ n : Nat, N ≤ n → Q n ≠ 0 ∧ (Q n).Splits)
    (hs : ∀ n : Nat, N ≤ n → s n ≠ 0)
    (hrow : ∀ n : Nat, N ≤ n → P n = (C (s n) * X + C (t n)) * Q n) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_product_lift_sequence using
    base := hbase,
    quotient_realrooted := hquot,
    slope_ne := hs,
    cutoff := N,
    factorization := hrow,
    certificate := affine

/-- Product-lift router, automatic affine factor with cutoff. -/
example {P Q : Nat → ℝ[X]} {t : Nat → ℝ}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hquot : ∀ n : Nat, N ≤ n → Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat,
      N ≤ n → P n = Q n * (C ((n : ℝ) + 1) * X + C (t n))) :
    ∀ n : Nat, (P n).Splits := by
  rr_product_lift_sequence using
    base := hbase,
    quotient_realrooted := hquot,
    cutoff := N,
    factorization := hrow,
    certificate := affineAuto

/-- Product-lift router, constant-first affine factor with cutoff. -/
example {P Q : Nat → ℝ[X]} {s t : Nat → ℝ}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hquot : ∀ n : Nat, N ≤ n → Q n ≠ 0 ∧ (Q n).Splits)
    (hs : ∀ n : Nat, N ≤ n → s n ≠ 0)
    (hrow : ∀ n : Nat, N ≤ n → P n = Q n * (C (t n) + C (s n) * X)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_lift_sequence using
    base := hbase,
    quotient_realrooted := hquot,
    slope_ne := hs,
    cutoff := N,
    factorization := hrow,
    certificate := constFirstAffine

/-- Product-lift router, automatic constant-first affine factor with cutoff. -/
example {P Q : Nat → ℝ[X]} {t : Nat → ℝ}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hquot : ∀ n : Nat, N ≤ n → Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat,
      N ≤ n → P n = (C (t n) + C ((n : ℝ) + 1) * X) * Q n) :
    ∀ n : Nat, (P n).Splits := by
  rr_product_lift_sequence using
    base := hbase,
    quotient_realrooted := hquot,
    cutoff := N,
    factorization := hrow,
    certificate := constFirstAffineAuto

/-- Product-lift router, constant-first affine factor. -/
example {P Q : Nat → ℝ[X]} {s t : Nat → ℝ}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hs : ∀ n : Nat, s n ≠ 0)
    (hrow : ∀ n : Nat, P n = (C (t n) + C (s n) * X) * Q n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_lift_sequence using
    quotient_realrooted := hquot,
    slope_ne := hs,
    factorization := hrow,
    certificate := constFirstAffine

/-- Product-lift router, automatic constant-first affine factor. -/
example {P Q : Nat → ℝ[X]} {t : Nat → ℝ}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, P n = Q n * (C (t n) + C ((n : ℝ) + 1) * X)) :
    ∀ n : Nat, (P n).Splits := by
  rr_product_lift_sequence using
    quotient_realrooted := hquot,
    factorization := hrow,
    certificate := constFirstAffineAuto

/-- Product-lift router, powered affine factor. -/
example {P Q : Nat → ℝ[X]} {s t : Nat → ℝ} {m : Nat → Nat}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hs : ∀ n : Nat, s n ≠ 0)
    (hrow : ∀ n : Nat, P n = Q n * (C (s n) * X + C (t n)) ^ (m n)) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_product_lift_sequence using
    quotient_realrooted := hquot,
    slope_ne := hs,
    factorization := hrow,
    certificate := affinePow

/-- Product-lift router, automatic powered affine factor. -/
example {P Q : Nat → ℝ[X]} {t : Nat → ℝ} {m : Nat → Nat}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat,
      P n = (C ((n : ℝ) + 1) * X + C (t n)) ^ (m n) * Q n) :
    ∀ n : Nat, (P n).Splits := by
  rr_product_lift_sequence using
    quotient_realrooted := hquot,
    factorization := hrow,
    certificate := affinePowAuto

/-- Product-lift router, powered constant-first affine factor. -/
example {P Q : Nat → ℝ[X]} {s t : Nat → ℝ} {m : Nat → Nat}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hs : ∀ n : Nat, s n ≠ 0)
    (hrow : ∀ n : Nat, P n = (C (t n) + C (s n) * X) ^ (m n) * Q n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_lift_sequence using
    quotient_realrooted := hquot,
    slope_ne := hs,
    factorization := hrow,
    certificate := constFirstAffinePow

/-- Product-lift router, automatic powered constant-first affine factor. -/
example {P Q : Nat → ℝ[X]} {t : Nat → ℝ} {m : Nat → Nat}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat,
      P n = Q n * (C (t n) + C ((n : ℝ) + 1) * X) ^ (m n)) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_product_lift_sequence using
    quotient_realrooted := hquot,
    factorization := hrow,
    certificate := constFirstAffinePowAuto

/-- Product-lift router, fixed unit-linear power with cutoff. -/
example {P Q : Nat → ℝ[X]} {m : Nat → Nat}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hquot : ∀ n : Nat, N ≤ n → Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, N ≤ n → P n = (X + C (1 : ℝ)) ^ (m n) * Q n) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_product_lift_sequence using
    base := hbase,
    quotient_realrooted := hquot,
    cutoff := N,
    factorization := hrow,
    certificate := fixedXAddCPow

/-- Product-lift router, row-wise unit-linear power with cutoff. -/
example {P Q : Nat → ℝ[X]} {t : Nat → ℝ} {m : Nat → Nat}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hquot : ∀ n : Nat, N ≤ n → Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, N ≤ n → P n = Q n * (X + C (t n)) ^ (m n)) :
    ∀ n : Nat, (P n).Splits := by
  rr_product_lift_sequence using
    base := hbase,
    quotient_realrooted := hquot,
    cutoff := N,
    factorization := hrow,
    certificate := rowXAddCPow

/-- Product-lift router, constant-first unit-linear power with cutoff. -/
example {P Q : Nat → ℝ[X]} {t : Nat → ℝ} {m : Nat → Nat}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hquot : ∀ n : Nat, N ≤ n → Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, N ≤ n → P n = (C (t n) + X) ^ (m n) * Q n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_lift_sequence using
    base := hbase,
    quotient_realrooted := hquot,
    cutoff := N,
    factorization := hrow,
    certificate := cAddXPow

/-- Product-lift router, affine-power factor with cutoff. -/
example {P Q : Nat → ℝ[X]} {s t : Nat → ℝ} {m : Nat → Nat}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hquot : ∀ n : Nat, N ≤ n → Q n ≠ 0 ∧ (Q n).Splits)
    (hs : ∀ n : Nat, N ≤ n → s n ≠ 0)
    (hrow : ∀ n : Nat,
      N ≤ n → P n = Q n * (C (s n) * X + C (t n)) ^ (m n)) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_product_lift_sequence using
    base := hbase,
    quotient_realrooted := hquot,
    slope_ne := hs,
    cutoff := N,
    factorization := hrow,
    certificate := affinePow

/-- Product-lift router, automatic affine-power factor with cutoff. -/
example {P Q : Nat → ℝ[X]} {t : Nat → ℝ} {m : Nat → Nat}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hquot : ∀ n : Nat, N ≤ n → Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat,
      N ≤ n → P n = (C ((n : ℝ) + 1) * X + C (t n)) ^ (m n) * Q n) :
    ∀ n : Nat, (P n).Splits := by
  rr_product_lift_sequence using
    base := hbase,
    quotient_realrooted := hquot,
    cutoff := N,
    factorization := hrow,
    certificate := affinePowAuto

/-- Product-lift router, powered constant-first affine factor with cutoff. -/
example {P Q : Nat → ℝ[X]} {s t : Nat → ℝ} {m : Nat → Nat}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hquot : ∀ n : Nat, N ≤ n → Q n ≠ 0 ∧ (Q n).Splits)
    (hs : ∀ n : Nat, N ≤ n → s n ≠ 0)
    (hrow : ∀ n : Nat,
      N ≤ n → P n = (C (t n) + C (s n) * X) ^ (m n) * Q n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_lift_sequence using
    base := hbase,
    quotient_realrooted := hquot,
    slope_ne := hs,
    cutoff := N,
    factorization := hrow,
    certificate := constFirstAffinePow

/-- Product-lift router, automatic powered constant-first affine cutoff. -/
example {P Q : Nat → ℝ[X]} {t : Nat → ℝ} {m : Nat → Nat}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hquot : ∀ n : Nat, N ≤ n → Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat,
      N ≤ n → P n = Q n * (C (t n) + C ((n : ℝ) + 1) * X) ^ (m n)) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_product_lift_sequence using
    base := hbase,
    quotient_realrooted := hquot,
    cutoff := N,
    factorization := hrow,
    certificate := constFirstAffinePowAuto

/-- Family G negative-lag router, shifted-square branch. -/
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hrec : ∀ n : Nat,
      P (n + 2) =
        A n * P (n + 1) +
          (-(C ((n : ℝ) + 1)) * (1 - X : ℝ[X]) ^ 2) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_g_negative_lag_sequence using
    base := hbase,
    pos_lc := hpos,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno,
    certificate := negativeSquare

/-- Family G denominator-normalized negative-square branch. -/
example {P : Nat → ℝ[X]} {A q : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hraw : ∀ n : Nat,
      C ((n : ℝ) + 1) * P (n + 2) =
        C ((n : ℝ) + 1) * (A n * P (n + 1)) +
          C ((n : ℝ) + 1) * (-(q n) ^ 2 * P n))
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_g_negative_lag_sequence_den_coeff using
    base := hbase,
    pos_lc := hpos,
    square_factor := q,
    coeff := fun _ => (1 : ℝ),
    raw_coeff := fun n => (n : ℝ) + 1,
    den := fun n => (n : ℝ) + 1,
    coeff_eq := rr_scalar_coeff_all_term,
    raw_recurrence := hraw,
    degree_succ := hdeg_succ,
    no_common_roots := hno,
    certificate := negativeSquare

/-- Family G denominator-normalized negative-square real-rootedness endpoint. -/
example {P : Nat → ℝ[X]} {A q : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hraw : ∀ n : Nat,
      C ((n : ℝ) + 1) * P (n + 2) =
        C ((n : ℝ) + 1) * (A n * P (n + 1)) +
          C ((n : ℝ) + 1) * (-(q n) ^ 2 * P n))
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_g_negative_lag_sequence_den_coeff_realrooted using
    base := hbase,
    pos_lc := hpos,
    square_factor := q,
    coeff := fun _ => (1 : ℝ),
    raw_coeff := fun n => (n : ℝ) + 1,
    den := fun n => (n : ℝ) + 1,
    coeff_eq := rr_scalar_coeff_all_term,
    raw_recurrence := hraw,
    degree_succ := hdeg_succ,
    no_common_roots := hno,
    certificate := negativeSquare

/-- Family G negative-lag router, monic quadratic real-rooted endpoint. -/
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hrec : ∀ n : Nat,
      P (n + 2) =
        A n * P (n + 1) + (-(X ^ 2 + C (2 : ℝ) * X + C (4 : ℝ))) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_g_negative_lag_sequence_realrooted using
    base := hbase,
    pos_lc := hpos,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno,
    certificate := negativeMonicQuadratic

/-- Family G negative-lag router, non-monic quadratic branch. -/
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hrec : ∀ n : Nat,
      P (n + 2) =
        A n * P (n + 1) +
          (-(C (2 : ℝ) * X ^ 2 + C (-1 : ℝ) * X + C (1 : ℝ))) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_g_negative_lag_sequence using
    base := hbase,
    pos_lc := hpos,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno,
    certificate := negativeQuadratic

/-- Family G denominator-normalized non-monic quadratic branch. -/
example {P : Nat → ℝ[X]} {Araw : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hraw : ∀ n : Nat,
      C ((n : ℝ) + 1) * P (n + 2) =
        Araw n * P (n + 1) +
          (-(C (2 * ((n : ℝ) + 1)) * X ^ 2 +
            C (-((n : ℝ) + 1)) * X + C ((n : ℝ) + 1))) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_g_negative_lag_sequence_den_coeff using
    base := hbase,
    pos_lc := hpos,
    leading := fun _ => (2 : ℝ),
    linear := fun _ => (-1 : ℝ),
    constant := fun _ => (1 : ℝ),
    raw_leading := fun n => 2 * ((n : ℝ) + 1),
    raw_linear := fun n => -((n : ℝ) + 1),
    raw_constant := fun n => (n : ℝ) + 1,
    den := fun n => (n : ℝ) + 1,
    leading_coeff_eq := rr_scalar_coeff_all_term,
    linear_coeff_eq := rr_scalar_coeff_all_term,
    constant_coeff_eq := rr_scalar_coeff_all_term,
    raw_recurrence := hraw,
    degree_succ := hdeg_succ,
    no_common_roots := hno,
    certificate := negativeQuadratic

/-- Family G denominator-normalized non-monic quadratic real-rooted endpoint. -/
example {P : Nat → ℝ[X]} {Araw : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hraw : ∀ n : Nat,
      C ((n : ℝ) + 1) * P (n + 2) =
        Araw n * P (n + 1) +
          (-(C (2 * ((n : ℝ) + 1)) * X ^ 2 +
            C (-((n : ℝ) + 1)) * X + C ((n : ℝ) + 1))) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_g_negative_lag_sequence_den_coeff_realrooted using
    base := hbase,
    pos_lc := hpos,
    leading := fun _ => (2 : ℝ),
    linear := fun _ => (-1 : ℝ),
    constant := fun _ => (1 : ℝ),
    raw_leading := fun n => 2 * ((n : ℝ) + 1),
    raw_linear := fun n => -((n : ℝ) + 1),
    raw_constant := fun n => (n : ℝ) + 1,
    den := fun n => (n : ℝ) + 1,
    leading_coeff_eq := rr_scalar_coeff_all_term,
    linear_coeff_eq := rr_scalar_coeff_all_term,
    constant_coeff_eq := rr_scalar_coeff_all_term,
    raw_recurrence := hraw,
    degree_succ := hdeg_succ,
    no_common_roots := hno,
    certificate := negativeQuadratic

/-- Family G negative-lag router, global nonpositive branch. -/
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hrec : ∀ n : Nat,
      P (n + 2) = A n * P (n + 1) + (-(X ^ 2 : ℝ[X])) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_g_negative_lag_sequence_realrooted using
    base := hbase,
    pos_lc := hpos,
    lag := fun _ => -(X ^ 2 : ℝ[X]),
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno,
    certificate := globalNonpos

/-- Family G denominator-normalized global nonpositive branch. -/
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hraw : ∀ n : Nat,
      C ((n : ℝ) + 1) * P (n + 2) =
        C ((n : ℝ) + 1) *
          (A n * P (n + 1) + (-(X ^ 2 : ℝ[X])) * P n))
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, (P n).Splits := by
  rr_g_negative_lag_sequence_den_realrooted using
    base := hbase,
    pos_lc := hpos,
    lag := fun _ => -(X ^ 2 : ℝ[X]),
    raw_recurrence := hraw,
    degree_succ := hdeg_succ,
    no_common_roots := hno,
    certificate := globalNonpos

/-- Family H second-derivative router, PF-bidiagonal cubic-residual branch. -/
example
    {P : Nat → ℝ[X]} {a0 a1 b1 b2 c2 c3 : Nat → ℝ} {d : Nat → ℕ}
    (hbackend : jensenPencilBidiagonalPreserverStatement)
    (hbase : IsPFPolynomial (P 0))
    (hdeg : ∀ n : Nat, (P n).natDegree ≤ d n)
    (hcert : ∀ n : Nat,
      BidiagonalCubicResidualCertificate
        (fun k => secondDerivativeQuadraticCoeff (a0 n) (b1 n) (c2 n) k)
        (fun k => secondDerivativeQuadraticCoeff (a1 n) (b2 n) (c3 n) k)
        (d n))
    (hrec : ∀ n : Nat,
      P (n + 1) =
        secondDerivativeBidiagonalForm
          (a0 n) (a1 n) (b1 n) (b2 n) (c2 n) (c3 n) (P n)) :
    ∀ n : Nat, IsPFPolynomial (P n) := by
  rr_h_second_derivative_sequence using
    route := pf_bidiagonal,
    jensen_backend := hbackend,
    cubic_certificate := hcert,
    base := hbase,
    degree := hdeg,
    recurrence := hrec

/-- Family H second-derivative router, cutoff and normalized PF-bidiagonal
branch. -/
example
    {P : Nat → ℝ[X]} {alphaSeq betaSeq : Nat → ℕ → ℝ}
    {a0 a1 b1 b2 c2 c3 : Nat → ℝ} {d : Nat → ℕ}
    (hbackend : jensenPencilBidiagonalPreserverStatement)
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → IsPFPolynomial (P n))
    (hdeg : ∀ n : Nat, N ≤ n → (P n).natDegree ≤ d n)
    (hcert : ∀ n : Nat, N ≤ n →
      BidiagonalCubicResidualCertificate (alphaSeq n) (betaSeq n) (d n))
    (hnorm : ∀ n : Nat, N ≤ n →
      secondDerivativeBidiagonalForm
          (a0 n) (a1 n) (b1 n) (b2 n) (c2 n) (c3 n) (P n) =
        bidiagonalOperator (alphaSeq n) (betaSeq n) (P n))
    (hne : ∀ n : Nat, P n ≠ 0)
    (hrec : ∀ n : Nat, N ≤ n →
      P (n + 1) =
        secondDerivativeBidiagonalForm
          (a0 n) (a1 n) (b1 n) (b2 n) (c2 n) (c3 n) (P n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_h_second_derivative_sequence using
    route := pf_bidiagonal,
    jensen_backend := hbackend,
    cubic_certificate := hcert,
    cutoff := N,
    base := hbase,
    degree := hdeg,
    normalizer := hnorm,
    recurrence := hrec,
    nonzero := hne

end Tactic
end RealRooted
