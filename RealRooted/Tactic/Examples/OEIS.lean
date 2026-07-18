import RealRooted.Tactic.OEIS

/-!
# OEIS router examples

Smoke tests for OEIS-facing certificate routers.  These examples keep the
router honest: it only dispatches to existing tactic backends after the caller
names a concrete certificate branch.
-/

open Polynomial

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
    den_nonzero := rr_scalar_active_den_all_term,
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
    den_nonzero := rr_scalar_active_den_all_term,
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

end Tactic
end RealRooted
