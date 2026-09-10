import RealRooted.Tactic.Examples.LiuWang.Step
import RealRooted.Tactic.Examples.LiuWang.CurrentFactors
import RealRooted.Tactic.Examples.LiuWang.StrictPositiveLag
import RealRooted.Tactic.Examples.LiuWang.AffineHalfLine
import RealRooted.Tactic.Examples.LiuWang.PositiveAffine
import RealRooted.Tactic.Examples.LiuWang.InnerWindow
import RealRooted.Tactic.Examples.LiuWang.Interval
import RealRooted.Tactic.Examples.LiuWang.NegativeInnerWindow
import RealRooted.Tactic.Finish
import RealRooted.Tactic.LiuWang
import RealRooted.Tactic.RootBounds

/-!
# `rr_liu_wang` examples

Abstract smoke tests for the generalized Liu-Wang dispatcher tactics.
-/

open Polynomial

namespace RealRooted
namespace Tactic

/-- Unit strict-degree Family E lag `t(1-t)`. -/
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hrec : ∀ n : Nat,
      P (n + 2) = A n * P (n + 1) + (X * (1 - X)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_lw_X_one_sub_X_lag_sequence using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Real-rootedness endpoint for the unit strict-degree lag `t(1-t)`. -/
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hrec : ∀ n : Nat,
      P (n + 2) = A n * P (n + 1) + (X * (1 - X)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_lw_X_one_sub_X_lag_sequence_realrooted using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Strict-degree lag `t(a_n-b_n t)` with explicit nonnegative parameters. -/
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]} {a b : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (ha : ∀ n : Nat, 0 ≤ a n)
    (hb : ∀ n : Nat, 0 ≤ b n)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        A n * P (n + 1) + (X * (C (a n) - C (b n) * X)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_lw_X_C_sub_C_mul_X_lag_sequence using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    left_coeff_nonneg := ha,
    right_coeff_nonneg := hb,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Automatic parameter side-goals for the strict-degree `t(a_n-b_n t)` lag. -/
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hrec : ∀ n : Nat,
      P (n + 2) =
        A n * P (n + 1) +
          (X * (C ((n : ℝ) + 1) - C (1 : ℝ) * X)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_lw_X_C_sub_C_mul_X_lag_sequence_auto using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Real-rootedness endpoint for the strict-degree `t(a_n-b_n t)` lag. -/
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]} {a b : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (ha : ∀ n : Nat, 0 ≤ a n)
    (hb : ∀ n : Nat, 0 ≤ b n)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        A n * P (n + 1) + (X * (C (a n) - C (b n) * X)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_lw_X_C_sub_C_mul_X_lag_sequence_realrooted using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    left_coeff_nonneg := ha,
    right_coeff_nonneg := hb,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Automatic real-rootedness endpoint for `t(a_n-b_n t)` lags. -/
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hrec : ∀ n : Nat,
      P (n + 2) =
        A n * P (n + 1) +
          (X * (C ((n : ℝ) + 1) - C (1 : ℝ) * X)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_lw_X_C_sub_C_mul_X_lag_sequence_realrooted_auto using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Scalar strict-degree lag `c_n t(a_n-b_n t)`. -/
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]} {c a b : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hc : ∀ n : Nat, 0 ≤ c n)
    (ha : ∀ n : Nat, 0 ≤ a n)
    (hb : ∀ n : Nat, 0 ≤ b n)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        A n * P (n + 1) + (C (c n) * X * (C (a n) - C (b n) * X)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_lw_C_mul_X_C_sub_C_mul_X_lag_sequence using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    scalar_nonneg := hc,
    left_coeff_nonneg := ha,
    right_coeff_nonneg := hb,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Automatic parameter side-goals for the scalar strict-degree lag. -/
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hrec : ∀ n : Nat,
      P (n + 2) =
        A n * P (n + 1) +
          (C ((n : ℝ) + 1) * X *
            (C ((n : ℝ) + 1) - C (1 : ℝ) * X)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_lw_C_mul_X_C_sub_C_mul_X_lag_sequence_auto using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Real-rootedness endpoint for the scalar strict-degree lag. -/
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]} {c a b : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hc : ∀ n : Nat, 0 ≤ c n)
    (ha : ∀ n : Nat, 0 ≤ a n)
    (hb : ∀ n : Nat, 0 ≤ b n)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        A n * P (n + 1) + (C (c n) * X * (C (a n) - C (b n) * X)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_lw_C_mul_X_C_sub_C_mul_X_lag_sequence_realrooted using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    scalar_nonneg := hc,
    left_coeff_nonneg := ha,
    right_coeff_nonneg := hb,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Automatic real-rootedness endpoint for scalar `c_n t(a_n-b_n t)` lags. -/
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hrec : ∀ n : Nat,
      P (n + 2) =
        A n * P (n + 1) +
          (C ((n : ℝ) + 1) * X *
            (C ((n : ℝ) + 1) - C (1 : ℝ) * X)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_lw_C_mul_X_C_sub_C_mul_X_lag_sequence_realrooted_auto using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Generic sequence-level nonpositive-lag shell.

This is the full induction form behind the Family G wrappers: the
sequence-specific file supplies the root-side sign certificate for the lag
coefficient. -/
example {P : Nat → ℝ[X]} {A B : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hB : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → (B n).eval r ≤ 0)
    (hrec : ∀ n : Nat, P (n + 2) = A n * P (n + 1) + B n * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_lw_nonpos_lag_sequence using
    base := hbase,
    pos_lc := hpos,
    lag_nonpos := hB,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- The generic nonpositive-lag shell also gives real-rootedness of all rows. -/
example {P : Nat → ℝ[X]} {A B : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hB : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → (B n).eval r ≤ 0)
    (hrec : ∀ n : Nat, P (n + 2) = A n * P (n + 1) + B n * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_lw_nonpos_lag_sequence_realrooted using
    base := hbase,
    pos_lc := hpos,
    lag_nonpos := hB,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Denominator-normalized generic nonpositive-lag shell. -/
example {P : Nat → ℝ[X]} {A B : Nat → ℝ[X]} {d : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hB : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → (B n).eval r ≤ 0)
    (hD : ∀ n : Nat, d n ≠ 0)
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        C (d n) * (A n * P (n + 1) + B n * P n))
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_lw_nonpos_lag_sequence_den using
    base := hbase,
    pos_lc := hpos,
    lag_nonpos := hB,
    den_nonzero := hD,
    raw_recurrence := hraw,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Real-rootedness endpoint for the denominator-normalized generic
nonpositive-lag shell. -/
example {P : Nat → ℝ[X]} {A B : Nat → ℝ[X]} {d : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hB : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → (B n).eval r ≤ 0)
    (hD : ∀ n : Nat, d n ≠ 0)
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        C (d n) * (A n * P (n + 1) + B n * P n))
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_lw_nonpos_lag_sequence_den_realrooted using
    base := hbase,
    pos_lc := hpos,
    lag_nonpos := hB,
    den_nonzero := hD,
    raw_recurrence := hraw,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Family E2-style global lag: `P_{n+2}=A_n P_{n+1}-t^2P_n`. -/
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hrec : ∀ n : Nat,
      P (n + 2) = A n * P (n + 1) + (-(X ^ 2 : ℝ[X])) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_lw_global_nonpos_sequence_auto using
    base := hbase,
    pos_lc := hpos,
    lag := fun _ => -(X ^ 2 : ℝ[X]),
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Family G global lag: negative-definite monic quadratic. -/
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hrec : ∀ n : Nat,
      P (n + 2) =
        A n * P (n + 1) + (-(X ^ 2 + C (1 : ℝ) * X + C (1 : ℝ))) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_lw_global_nonpos_sequence_auto using
    base := hbase,
    pos_lc := hpos,
    lag := fun _ => -(X ^ 2 + C (1 : ℝ) * X + C (1 : ℝ)),
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Scaled negative-definite quadratic lag, real-rootedness endpoint. -/
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hrec : ∀ n : Nat,
      P (n + 2) =
        A n * P (n + 1) +
          (-(C ((n : ℝ) + 1)) * (X ^ 2 + C (2 : ℝ) * X + C (4 : ℝ))) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_lw_global_nonpos_sequence_realrooted_auto using
    base := hbase,
    pos_lc := hpos,
    lag := fun n =>
      -(C ((n : ℝ) + 1)) * (X ^ 2 + C (2 : ℝ) * X + C (4 : ℝ)),
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Denominator-normalized global nonpositive lag with automatic sign
discharge. -/
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hraw : ∀ n : Nat,
      C ((n : ℝ) + 1) * P (n + 2) =
        C ((n : ℝ) + 1) *
          (A n * P (n + 1) + (-(X ^ 2 : ℝ[X])) * P n))
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_lw_global_nonpos_sequence_den_auto using
    base := hbase,
    pos_lc := hpos,
    lag := fun _ => -(X ^ 2 : ℝ[X]),
    raw_recurrence := hraw,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Real-rootedness endpoint for denominator-normalized global nonpositive
lags. -/
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hraw : ∀ n : Nat,
      C ((n : ℝ) + 1) * P (n + 2) =
        C ((n : ℝ) + 1) *
          (A n * P (n + 1) + (-(X ^ 2 : ℝ[X])) * P n))
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_lw_global_nonpos_sequence_den_realrooted_auto using
    base := hbase,
    pos_lc := hpos,
    lag := fun _ => -(X ^ 2 : ℝ[X]),
    raw_recurrence := hraw,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Projection endpoint for the denominator-normalized global-nonpositive
router. -/
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
  rr_lw_global_nonpos_sequence_den_realrooted_auto using
    base := hbase,
    pos_lc := hpos,
    lag := fun _ => -(X ^ 2 : ℝ[X]),
    raw_recurrence := hraw,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Favard-like sequence shell: negative constant lag with automatic
nonnegativity of `c_n`. -/
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hrec : ∀ n : Nat,
      P (n + 2) = A n * P (n + 1) + (-(C ((n : ℝ) + 1))) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_lw_negative_const_sequence_auto using
    base := hbase,
    pos_lc := hpos,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Favard-like sequence shell with an explicit coefficient certificate. -/
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]} {c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hrec : ∀ n : Nat, P (n + 2) = A n * P (n + 1) + (-(C (c n))) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_lw_negative_const_sequence using
    base := hbase,
    pos_lc := hpos,
    coeff_nonneg := hc,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Favard-like negative-constant shell, real-rootedness endpoint. -/
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]} {c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hrec : ∀ n : Nat, P (n + 2) = A n * P (n + 1) + (-(C (c n))) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_lw_negative_const_sequence_realrooted using
    base := hbase,
    pos_lc := hpos,
    coeff_nonneg := hc,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Favard-like negative-constant shell, automatic real-rootedness endpoint. -/
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hrec : ∀ n : Nat,
      P (n + 2) = A n * P (n + 1) + (-(C ((n : ℝ) + 1))) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_lw_negative_const_sequence_realrooted_auto using
    base := hbase,
    pos_lc := hpos,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Normalized `C (-c_n)` negative-constant lag, real-rootedness endpoint. -/
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]} {c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hrec : ∀ n : Nat, P (n + 2) = A n * P (n + 1) + C (-(c n)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_lw_negative_const_C_neg_sequence_realrooted using
    base := hbase,
    pos_lc := hpos,
    coeff_nonneg := hc,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Normalized `C (-c_n)` negative-constant lag, automatic real-rootedness
endpoint. -/
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hrec : ∀ n : Nat,
      P (n + 2) = A n * P (n + 1) + C (-((n : ℝ) + 1)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_lw_negative_const_C_neg_sequence_realrooted_auto using
    base := hbase,
    pos_lc := hpos,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Normalized `C (-c_n)` lag with an explicit coefficient certificate. -/
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]} {c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hrec : ∀ n : Nat, P (n + 2) = A n * P (n + 1) + C (-(c n)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_lw_negative_const_C_neg_sequence using
    base := hbase,
    pos_lc := hpos,
    coeff_nonneg := hc,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Normalized `C (-c_n)` lag with automatic coefficient positivity. -/
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hrec : ∀ n : Nat,
      P (n + 2) = A n * P (n + 1) + C (-((n : ℝ) + 1)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_lw_negative_const_C_neg_sequence_auto using
    base := hbase,
    pos_lc := hpos,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- `A008459`: scaled negative-square lag after recurrence normalization. -/
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]} {c : Nat → ℝ} {α : ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        A n * P (n + 1) + (-(C (c n)) * (X - C α) ^ 2) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_lw_negative_square_sequence using
    base := hbase,
    pos_lc := hpos,
    coeff_nonneg := hc,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Family G sequence shell: Narayana/Jacobi-style negative-square lag with
automatic coefficient side-goals. -/
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
  rr_lw_negative_square_sequence_auto using
    base := hbase,
    pos_lc := hpos,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Family G sequence shell: shifted-square lag, real-rootedness endpoint. -/
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]} {α : ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hc : ∀ n : Nat, 0 ≤ (n : ℝ) + 1)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        A n * P (n + 1) + (-(C ((n : ℝ) + 1)) * (X - C α) ^ 2) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_lw_negative_square_sequence_realrooted using
    base := hbase,
    pos_lc := hpos,
    coeff_nonneg := hc,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Family G negative-square lag, automatic real-rootedness endpoint. -/
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hrec : ∀ n : Nat,
      P (n + 2) =
        A n * P (n + 1) +
          (-(C ((n : ℝ) + 1)) * (X - C (2 : ℝ)) ^ 2) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_lw_negative_square_sequence_realrooted_auto using
    base := hbase,
    pos_lc := hpos,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Family G shifted-square lag with unit scalar coefficient. -/
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]} {α : ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hrec : ∀ n : Nat,
      P (n + 2) = A n * P (n + 1) + (-((X - C α : ℝ[X]) ^ 2)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_lw_negative_square_sequence_unit using
    base := hbase,
    pos_lc := hpos,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- `A091042`/`A122076`: unit shifted-square lag, with centers `1` and `-1`. -/
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]} {α : ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hrec : ∀ n : Nat,
      P (n + 2) = A n * P (n + 1) + (-((X - C α : ℝ[X]) ^ 2)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_lw_negative_square_sequence_realrooted_unit using
    base := hbase,
    pos_lc := hpos,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Denominator-normalized negative-square lag with an explicit scalar
coefficient certificate. -/
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
  rr_lw_negative_square_sequence_den_coeff using
    base := hbase,
    pos_lc := hpos,
    coeff := fun _ => (1 : ℝ),
    coeff_nonneg := rr_lw_coeff_nonneg_seq_term,
    raw_recurrence := hraw,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Split-form denominator-normalized negative-square lag. -/
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
  rr_lw_negative_square_sequence_den_coeff_split using
    base := hbase,
    pos_lc := hpos,
    square_factor := q,
    coeff := fun _ => (1 : ℝ),
    raw_coeff := fun n => (n : ℝ) + 1,
    den := fun n => (n : ℝ) + 1,
    coeff_nonneg := rr_lw_coeff_nonneg_seq_term,
    raw_recurrence := hraw,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Denominator-normalized negative-square lag with automatic scalar
side-goals. -/
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
  rr_lw_negative_square_sequence_den_coeff_auto using
    base := hbase,
    pos_lc := hpos,
    coeff := fun _ => (1 : ℝ),
    raw_recurrence := hraw,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Split-form denominator-normalized negative-square lag with automatic
scalar side-goals. -/
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
  rr_lw_negative_square_sequence_den_coeff_auto_split using
    base := hbase,
    pos_lc := hpos,
    square_factor := q,
    coeff := fun _ => (1 : ℝ),
    raw_coeff := fun n => (n : ℝ) + 1,
    den := fun n => (n : ℝ) + 1,
    raw_recurrence := hraw,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Real-rootedness endpoint for the denominator-normalized negative-square
lag. -/
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
  rr_lw_negative_square_sequence_den_coeff_realrooted using
    base := hbase,
    pos_lc := hpos,
    coeff := fun _ => (1 : ℝ),
    coeff_nonneg := rr_lw_coeff_nonneg_seq_term,
    raw_recurrence := hraw,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Split-form real-rootedness endpoint for the denominator-normalized
negative-square lag. -/
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
  rr_lw_negative_square_sequence_den_coeff_realrooted_split using
    base := hbase,
    pos_lc := hpos,
    square_factor := q,
    coeff := fun _ => (1 : ℝ),
    raw_coeff := fun n => (n : ℝ) + 1,
    den := fun n => (n : ℝ) + 1,
    coeff_nonneg := rr_lw_coeff_nonneg_seq_term,
    raw_recurrence := hraw,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Real-rootedness endpoint for the denominator-normalized negative-square
lag with automatic scalar side-goals. -/
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
  rr_lw_negative_square_sequence_den_coeff_realrooted_auto using
    base := hbase,
    pos_lc := hpos,
    coeff := fun _ => (1 : ℝ),
    raw_recurrence := hraw,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Split-form real-rootedness endpoint for the denominator-normalized
negative-square lag with automatic scalar side-goals. -/
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
  rr_lw_negative_square_sequence_den_coeff_realrooted_auto_split using
    base := hbase,
    pos_lc := hpos,
    square_factor := q,
    coeff := fun _ => (1 : ℝ),
    raw_coeff := fun n => (n : ℝ) + 1,
    den := fun n => (n : ℝ) + 1,
    raw_recurrence := hraw,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- `A181738`-style sequence shell: negative-definite monic quadratic lag. -/
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hrec : ∀ n : Nat,
      P (n + 2) =
        A n * P (n + 1) + (-(X ^ 2 + C (2 : ℝ) * X + C (4 : ℝ))) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_lw_negative_monic_quadratic_sequence using
    base := hbase,
    pos_lc := hpos,
    discriminant := rr_lw_quadratic_discriminant,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- The same negative-definite quadratic sequence shell closes all rows. -/
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hrec : ∀ n : Nat,
      P (n + 2) =
        A n * P (n + 1) + (-(X ^ 2 + C (2 : ℝ) * X + C (4 : ℝ))) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_lw_negative_monic_quadratic_sequence_realrooted using
    base := hbase,
    pos_lc := hpos,
    discriminant := rr_lw_quadratic_discriminant,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- The same negative-definite quadratic shell with automatic discriminant
discharge. -/
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hrec : ∀ n : Nat,
      P (n + 2) =
        A n * P (n + 1) + (-(X ^ 2 + C (2 : ℝ) * X + C (4 : ℝ))) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_lw_negative_monic_quadratic_sequence_auto using
    base := hbase,
    pos_lc := hpos,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Automatic discriminant discharge, real-rootedness endpoint. -/
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hrec : ∀ n : Nat,
      P (n + 2) =
        A n * P (n + 1) + (-(X ^ 2 + C (2 : ℝ) * X + C (4 : ℝ))) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_lw_negative_monic_quadratic_sequence_realrooted_auto using
    base := hbase,
    pos_lc := hpos,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- `A001607`-style sequence shell: non-monic negative-definite quadratic
lag `-(2t^2-t+1)`. -/
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
  rr_lw_negative_quadratic_sequence using
    base := hbase,
    pos_lc := hpos,
    leading_nonneg := rr_lw_coeff_nonneg_seq_term,
    constant_nonneg := rr_lw_coeff_nonneg_seq_term,
    discriminant := rr_lw_quadratic_discriminant,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Real-rootedness endpoint for the explicit non-monic negative quadratic
shell. -/
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hrec : ∀ n : Nat,
      P (n + 2) =
        A n * P (n + 1) +
          (-(C (2 : ℝ) * X ^ 2 + C (-1 : ℝ) * X + C (1 : ℝ))) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_lw_negative_quadratic_sequence_realrooted using
    base := hbase,
    pos_lc := hpos,
    leading_nonneg := rr_lw_coeff_nonneg_seq_term,
    constant_nonneg := rr_lw_coeff_nonneg_seq_term,
    discriminant := rr_lw_quadratic_discriminant,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- The same non-monic negative quadratic shell with automatic side-goal
discharge. -/
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
  rr_lw_negative_quadratic_sequence_auto using
    base := hbase,
    pos_lc := hpos,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Real-rootedness endpoint for the same non-monic negative quadratic shell. -/
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hrec : ∀ n : Nat,
      P (n + 2) =
        A n * P (n + 1) +
          (-(C (2 : ℝ) * X ^ 2 + C (-1 : ℝ) * X + C (1 : ℝ))) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_lw_negative_quadratic_sequence_realrooted_auto using
    base := hbase,
    pos_lc := hpos,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- `A010892`-style sequence shell: repeated lag `-(t^2+t+1)`. -/
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hrec : ∀ n : Nat,
      P (n + 2) =
        A n * P (n + 1) +
          (-(C (1 : ℝ) * X ^ 2 + C (1 : ℝ) * X + C (1 : ℝ))) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_lw_negative_quadratic_sequence_auto using
    base := hbase,
    pos_lc := hpos,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- `A049347`-style sequence shell: repeated lag `-(t^2-t+1)`. -/
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hrec : ∀ n : Nat,
      P (n + 2) =
        A n * P (n + 1) +
          (-(C (1 : ℝ) * X ^ 2 + C (-1 : ℝ) * X + C (1 : ℝ))) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_lw_negative_quadratic_sequence_realrooted_auto using
    base := hbase,
    pos_lc := hpos,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- `A078020`-style sequence shell: repeated lag `-(2t^2+t+1)`. -/
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hrec : ∀ n : Nat,
      P (n + 2) =
        A n * P (n + 1) +
          (-(C (2 : ℝ) * X ^ 2 + C (1 : ℝ) * X + C (1 : ℝ))) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_lw_negative_quadratic_sequence_auto using
    base := hbase,
    pos_lc := hpos,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Active-leading-coefficient smoke test for repeated
`-(k t^2+t+1)` families. -/
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hrec : ∀ n : Nat,
      P (n + 2) =
        A n * P (n + 1) +
          (-(C ((n : ℝ) + 1) * X ^ 2 + C (1 : ℝ) * X + C (1 : ℝ))) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_lw_negative_quadratic_sequence_realrooted_auto using
    base := hbase,
    pos_lc := hpos,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Denominator-normalized raw quadratic smoke test.

The raw recurrence has a left factor `n+1` and raw lag coefficients
`(n+1) * (-(2t^2-t+1))`; after scalar cancellation the usual non-monic
quadratic discriminant certificate applies. -/
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
  rr_lw_negative_quadratic_sequence_den_coeff_realrooted_auto_split using
    base := hbase,
    pos_lc := hpos,
    leading := fun _ => (2 : ℝ),
    linear := fun _ => (-1 : ℝ),
    constant := fun _ => (1 : ℝ),
    raw_leading := fun n => 2 * ((n : ℝ) + 1),
    raw_linear := fun n => -((n : ℝ) + 1),
    raw_constant := fun n => (n : ℝ) + 1,
    den := fun n => (n : ℝ) + 1,
    raw_recurrence := hraw,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Denominator-normalized raw quadratic smoke test, explicit endpoint. -/
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
  rr_lw_negative_quadratic_sequence_den_coeff_split using
    base := hbase,
    pos_lc := hpos,
    leading := fun _ => (2 : ℝ),
    linear := fun _ => (-1 : ℝ),
    constant := fun _ => (1 : ℝ),
    raw_leading := fun n => 2 * ((n : ℝ) + 1),
    raw_linear := fun n => -((n : ℝ) + 1),
    raw_constant := fun n => (n : ℝ) + 1,
    den := fun n => (n : ℝ) + 1,
    leading_nonneg := rr_lw_coeff_nonneg_seq_term,
    constant_nonneg := rr_lw_coeff_nonneg_seq_term,
    discriminant := rr_lw_quadratic_discriminant,
    raw_recurrence := hraw,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Denominator-normalized raw quadratic smoke test, automatic side-goals. -/
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
  rr_lw_negative_quadratic_sequence_den_coeff_auto_split using
    base := hbase,
    pos_lc := hpos,
    leading := fun _ => (2 : ℝ),
    linear := fun _ => (-1 : ℝ),
    constant := fun _ => (1 : ℝ),
    raw_leading := fun n => 2 * ((n : ℝ) + 1),
    raw_linear := fun n => -((n : ℝ) + 1),
    raw_constant := fun n => (n : ℝ) + 1,
    den := fun n => (n : ℝ) + 1,
    raw_recurrence := hraw,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Denominator-normalized raw quadratic smoke test, explicit
real-rootedness endpoint. -/
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
  rr_lw_negative_quadratic_sequence_den_coeff_realrooted_split using
    base := hbase,
    pos_lc := hpos,
    leading := fun _ => (2 : ℝ),
    linear := fun _ => (-1 : ℝ),
    constant := fun _ => (1 : ℝ),
    raw_leading := fun n => 2 * ((n : ℝ) + 1),
    raw_linear := fun n => -((n : ℝ) + 1),
    raw_constant := fun n => (n : ℝ) + 1,
    den := fun n => (n : ℝ) + 1,
    leading_nonneg := rr_lw_coeff_nonneg_seq_term,
    constant_nonneg := rr_lw_coeff_nonneg_seq_term,
    discriminant := rr_lw_quadratic_discriminant,
    raw_recurrence := hraw,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- OEIS-style active-range check: after the active index threshold, a fitted
coefficient `c_n - 2` gives the nonnegative positive-`t` lag. -/
example {f g : ℝ[X]} {c : ℝ}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hf_roots : ∀ r, f.IsRoot r → r ≤ 0)
    (hactive : (2 : ℝ) ≤ c)
    (hF_pos : HasPosLeadingCoeff ((1 + X : ℝ[X]) * f + (C (c - 2) * X) * g))
    (hdeg_lo :
      f.natDegree ≤ ((1 + X : ℝ[X]) * f + (C (c - 2) * X) * g).natDegree)
    (hdeg_hi :
      ((1 + X : ℝ[X]) * f + (C (c - 2) * X) * g).natDegree ≤
        f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    Prec f ((1 + X : ℝ[X]) * f + (C (c - 2) * X) * g) := by
  rr_lw_positive_t_auto using
    interlacer := hgf,
    interlacer_pos_lc := hg_pos,
    roots_nonpos := hf_roots,
    target_pos_lc := hF_pos,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi,
    no_common_roots := hno

/-- Active-range same-degree branch: a negative constant lag gives a plateau
step when the degree certificate says no new degree appears. -/
example {f g : ℝ[X]} {c : ℝ}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hactive : (2 : ℝ) < c)
    (hF_pos : HasPosLeadingCoeff ((1 + X : ℝ[X]) * f + C (2 - c) * g))
    (hdeg : (((1 + X : ℝ[X]) * f + C (2 - c) * g).natDegree = f.natDegree))
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    Prec f ((1 + X : ℝ[X]) * f + C (2 - c) * g) := by
  have hb_neg : ∀ r, f.IsRoot r → (C (2 - c) : ℝ[X]).eval r < 0 := by
    intro r _hr
    simpa using sub_neg.mpr hactive
  rr_liu_wang_two_strict_same using
    interlacer := hgf,
    interlacer_pos_lc := hg_pos,
    target_pos_lc := hF_pos,
    degree := hdeg,
    no_common_roots := hno,
    head_neg := hb_neg

/-- Active-range successor-degree branch: the same sign certificate dispatches
to the degree-increase Liu--Wang wrapper when the degree certificate says so. -/
example {f g : ℝ[X]} {c : ℝ}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hactive : (2 : ℝ) < c)
    (hF_pos : HasPosLeadingCoeff ((1 + X : ℝ[X]) * f + C (2 - c) * g))
    (hdeg :
      (((1 + X : ℝ[X]) * f + C (2 - c) * g).natDegree = f.natDegree + 1))
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    Prec f ((1 + X : ℝ[X]) * f + C (2 - c) * g) := by
  have hb_neg : ∀ r, f.IsRoot r → (C (2 - c) : ℝ[X]).eval r < 0 := by
    intro r _hr
    simpa using sub_neg.mpr hactive
  rr_liu_wang_two_strict_succ using
    interlacer := hgf,
    interlacer_pos_lc := hg_pos,
    target_pos_lc := hF_pos,
    degree := hdeg,
    no_common_roots := hno,
    head_neg := hb_neg

/-- The same active-range plateau/successor choice can be kept as a single
degree branch until the tactic dispatches to the matching Liu--Wang theorem. -/
example {f g : ℝ[X]} {c : ℝ}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hactive : (2 : ℝ) < c)
    (hF_pos : HasPosLeadingCoeff ((1 + X : ℝ[X]) * f + C (2 - c) * g))
    (hdegree :
      (((1 + X : ℝ[X]) * f + C (2 - c) * g).natDegree = f.natDegree) ∨
        (((1 + X : ℝ[X]) * f + C (2 - c) * g).natDegree = f.natDegree + 1))
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    Prec f ((1 + X : ℝ[X]) * f + C (2 - c) * g) := by
  have hb_neg : ∀ r, f.IsRoot r → (C (2 - c) : ℝ[X]).eval r < 0 := by
    intro r _hr
    simpa using sub_neg.mpr hactive
  rr_liu_wang_two_strict_branch using
    interlacer := hgf,
    interlacer_pos_lc := hg_pos,
    target_pos_lc := hF_pos,
    degree_branch := hdegree,
    no_common_roots := hno,
    head_neg := hb_neg

/-- Plateau sequence skeleton combining the branch induction shell with the
strict Liu--Wang same/successor degree dispatcher.

The remaining sequence-specific input is `hinter`: for a concrete plateau
family, this is where one proves that the previous `Prec` certificate gives
the interlacer needed by the strict Liu--Wang step. -/
example {P : Nat → ℝ[X]} {A B : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hrec : ∀ n : Nat, P (n + 2) = A n * P (n + 1) + B n * P n)
    (hdegree : ∀ n : Nat,
      (P (n + 2)).natDegree = (P (n + 1)).natDegree ∨
        (P (n + 2)).natDegree = (P (n + 1)).natDegree + 1)
    (hinter : ∀ n : Nat,
      Prec (P n) (P (n + 1)) → Interlaces (P n) (P (n + 1)))
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r)
    (hb_neg : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → (B n).eval r < 0) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  let hsame : ∀ n : Nat,
      (P (n + 2)).natDegree = (P (n + 1)).natDegree →
      Prec (P n) (P (n + 1)) → Prec (P (n + 1)) (P (n + 2)) := by
    intro n hdeg hprev
    have htarget_pos :
        HasPosLeadingCoeff (A n * P (n + 1) + B n * P n) := by
      simpa [← hrec n] using hpos (n + 2)
    have hbranch :
        (A n * P (n + 1) + B n * P n).natDegree =
            (P (n + 1)).natDegree ∨
          (A n * P (n + 1) + B n * P n).natDegree =
            (P (n + 1)).natDegree + 1 := by
      left
      simpa [← hrec n] using hdeg
    have hstep :
        Prec (P (n + 1)) (A n * P (n + 1) + B n * P n) := by
      rr_liu_wang_two_strict_branch using
        interlacer := hinter n hprev,
        interlacer_pos_lc := hpos n,
        target_pos_lc := htarget_pos,
        degree_branch := hbranch,
        no_common_roots := hno n,
        head_neg := hb_neg n
    simpa [← hrec n] using hstep
  let hsucc : ∀ n : Nat,
      (P (n + 2)).natDegree = (P (n + 1)).natDegree + 1 →
      Prec (P n) (P (n + 1)) → Prec (P (n + 1)) (P (n + 2)) := by
    intro n hdeg hprev
    have htarget_pos :
        HasPosLeadingCoeff (A n * P (n + 1) + B n * P n) := by
      simpa [← hrec n] using hpos (n + 2)
    have hbranch :
        (A n * P (n + 1) + B n * P n).natDegree =
            (P (n + 1)).natDegree ∨
          (A n * P (n + 1) + B n * P n).natDegree =
            (P (n + 1)).natDegree + 1 := by
      right
      simpa [← hrec n] using hdeg
    have hstep :
        Prec (P (n + 1)) (A n * P (n + 1) + B n * P n) := by
      rr_liu_wang_two_strict_branch using
        interlacer := hinter n hprev,
        interlacer_pos_lc := hpos n,
        target_pos_lc := htarget_pos,
        degree_branch := hbranch,
        no_common_roots := hno n,
        head_neg := hb_neg n
    simpa [← hrec n] using hstep
  rr_prec_sequence_branches using
    base := hbase,
    degree_branch := hdegree,
    same := hsame,
    successor := hsucc

/-- OEIS shapes `A154227`/`A154228`/`A249248`, using nonnegative coefficients
to infer the half-line root certificate for a positive `t` lag. -/
example {f g : ℝ[X]} {c : ℝ}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hf_nonneg : HasNonnegCoeffs f)
    (hc : 0 ≤ c)
    (hF_pos : HasPosLeadingCoeff ((1 + X : ℝ[X]) * f + (C c * X) * g))
    (hdeg_lo : f.natDegree ≤ ((1 + X : ℝ[X]) * f + (C c * X) * g).natDegree)
    (hdeg_hi : ((1 + X : ℝ[X]) * f + (C c * X) * g).natDegree ≤
      f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    Prec f ((1 + X : ℝ[X]) * f + (C c * X) * g) := by
  rr_lw_positive_t_nonneg_auto using
    interlacer := hgf,
    interlacer_pos_lc := hg_pos,
    nonneg_coeffs := hf_nonneg,
    target_pos_lc := hF_pos,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi,
    no_common_roots := hno

/-- Favard-like negative constant lag, available as a direct Liu--Wang
sign-test path when the adjacent interlacing invariant is already known. -/
example {f g : ℝ[X]} {α c : ℝ}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hc : 0 ≤ c)
    (hF_pos : HasPosLeadingCoeff ((X - C α) * f + (-(C c)) * g))
    (hdeg_lo : f.natDegree ≤ ((X - C α) * f + (-(C c)) * g).natDegree)
    (hdeg_hi : ((X - C α) * f + (-(C c)) * g).natDegree ≤ f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    Prec f ((X - C α) * f + (-(C c)) * g) := by
  rr_lw_negative_const using
    interlacer := hgf,
    interlacer_pos_lc := hg_pos,
    coeff_nonneg := hc,
    target_pos_lc := hF_pos,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi,
    no_common_roots := hno

/-- Favard-like negative constant lag with automatic constant nonnegativity. -/
example {f g : ℝ[X]} {α : ℝ}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hF_pos : HasPosLeadingCoeff ((X - C α) * f + (-(C (1 : ℝ))) * g))
    (hdeg_lo :
      f.natDegree ≤ ((X - C α) * f + (-(C (1 : ℝ))) * g).natDegree)
    (hdeg_hi :
      ((X - C α) * f + (-(C (1 : ℝ))) * g).natDegree ≤ f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    Prec f ((X - C α) * f + (-(C (1 : ℝ))) * g) := by
  rr_lw_negative_const_auto using
    interlacer := hgf,
    interlacer_pos_lc := hg_pos,
    target_pos_lc := hF_pos,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi,
    no_common_roots := hno

/-- Normalized negative constant lag with automatic constant nonnegativity. -/
example {f g : ℝ[X]} {α : ℝ}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hF_pos : HasPosLeadingCoeff ((X - C α) * f + C (-1 : ℝ) * g))
    (hdeg_lo : f.natDegree ≤ ((X - C α) * f + C (-1 : ℝ) * g).natDegree)
    (hdeg_hi : ((X - C α) * f + C (-1 : ℝ) * g).natDegree ≤ f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    Prec f ((X - C α) * f + C (-1 : ℝ) * g) := by
  rr_lw_negative_const_C_neg_auto using
    interlacer := hgf,
    interlacer_pos_lc := hg_pos,
    target_pos_lc := hF_pos,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi,
    no_common_roots := hno

/-- Family G quadratic lag: `B(t) = -c(t-α)^2`, a globally nonpositive lag. -/
example {f g a : ℝ[X]} {α c : ℝ}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hc : 0 ≤ c)
    (hF_pos : HasPosLeadingCoeff (a * f + (-(C c) * (X - C α) ^ 2) * g))
    (hdeg_lo : f.natDegree ≤ (a * f + (-(C c) * (X - C α) ^ 2) * g).natDegree)
    (hdeg_hi :
      (a * f + (-(C c) * (X - C α) ^ 2) * g).natDegree ≤ f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    Prec f (a * f + (-(C c) * (X - C α) ^ 2) * g) := by
  rr_lw_negative_square using
    interlacer := hgf,
    interlacer_pos_lc := hg_pos,
    coeff_nonneg := hc,
    target_pos_lc := hF_pos,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi,
    no_common_roots := hno

/-- Family G unit negative-square lag with automatic coefficient
nonnegativity. -/
example {f g a : ℝ[X]} {α : ℝ}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hF_pos : HasPosLeadingCoeff (a * f + (-(C (1 : ℝ)) * (X - C α) ^ 2) * g))
    (hdeg_lo :
      f.natDegree ≤ (a * f + (-(C (1 : ℝ)) * (X - C α) ^ 2) * g).natDegree)
    (hdeg_hi :
      (a * f + (-(C (1 : ℝ)) * (X - C α) ^ 2) * g).natDegree ≤
        f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    Prec f (a * f + (-(C (1 : ℝ)) * (X - C α) ^ 2) * g) := by
  rr_lw_negative_square_auto using
    interlacer := hgf,
    interlacer_pos_lc := hg_pos,
    target_pos_lc := hF_pos,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi,
    no_common_roots := hno

/-- OEIS shape `A181738`: a negative-definite monic quadratic lag can be
certified directly by the discriminant inequality, without exposing a square. -/
example {f g a : ℝ[X]}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hF_pos :
      HasPosLeadingCoeff (a * f + (-(X ^ 2 + C (2 : ℝ) * X + C (4 : ℝ))) * g))
    (hdeg_lo :
      f.natDegree ≤ (a * f + (-(X ^ 2 + C (2 : ℝ) * X + C (4 : ℝ))) * g).natDegree)
    (hdeg_hi :
      (a * f + (-(X ^ 2 + C (2 : ℝ) * X + C (4 : ℝ))) * g).natDegree ≤
        f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    Prec f (a * f + (-(X ^ 2 + C (2 : ℝ) * X + C (4 : ℝ))) * g) := by
  rr_lw_negative_monic_quadratic using
    interlacer := hgf,
    interlacer_pos_lc := hg_pos,
    discriminant := rr_lw_coeff_nonneg_term,
    target_pos_lc := hF_pos,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi,
    no_common_roots := hno

/-- OEIS shape `A181738`: automatic discriminant discharge for a monic
quadratic lag. -/
example {f g a : ℝ[X]}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hF_pos :
      HasPosLeadingCoeff (a * f + (-(X ^ 2 + C (2 : ℝ) * X + C (4 : ℝ))) * g))
    (hdeg_lo :
      f.natDegree ≤ (a * f + (-(X ^ 2 + C (2 : ℝ) * X + C (4 : ℝ))) * g).natDegree)
    (hdeg_hi :
      (a * f + (-(X ^ 2 + C (2 : ℝ) * X + C (4 : ℝ))) * g).natDegree ≤
        f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    Prec f (a * f + (-(X ^ 2 + C (2 : ℝ) * X + C (4 : ℝ))) * g) := by
  rr_lw_negative_monic_quadratic_auto using
    interlacer := hgf,
    interlacer_pos_lc := hg_pos,
    target_pos_lc := hF_pos,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi,
    no_common_roots := hno

/-- One-step non-monic negative quadratic lag, with explicit scalar
certificates. -/
example {f g a : ℝ[X]}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hF_pos :
      HasPosLeadingCoeff
        (a * f + (-(C (2 : ℝ) * X ^ 2 + C (-1 : ℝ) * X + C (1 : ℝ))) * g))
    (hdeg_lo :
      f.natDegree ≤
        (a * f + (-(C (2 : ℝ) * X ^ 2 + C (-1 : ℝ) * X + C (1 : ℝ))) * g).natDegree)
    (hdeg_hi :
      (a * f + (-(C (2 : ℝ) * X ^ 2 + C (-1 : ℝ) * X + C (1 : ℝ))) * g).natDegree ≤
        f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    Prec f (a * f + (-(C (2 : ℝ) * X ^ 2 + C (-1 : ℝ) * X + C (1 : ℝ))) * g) := by
  rr_lw_negative_quadratic using
    interlacer := hgf,
    interlacer_pos_lc := hg_pos,
    leading_nonneg := rr_lw_coeff_nonneg_term,
    constant_nonneg := rr_lw_coeff_nonneg_term,
    discriminant := rr_lw_coeff_nonneg_term,
    target_pos_lc := hF_pos,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi,
    no_common_roots := hno

/-- One-step non-monic negative quadratic lag, with automatic scalar
certificates. -/
example {f g a : ℝ[X]}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hF_pos :
      HasPosLeadingCoeff
        (a * f + (-(C (2 : ℝ) * X ^ 2 + C (-1 : ℝ) * X + C (1 : ℝ))) * g))
    (hdeg_lo :
      f.natDegree ≤
        (a * f + (-(C (2 : ℝ) * X ^ 2 + C (-1 : ℝ) * X + C (1 : ℝ))) * g).natDegree)
    (hdeg_hi :
      (a * f + (-(C (2 : ℝ) * X ^ 2 + C (-1 : ℝ) * X + C (1 : ℝ))) * g).natDegree ≤
        f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    Prec f (a * f + (-(C (2 : ℝ) * X ^ 2 + C (-1 : ℝ) * X + C (1 : ℝ))) * g) := by
  rr_lw_negative_quadratic_auto using
    interlacer := hgf,
    interlacer_pos_lc := hg_pos,
    target_pos_lc := hF_pos,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi,
    no_common_roots := hno

/-- One-step Family E3 product lag: `t Q(t)` reduces to a focused
`Q(r) >= 0` certificate at current-row roots. -/
example {f g a q : ℝ[X]}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hf_roots : ∀ r, f.IsRoot r → r ≤ 0)
    (hQ : ∀ r, f.IsRoot r → 0 ≤ q.eval r)
    (hF_pos : HasPosLeadingCoeff (a * f + (X * q) * g))
    (hdeg_lo : f.natDegree ≤ (a * f + (X * q) * g).natDegree)
    (hdeg_hi : (a * f + (X * q) * g).natDegree ≤ f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    Prec f (a * f + (X * q) * g) := by
  rr_lw_positive_X_mul using
    interlacer := hgf,
    interlacer_pos_lc := hg_pos,
    roots_nonpos := hf_roots,
    factor_nonneg := hQ,
    target_pos_lc := hF_pos,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi,
    no_common_roots := hno

/-- One-step product lag with the root half-line supplied by nonnegative
coefficients. -/
example {f g a q : ℝ[X]}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hf_nonneg : HasNonnegCoeffs f)
    (hQ : ∀ r, f.IsRoot r → 0 ≤ q.eval r)
    (hF_pos : HasPosLeadingCoeff (a * f + (X * q) * g))
    (hdeg_lo : f.natDegree ≤ (a * f + (X * q) * g).natDegree)
    (hdeg_hi : (a * f + (X * q) * g).natDegree ≤ f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    Prec f (a * f + (X * q) * g) := by
  rr_lw_positive_X_mul_nonneg using
    interlacer := hgf,
    interlacer_pos_lc := hg_pos,
    nonneg_coeffs := hf_nonneg,
    factor_nonneg := hQ,
    target_pos_lc := hF_pos,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi,
    no_common_roots := hno

/-- One-step scalar product lag with explicit scalar nonnegativity. -/
example {f g a q : ℝ[X]} {c : ℝ}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hf_nonneg : HasNonnegCoeffs f)
    (hc : 0 ≤ c)
    (hQ : ∀ r, f.IsRoot r → 0 ≤ q.eval r)
    (hF_pos : HasPosLeadingCoeff (a * f + (C c * X * q) * g))
    (hdeg_lo : f.natDegree ≤ (a * f + (C c * X * q) * g).natDegree)
    (hdeg_hi : (a * f + (C c * X * q) * g).natDegree ≤ f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    Prec f (a * f + (C c * X * q) * g) := by
  rr_lw_positive_C_mul_X_mul_nonneg using
    interlacer := hgf,
    interlacer_pos_lc := hg_pos,
    nonneg_coeffs := hf_nonneg,
    coeff_nonneg := hc,
    factor_nonneg := hQ,
    target_pos_lc := hF_pos,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi,
    no_common_roots := hno

/-- One-step scalar product lag, deriving the half-line root bound from
nonnegative coefficients and closing the scalar side goal automatically. -/
example {f g a q : ℝ[X]}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hf_nonneg : HasNonnegCoeffs f)
    (hQ : ∀ r, f.IsRoot r → 0 ≤ q.eval r)
    (hF_pos : HasPosLeadingCoeff (a * f + (C (2 : ℝ) * X * q) * g))
    (hdeg_lo : f.natDegree ≤ (a * f + (C (2 : ℝ) * X * q) * g).natDegree)
    (hdeg_hi :
      (a * f + (C (2 : ℝ) * X * q) * g).natDegree ≤ f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    Prec f (a * f + (C (2 : ℝ) * X * q) * g) := by
  rr_lw_positive_C_mul_X_mul_nonneg_auto using
    interlacer := hgf,
    interlacer_pos_lc := hg_pos,
    nonneg_coeffs := hf_nonneg,
    factor_nonneg := hQ,
    target_pos_lc := hF_pos,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi,
    no_common_roots := hno

/-- Family E3 product-lag sequence shell: once the concrete recurrence supplies
`Q_n(r) >= 0` at current-row roots, the tactic handles the `t Q_n(t)` sign
test and the Liu--Wang induction. -/
example {P : Nat → ℝ[X]} {A Q : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hQ : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → 0 ≤ (Q n).eval r)
    (hrec : ∀ n : Nat, P (n + 2) = A n * P (n + 1) + (X * Q n) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_lw_positive_X_mul_sequence using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    factor_nonneg := hQ,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- The product-lag sequence tactic accepts the natural associated form
`X * (Q_n * P_n)` by associativity, avoiding local rewrite blocks. -/
example {P : Nat → ℝ[X]} {A Q : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hQ : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → 0 ≤ (Q n).eval r)
    (hrec : ∀ n : Nat, P (n + 2) = A n * P (n + 1) + X * (Q n * P n))
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_lw_positive_X_mul_sequence using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    factor_nonneg := hQ,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- The same `t Q_n(t)` sequence shell closes real-rootedness of every row. -/
example {P : Nat → ℝ[X]} {A Q : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hQ : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → 0 ≤ (Q n).eval r)
    (hrec : ∀ n : Nat, P (n + 2) = A n * P (n + 1) + (X * Q n) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_lw_positive_X_mul_sequence_realrooted using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    factor_nonneg := hQ,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Projection endpoint for the `t Q_n(t)` shell; this also checks the
associativity fallback branch. -/
example {P : Nat → ℝ[X]} {A Q : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hQ : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → 0 ≤ (Q n).eval r)
    (hrec : ∀ n : Nat, P (n + 2) = A n * P (n + 1) + (X * Q n) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, (P n).Splits := by
  rr_lw_positive_X_mul_sequence_realrooted using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    factor_nonneg := hQ,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- The explicit scalar product-lag real-rootedness endpoint also accepts
`c_n X (Q_n P_n)` by associativity.  Use the explicit coefficient certificate
for this parenthesized scalar form. -/
example {P : Nat → ℝ[X]} {A Q : Nat → ℝ[X]} {c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hQ : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → 0 ≤ (Q n).eval r)
    (hrec : ∀ n : Nat,
      P (n + 2) = A n * P (n + 1) + C (c n) * (X * (Q n * P n)))
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_lw_positive_C_mul_X_mul_sequence_realrooted using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    coeff_nonneg := hc,
    factor_nonneg := hQ,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- The explicit scalar product-lag sequence endpoint uses a supplied
coefficient certificate. -/
example {P : Nat → ℝ[X]} {A Q : Nat → ℝ[X]} {c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hQ : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → 0 ≤ (Q n).eval r)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        A n * P (n + 1) + (C (c n) * X * Q n) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_lw_positive_C_mul_X_mul_sequence using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    coeff_nonneg := hc,
    factor_nonneg := hQ,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Scalar product-lag sequence shell with automatic nonnegativity of the
scalar coefficient. -/
example {P : Nat → ℝ[X]} {A Q : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hQ : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → 0 ≤ (Q n).eval r)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        A n * P (n + 1) + (C ((n : ℝ) + 1) * X * Q n) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_lw_positive_C_mul_X_mul_sequence_auto using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    factor_nonneg := hQ,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- The automatic scalar product-lag shell also accepts the associated form
`c_n X (Q_n P_n)` when `positivity` can prove `0 <= c_n`. -/
example {P : Nat → ℝ[X]} {A Q : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hQ : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → 0 ≤ (Q n).eval r)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        A n * P (n + 1) + C ((n : ℝ) + 1) * (X * (Q n * P n)))
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_lw_positive_C_mul_X_mul_sequence_auto using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    factor_nonneg := hQ,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Real-rootedness endpoint for the same associated scalar product-lag form. -/
example {P : Nat → ℝ[X]} {A Q : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hQ : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → 0 ≤ (Q n).eval r)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        A n * P (n + 1) + C ((n : ℝ) + 1) * (X * (Q n * P n)))
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_lw_positive_C_mul_X_mul_sequence_realrooted_auto using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    factor_nonneg := hQ,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- A window-certified product lag: if current-row roots lie in `[-1, 0]`,
then `Q(t)=1+t` is nonnegative at those roots and the scalar product-lag
tactic applies. -/
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hroot_lower : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → -1 ≤ r)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        A n * P (n + 1) + (C ((n : ℝ) + 1) * X * (1 + X : ℝ[X])) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  have hQ : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r →
      0 ≤ ((1 + X : ℝ[X]).eval r) := by
    intro n r hr
    have hlo : -1 ≤ r := hroot_lower n r hr
    rr_eval_simp_arith
  rr_lw_positive_C_mul_X_mul_sequence_realrooted_auto using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    factor_nonneg := hQ,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Family E strict-degree `t R_n(t)` spelling.  This is the named surface for
the largest clean three-term Liu--Wang bucket. -/
example {P : Nat → ℝ[X]} {A R : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hR : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → 0 ≤ (R n).eval r)
    (hrec : ∀ n : Nat, P (n + 2) = A n * P (n + 1) + (X * R n) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_lw_tR_lag_sequence using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    factor_nonneg := hR,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Real-rootedness endpoint for the same `t R_n(t)` Family E shell. -/
example {P : Nat → ℝ[X]} {A R : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hR : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → 0 ≤ (R n).eval r)
    (hrec : ∀ n : Nat, P (n + 2) = A n * P (n + 1) + (X * R n) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_lw_tR_lag_sequence_realrooted using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    factor_nonneg := hR,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Projection endpoint for the named `t R_n(t)` router, using the associated
recurrence shape produced by some promoted product-lag rows. -/
example {P : Nat → ℝ[X]} {A R : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hR : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → 0 ≤ (R n).eval r)
    (hrec : ∀ n : Nat, P (n + 2) = A n * P (n + 1) + X * (R n * P n))
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, (P n).Splits := by
  rr_lw_tR_lag_sequence_realrooted using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    factor_nonneg := hR,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Explicit active-coefficient `c_n t R_n(t)` shell with a supplied
coefficient certificate. -/
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
  rr_lw_c_tR_lag_sequence using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    coeff_nonneg := hc,
    factor_nonneg := hR,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Real-rootedness endpoint for the explicit `c_n t R_n(t)` alias. -/
example {P : Nat → ℝ[X]} {A R : Nat → ℝ[X]} {c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hR : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → 0 ≤ (R n).eval r)
    (hrec : ∀ n : Nat,
      P (n + 2) = A n * P (n + 1) + C (c n) * (X * (R n * P n)))
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_lw_c_tR_lag_sequence_realrooted using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    coeff_nonneg := hc,
    factor_nonneg := hR,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Scalar active-coefficient form `c_n t R_n(t)` with the coefficient
nonnegativity closed by the active-index helper. -/
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
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_lw_c_tR_lag_sequence_auto using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    factor_nonneg := hR,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Real-rootedness endpoint for active-coefficient `c_n t R_n(t)` recurrences. -/
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
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_lw_c_tR_lag_sequence_realrooted_auto using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    factor_nonneg := hR,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Projection endpoint for the active-coefficient `c_n t R_n(t)` router,
again in the associated product-lag form. -/
example {P : Nat → ℝ[X]} {A R : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hR : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → 0 ≤ (R n).eval r)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        A n * P (n + 1) + C ((n : ℝ) + 1) * (X * (R n * P n)))
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, (P n).Splits := by
  rr_lw_c_tR_lag_sequence_realrooted_auto using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    factor_nonneg := hR,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

section InferredSequenceCertificates

variable {P A B R Q : Nat → ℝ[X]}
variable (hbase : Prec (P 0) (P 1))
variable (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
variable (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
variable (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r)

variable (hB : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → (B n).eval r ≤ 0)
variable (hrecB : ∀ n : Nat, P (n + 2) = A n * P (n + 1) + B n * P n)

/-- A supplied recurrence fixes both hidden coefficient families before lookup. -/
example : ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_lw_nonpos_lag_sequence using recurrence := hrecB

/-- The inferred nonpositive-lag shell returns its full real-rooted endpoint. -/
example : ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_lw_nonpos_lag_sequence_realrooted using recurrence := hrecB

/-- The inferred nonpositive-lag shell supports the splitting projection. -/
example : ∀ n : Nat, (P n).Splits := by
  rr_lw_nonpos_lag_sequence_realrooted using recurrence := hrecB

/-- The inferred nonpositive-lag shell supports the nonzero projection. -/
example : ∀ n : Nat, P n ≠ 0 := by rr_lw_nonpos_lag_sequence_realrooted using recurrence := hrecB

/-- The inferred nonpositive-lag shell supports an indexed splitting projection. -/
example : (P 3).Splits := by rr_lw_nonpos_lag_sequence_realrooted using recurrence := hrecB

variable (_hQ : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → 0 ≤ (Q n).eval r)
variable (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
variable (hR : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → 0 ≤ (R n).eval r)
variable (hrecR : ∀ n : Nat,
  P (n + 2) = A n * P (n + 1) + (X * R n) * P n)
variable (hraw : ∀ n : Nat,
  P (n + 2) = A n * P (n + 1) + X * (R n * P n))

/-- The tR recurrence selects its factor family ahead of the decoy before lookup. -/
example : ∀ n : Nat, Prec (P n) (P (n + 1)) := by rr_lw_tR_lag_sequence using recurrence := hrecR

/-- The inferred tR shell returns its full real-rooted endpoint. -/
example : ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_lw_tR_lag_sequence_realrooted using recurrence := hrecR

/-- The inferred tR shell supports an indexed splitting projection. -/
example : (P 3).Splits := by rr_lw_tR_lag_sequence_realrooted using recurrence := hrecR

/-- An ascribed normalizer fixes the hidden factor family before its tactic runs. -/
example : ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_lw_tR_lag_sequence using recurrence :=
    (show ∀ n : Nat,
      P (n + 2) = A n * P (n + 1) + (X * R n) * P n from
      fun n => by simpa only [mul_assoc] using hraw n)

end InferredSequenceCertificates

end Tactic
end RealRooted
