import RealRooted.Tactic.LiuWang.SequencePositive

/-!
# Liu--Wang positive-affine regression examples

Sequence tests for positive-affine lag factors, including shifted
nonnegative-coefficient certificates and projection endpoints.
-/

open Polynomial

namespace RealRooted
namespace Tactic

/-- Family G7 shifted-root positive affine lag:
`P_{n+2}=A_nP_{n+1}+c_n(a_n+t)P_n`.

The side condition is the root-location certificate `r <= -a_n` for the
current row, which is what the shifted-variable argument supplies. -/
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]} {c a : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hroot_upper : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → r ≤ -(a n))
    (hrec : ∀ n : Nat,
      P (n + 2) = A n * P (n + 1) + (C (c n) * (C (a n) + X)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_lw_positive_affine_lag_sequence using
    base := hbase,
    pos_lc := hpos,
    coeff_nonneg := hc,
    root_upper := hroot_upper,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Automatic coefficient side-goal for the positive-affine `Prec` endpoint. -/
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hroot_upper : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → r ≤ -(1 : ℝ))
    (hrec : ∀ n : Nat,
      P (n + 2) =
        A n * P (n + 1) + (C ((n : ℝ) + 1) * (C (1 : ℝ) + X)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_lw_positive_affine_lag_sequence_auto using
    base := hbase,
    pos_lc := hpos,
    root_upper := hroot_upper,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Real-rootedness endpoint for the positive-affine lag with explicit scalar
nonnegativity. -/
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]} {c a : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hroot_upper : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → r ≤ -(a n))
    (hrec : ∀ n : Nat,
      P (n + 2) = A n * P (n + 1) + (C (c n) * (C (a n) + X)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_lw_positive_affine_lag_sequence_realrooted using
    base := hbase,
    pos_lc := hpos,
    coeff_nonneg := hc,
    root_upper := hroot_upper,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Automatic coefficient side-goal for active positive-affine lags such as
`(n+1)(1+t)`. -/
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hroot_upper : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → r ≤ -(1 : ℝ))
    (hrec : ∀ n : Nat,
      P (n + 2) =
        A n * P (n + 1) + (C ((n : ℝ) + 1) * (C (1 : ℝ) + X)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_lw_positive_affine_lag_sequence_realrooted_auto using
    base := hbase,
    pos_lc := hpos,
    root_upper := hroot_upper,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Unit positive-affine lag `a_n+t`, covering the direct `1+t` and `2+t`
shifted-Fibonacci records after the root bound is supplied. -/
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]} {a : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hroot_upper : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → r ≤ -(a n))
    (hrec : ∀ n : Nat, P (n + 2) = A n * P (n + 1) + (C (a n) + X) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_lw_C_add_X_lag_sequence_realrooted using
    base := hbase,
    pos_lc := hpos,
    root_upper := hroot_upper,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Unit positive-affine lag, tested on the `Prec` endpoint. -/
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]} {a : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hroot_upper : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → r ≤ -(a n))
    (hrec : ∀ n : Nat, P (n + 2) = A n * P (n + 1) + (C (a n) + X) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_lw_C_add_X_lag_sequence using
    base := hbase,
    pos_lc := hpos,
    root_upper := hroot_upper,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- The shifted certificate version removes the explicit root-location
hypothesis from the positive-affine lag. -/
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]} {c a : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hshift_nonneg :
      ∀ n : Nat, HasNonnegCoeffs ((P (n + 1)).comp (X - C (a n))))
    (hrec : ∀ n : Nat,
      P (n + 2) = A n * P (n + 1) + (C (c n) * (C (a n) + X)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_lw_positive_affine_lag_sequence_shift_nonneg using
    base := hbase,
    pos_lc := hpos,
    coeff_nonneg := hc,
    shift_nonneg := hshift_nonneg,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Shifted positive-affine lag with automatic scalar nonnegativity, tested on
the `Prec` endpoint. -/
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hshift_nonneg :
      ∀ n : Nat, HasNonnegCoeffs ((P (n + 1)).comp (X - C (1 : ℝ))))
    (hrec : ∀ n : Nat,
      P (n + 2) =
        A n * P (n + 1) + (C ((n : ℝ) + 1) * (C (1 : ℝ) + X)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_lw_positive_affine_lag_sequence_shift_nonneg_auto using
    base := hbase,
    pos_lc := hpos,
    shift_nonneg := hshift_nonneg,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Shifted positive-affine real-rootedness endpoint with explicit scalar
nonnegativity. -/
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]} {c a : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hshift_nonneg :
      ∀ n : Nat, HasNonnegCoeffs ((P (n + 1)).comp (X - C (a n))))
    (hrec : ∀ n : Nat,
      P (n + 2) = A n * P (n + 1) + (C (c n) * (C (a n) + X)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_lw_positive_affine_lag_sequence_realrooted_shift_nonneg using
    base := hbase,
    pos_lc := hpos,
    coeff_nonneg := hc,
    shift_nonneg := hshift_nonneg,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Unit positive-affine lag with shifted nonnegative coefficients, tested on
the `Prec` endpoint. -/
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]} {a : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hshift_nonneg :
      ∀ n : Nat, HasNonnegCoeffs ((P (n + 1)).comp (X - C (a n))))
    (hrec : ∀ n : Nat, P (n + 2) = A n * P (n + 1) + (C (a n) + X) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_lw_C_add_X_lag_sequence_shift_nonneg using
    base := hbase,
    pos_lc := hpos,
    shift_nonneg := hshift_nonneg,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- The same shifted certificate path with automatic scalar nonnegativity. -/
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hshift_nonneg :
      ∀ n : Nat, HasNonnegCoeffs ((P (n + 1)).comp (X - C (1 : ℝ))))
    (hrec : ∀ n : Nat,
      P (n + 2) =
        A n * P (n + 1) + (C ((n : ℝ) + 1) * (C (1 : ℝ) + X)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_lw_positive_affine_lag_sequence_realrooted_shift_nonneg_auto using
    base := hbase,
    pos_lc := hpos,
    shift_nonneg := hshift_nonneg,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Unit positive-affine lag `a_n+t` with shifted nonnegative coefficients
supplying the root bound automatically. -/
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]} {a : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hshift_nonneg :
      ∀ n : Nat, HasNonnegCoeffs ((P (n + 1)).comp (X - C (a n))))
    (hrec : ∀ n : Nat, P (n + 2) = A n * P (n + 1) + (C (a n) + X) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_lw_C_add_X_lag_sequence_realrooted_shift_nonneg using
    base := hbase,
    pos_lc := hpos,
    shift_nonneg := hshift_nonneg,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno


end Tactic
end RealRooted
