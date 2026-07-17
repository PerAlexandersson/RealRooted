import RealRooted.CoefficientShape
import RealRooted.Tactic.Finish

/-!
# Coefficient-shape finish tactics

Small wrappers for coefficient consequences of nonnegative real-rooted
polynomials.  This file is separate from `RealRooted.Tactic.Finish` so the
heavier coefficient-shape imports do not affect hot recurrence tactics.
-/

open Polynomial

namespace RealRooted

/-- Ultra-log-concavity from nonnegative coefficients and strict real-rootedness. -/
theorem hasUltraLogConcaveCoeffs_of_hasNonnegCoeffs_of_isRealRooted {p : ℝ[X]}
    (hpnn : HasNonnegCoeffs p) (hrr : p ≠ 0 ∧ p.Splits) :
    HasUltraLogConcaveCoeffs p :=
  hasUltraLogConcaveCoeffs_of_hasNonnegCoeffs_of_eq_zero_or_splits hpnn
    (eq_zero_or_splits_of_isRealRooted hrr)

/-- No-internal-zero coefficients from nonnegative coefficients and strict
real-rootedness. -/
theorem hasNoInternalCoeffZeros_of_hasNonnegCoeffs_of_isRealRooted {p : ℝ[X]}
    (hpnn : HasNonnegCoeffs p) (hrr : p ≠ 0 ∧ p.Splits) :
    HasNoInternalCoeffZeros p :=
  hasNoInternalCoeffZeros_of_hasNonnegCoeffs_of_eq_zero_or_splits hpnn
    (eq_zero_or_splits_of_isRealRooted hrr)

/-- Log-concavity from nonnegative coefficients and strict real-rootedness. -/
theorem hasLogConcaveCoeffs_of_hasNonnegCoeffs_of_isRealRooted {p : ℝ[X]}
    (hpnn : HasNonnegCoeffs p) (hrr : p ≠ 0 ∧ p.Splits) :
    HasLogConcaveCoeffs p :=
  hasLogConcaveCoeffs_of_hasNonnegCoeffs_of_eq_zero_or_splits hpnn
    (eq_zero_or_splits_of_isRealRooted hrr)

/-- Unimodality from nonnegative coefficients and strict real-rootedness. -/
theorem hasUnimodalCoeffs_of_hasNonnegCoeffs_of_isRealRooted {p : ℝ[X]}
    (hpnn : HasNonnegCoeffs p) (hrr : p ≠ 0 ∧ p.Splits) :
    HasUnimodalCoeffs p :=
  hasUnimodalCoeffs_of_hasNonnegCoeffs_of_eq_zero_or_splits hpnn
    (eq_zero_or_splits_of_isRealRooted hrr)

/-- Row-wise ultra-log-concavity from nonnegative coefficients and zero-aware splitting. -/
theorem sequence_hasUltraLogConcaveCoeffs_of_nonneg_of_eq_zero_or_splits
    {P : Nat → ℝ[X]} (hPnn : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hPrr : ∀ n : Nat, P n = 0 ∨ (P n).Splits) :
    ∀ n : Nat, HasUltraLogConcaveCoeffs (P n) :=
  fun n => hasUltraLogConcaveCoeffs_of_hasNonnegCoeffs_of_eq_zero_or_splits (hPnn n)
    (hPrr n)

/-- Row-wise no-internal-zero coefficients from nonnegative coefficients and
zero-aware splitting. -/
theorem sequence_hasNoInternalCoeffZeros_of_nonneg_of_eq_zero_or_splits
    {P : Nat → ℝ[X]} (hPnn : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hPrr : ∀ n : Nat, P n = 0 ∨ (P n).Splits) :
    ∀ n : Nat, HasNoInternalCoeffZeros (P n) :=
  fun n => hasNoInternalCoeffZeros_of_hasNonnegCoeffs_of_eq_zero_or_splits (hPnn n)
    (hPrr n)

/-- Row-wise log-concavity from nonnegative coefficients and zero-aware splitting. -/
theorem sequence_hasLogConcaveCoeffs_of_nonneg_of_eq_zero_or_splits
    {P : Nat → ℝ[X]} (hPnn : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hPrr : ∀ n : Nat, P n = 0 ∨ (P n).Splits) :
    ∀ n : Nat, HasLogConcaveCoeffs (P n) :=
  fun n => hasLogConcaveCoeffs_of_hasNonnegCoeffs_of_eq_zero_or_splits (hPnn n)
    (hPrr n)

/-- Row-wise unimodality from nonnegative coefficients and zero-aware splitting. -/
theorem sequence_hasUnimodalCoeffs_of_nonneg_of_eq_zero_or_splits
    {P : Nat → ℝ[X]} (hPnn : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hPrr : ∀ n : Nat, P n = 0 ∨ (P n).Splits) :
    ∀ n : Nat, HasUnimodalCoeffs (P n) :=
  fun n => hasUnimodalCoeffs_of_hasNonnegCoeffs_of_eq_zero_or_splits (hPnn n)
    (hPrr n)

/-- Row-wise ultra-log-concavity from nonnegative coefficients and strict real-rootedness. -/
theorem sequence_hasUltraLogConcaveCoeffs_of_nonneg_of_isRealRooted
    {P : Nat → ℝ[X]} (hPnn : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hPrr : ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits) :
    ∀ n : Nat, HasUltraLogConcaveCoeffs (P n) :=
  sequence_hasUltraLogConcaveCoeffs_of_nonneg_of_eq_zero_or_splits hPnn
    (eq_zero_or_splits_of_isRealRooted_sequence hPrr)

/-- Row-wise no-internal-zero coefficients from nonnegative coefficients and
real-rootedness. -/
theorem sequence_hasNoInternalCoeffZeros_of_nonneg_of_isRealRooted
    {P : Nat → ℝ[X]} (hPnn : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hPrr : ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits) :
    ∀ n : Nat, HasNoInternalCoeffZeros (P n) :=
  sequence_hasNoInternalCoeffZeros_of_nonneg_of_eq_zero_or_splits hPnn
    (eq_zero_or_splits_of_isRealRooted_sequence hPrr)

/-- Row-wise log-concavity from nonnegative coefficients and strict real-rootedness. -/
theorem sequence_hasLogConcaveCoeffs_of_nonneg_of_isRealRooted
    {P : Nat → ℝ[X]} (hPnn : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hPrr : ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits) :
    ∀ n : Nat, HasLogConcaveCoeffs (P n) :=
  sequence_hasLogConcaveCoeffs_of_nonneg_of_eq_zero_or_splits hPnn
    (eq_zero_or_splits_of_isRealRooted_sequence hPrr)

/-- Row-wise unimodality from nonnegative coefficients and strict real-rootedness. -/
theorem sequence_hasUnimodalCoeffs_of_nonneg_of_isRealRooted
    {P : Nat → ℝ[X]} (hPnn : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hPrr : ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits) :
    ∀ n : Nat, HasUnimodalCoeffs (P n) :=
  sequence_hasUnimodalCoeffs_of_nonneg_of_eq_zero_or_splits hPnn
    (eq_zero_or_splits_of_isRealRooted_sequence hPrr)

namespace Tactic

syntax (name := rr_coeff_shape_named)
  "rr_coeff_shape" " using "
    "nonneg" ":=" term ","
    "realrooted" ":=" term :
  tactic

syntax (name := rr_coeff_shape_auto) "rr_coeff_shape" : tactic

macro_rules
  | `(tactic|
      rr_coeff_shape using
        nonneg := $hPnn:term,
        realrooted := $hPrr:term) =>
      `(tactic|
        first
          | exact RealRooted.hasUltraLogConcaveCoeffs_of_hasNonnegCoeffs_of_eq_zero_or_splits
              $hPnn $hPrr
          | exact RealRooted.hasNoInternalCoeffZeros_of_hasNonnegCoeffs_of_eq_zero_or_splits
              $hPnn $hPrr
          | exact RealRooted.hasLogConcaveCoeffs_of_hasNonnegCoeffs_of_eq_zero_or_splits
              $hPnn $hPrr
          | exact RealRooted.hasUnimodalCoeffs_of_hasNonnegCoeffs_of_eq_zero_or_splits
              $hPnn $hPrr
          | exact RealRooted.hasUltraLogConcaveCoeffs_of_hasNonnegCoeffs_of_isRealRooted
              $hPnn $hPrr
          | exact RealRooted.hasNoInternalCoeffZeros_of_hasNonnegCoeffs_of_isRealRooted
              $hPnn $hPrr
          | exact RealRooted.hasLogConcaveCoeffs_of_hasNonnegCoeffs_of_isRealRooted
              $hPnn $hPrr
          | exact RealRooted.hasUnimodalCoeffs_of_hasNonnegCoeffs_of_isRealRooted
              $hPnn $hPrr
          | exact RealRooted.sequence_hasUltraLogConcaveCoeffs_of_nonneg_of_eq_zero_or_splits
              $hPnn $hPrr
          | exact (RealRooted.sequence_hasUltraLogConcaveCoeffs_of_nonneg_of_eq_zero_or_splits
              $hPnn $hPrr _)
          | exact RealRooted.sequence_hasNoInternalCoeffZeros_of_nonneg_of_eq_zero_or_splits
              $hPnn $hPrr
          | exact (RealRooted.sequence_hasNoInternalCoeffZeros_of_nonneg_of_eq_zero_or_splits
              $hPnn $hPrr _)
          | exact RealRooted.sequence_hasLogConcaveCoeffs_of_nonneg_of_eq_zero_or_splits
              $hPnn $hPrr
          | exact (RealRooted.sequence_hasLogConcaveCoeffs_of_nonneg_of_eq_zero_or_splits
              $hPnn $hPrr _)
          | exact RealRooted.sequence_hasUnimodalCoeffs_of_nonneg_of_eq_zero_or_splits
              $hPnn $hPrr
          | exact (RealRooted.sequence_hasUnimodalCoeffs_of_nonneg_of_eq_zero_or_splits
              $hPnn $hPrr _)
          | exact RealRooted.sequence_hasUltraLogConcaveCoeffs_of_nonneg_of_isRealRooted
              $hPnn $hPrr
          | exact (RealRooted.sequence_hasUltraLogConcaveCoeffs_of_nonneg_of_isRealRooted
              $hPnn $hPrr _)
          | exact RealRooted.sequence_hasNoInternalCoeffZeros_of_nonneg_of_isRealRooted
              $hPnn $hPrr
          | exact (RealRooted.sequence_hasNoInternalCoeffZeros_of_nonneg_of_isRealRooted
              $hPnn $hPrr _)
          | exact RealRooted.sequence_hasLogConcaveCoeffs_of_nonneg_of_isRealRooted
              $hPnn $hPrr
          | exact (RealRooted.sequence_hasLogConcaveCoeffs_of_nonneg_of_isRealRooted
              $hPnn $hPrr _)
          | exact RealRooted.sequence_hasUnimodalCoeffs_of_nonneg_of_isRealRooted
              $hPnn $hPrr
          | exact (RealRooted.sequence_hasUnimodalCoeffs_of_nonneg_of_isRealRooted
              $hPnn $hPrr _))
  | `(tactic| rr_coeff_shape) =>
      `(tactic|
        first
          | rr_coeff_shape using nonneg := by rr_lookup, realrooted := by rr_lookup
          | rr_coeff_shape using nonneg := by rr_lookup, realrooted := by rr_realrooted)

end Tactic
end RealRooted
