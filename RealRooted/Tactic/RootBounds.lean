import RealRooted.RootBounds
import RealRooted.Tactic.Sign

/-!
# Root-bound certificate tactics

The common OEIS recurrence route uses nonnegative coefficients to propagate
the root interval `(-∞, 0]`.  This file packages the repeated step from
`p ≠ 0 ∧ p.Splits` and `HasNonnegCoeffs p` to nonpositive roots, and combines
it with `rr_sign` for coefficient-sign goals at roots.
-/

open Polynomial

namespace RealRooted

namespace Tactic

syntax (name := rr_root_nonpos_realrooted)
  "rr_root_nonpos" " using " term ", " term ", " term : tactic

syntax (name := rr_root_nonpos_ne_splits)
  "rr_root_nonpos" " using " term ", " term ", " term ", " term : tactic

syntax (name := rr_root_nonpos_named)
  "rr_root_nonpos" " using "
    "realrooted" ":=" term ","
    "nonneg" ":=" term ","
    "root" ":=" term :
  tactic

syntax (name := rr_root_nonpos_auto) "rr_root_nonpos" : tactic

syntax (name := rr_root_nonpos_sequence_named)
  "rr_root_nonpos_sequence" " using "
    "realrooted" ":=" term ","
    "nonneg" ":=" term :
  tactic

syntax (name := rr_root_le_neg_shift_named)
  "rr_root_le_neg_shift" " using "
    "realrooted" ":=" term ","
    "shift_nonneg" ":=" term ","
    "root" ":=" term :
  tactic

syntax (name := rr_root_le_neg_shift_sequence_named)
  "rr_root_le_neg_shift_sequence" " using "
    "realrooted" ":=" term ","
    "shift_nonneg" ":=" term :
  tactic

syntax (name := rr_derivative_root_nonpos_named)
  "rr_derivative_root_nonpos" " using "
    "realrooted" ":=" term ","
    "nonneg" ":=" term ","
    "derivative_ne" ":=" term ","
    "root" ":=" term :
  tactic

syntax (name := rr_derivative_root_nonpos_auto) "rr_derivative_root_nonpos" : tactic

syntax (name := rr_derivative_root_nonpos_sequence_named)
  "rr_derivative_root_nonpos_sequence" " using "
    "realrooted" ":=" term ","
    "nonneg" ":=" term ","
    "derivative_ne" ":=" term :
  tactic

syntax (name := rr_sign_at_roots)
  "rr_sign_at_roots" " using " term ", " term : tactic

syntax (name := rr_sign_at_roots_named)
  "rr_sign_at_roots" " using "
    "realrooted" ":=" term ","
    "nonneg" ":=" term :
  tactic

syntax (name := rr_sign_at_roots_auto) "rr_sign_at_roots" : tactic

syntax (name := rr_sign_at_roots_sequence_named)
  "rr_sign_at_roots_sequence" " using "
    "realrooted" ":=" term ","
    "nonneg" ":=" term :
  tactic

syntax (name := rr_sign_at_roots_term) "rr_sign_at_roots_term " term ", " term : term

syntax (name := rr_sign_at_roots_sequence_term)
  "rr_sign_at_roots_sequence_term " term ", " term :
  term

syntax (name := rr_sign_at_roots_nonpos_term)
  "rr_sign_at_roots_nonpos_term " term :
  term

syntax (name := rr_sign_at_roots_factor)
  "rr_sign_at_roots_with_factor" " using " term ", " term ", " term : tactic

syntax (name := rr_sign_at_roots_factor_named)
  "rr_sign_at_roots_with_factor" " using "
    "realrooted" ":=" term ","
    "nonneg" ":=" term ","
    "factor_nonneg" ":=" term :
  tactic

syntax (name := rr_sign_at_roots_factor_auto)
  "rr_sign_at_roots_with_factor" " using "
    "factor_nonneg" ":=" term :
  tactic

syntax (name := rr_sign_at_roots_sequence_factor_named)
  "rr_sign_at_roots_sequence_with_factor" " using "
    "realrooted" ":=" term ","
    "nonneg" ":=" term ","
    "factor_nonneg" ":=" term :
  tactic

syntax (name := rr_sign_at_roots_sequence_factor_term)
  "rr_sign_at_roots_sequence_factor_term " term ", " term ", " term :
  term

syntax (name := rr_sign_at_roots_factor_term)
  "rr_sign_at_roots_factor_term " term ", " term ", " term :
  term

syntax (name := rr_sign_at_roots_nonpos_factor_term)
  "rr_sign_at_roots_nonpos_factor_term " term ", " term :
  term

syntax (name := rr_sign_at_roots_lower)
  "rr_sign_at_roots_lower" " using " term : tactic

syntax (name := rr_sign_at_roots_lower_named)
  "rr_sign_at_roots_lower" " using "
    "root_lower" ":=" term :
  tactic

syntax (name := rr_sign_at_roots_upper)
  "rr_sign_at_roots_upper" " using " term : tactic

syntax (name := rr_sign_at_roots_upper_named)
  "rr_sign_at_roots_upper" " using "
    "root_upper" ":=" term :
  tactic

syntax (name := rr_sign_at_roots_lower_seq)
  "rr_sign_at_roots_lower_seq " term :
  term

syntax (name := rr_sign_at_roots_upper_seq)
  "rr_sign_at_roots_upper_seq " term :
  term

syntax (name := rr_sign_at_roots_lower_term)
  "rr_sign_at_roots_lower_term " term :
  term

syntax (name := rr_sign_at_roots_upper_term)
  "rr_sign_at_roots_upper_term " term :
  term

syntax (name := rr_sign_at_roots_window)
  "rr_sign_at_roots_window" " using " term ", " term : tactic

syntax (name := rr_sign_at_roots_window_named)
  "rr_sign_at_roots_window" " using "
    "root_lower" ":=" term ","
    "root_upper" ":=" term :
  tactic

syntax (name := rr_sign_at_roots_window_term)
  "rr_sign_at_roots_window_term " term ", " term :
  term

macro_rules
  | `(tactic| rr_root_nonpos using $hrr:term, $hnn:term, $hr:term) =>
      `(tactic|
        exact RealRooted.root_nonpos_of_realrooted_of_nonneg_coeffs
          $hrr $hnn $hr)
  | `(tactic| rr_root_nonpos using $hne:term, $hsplits:term, $hnn:term, $hr:term) =>
      `(tactic|
        exact RealRooted.root_nonpos_of_ne_zero_of_splits_of_nonneg_coeffs
          $hne $hsplits $hnn $hr)
  | `(tactic|
      rr_root_nonpos using
        realrooted := $hrr:term,
        nonneg := $hnn:term,
        root := $hr:term) =>
      `(tactic|
        rr_root_nonpos using $hrr, $hnn, $hr)
  | `(tactic| rr_root_nonpos) =>
      `(tactic|
        first
          | exact RealRooted.root_nonpos_of_realrooted_of_nonneg_coeffs
              (by assumption) (by assumption) (by assumption)
          | exact RealRooted.root_nonpos_of_ne_zero_of_splits_of_nonneg_coeffs
              (by assumption) (by assumption) (by assumption) (by assumption))
  | `(tactic|
      rr_root_nonpos_sequence using
        realrooted := $hrr:term,
        nonneg := $hnn:term) =>
      `(tactic|
        exact RealRooted.roots_nonpos_sequence_of_realrooted_of_nonneg_coeffs
          $hrr $hnn)
  | `(tactic|
      rr_root_le_neg_shift using
        realrooted := $hrr:term,
        shift_nonneg := $hnn:term,
        root := $hr:term) =>
      `(tactic|
        exact RealRooted.root_le_neg_of_realrooted_of_shift_nonneg_coeffs
          $hrr $hnn $hr)
  | `(tactic|
      rr_root_le_neg_shift_sequence using
        realrooted := $hrr:term,
        shift_nonneg := $hnn:term) =>
      `(tactic|
        exact RealRooted.roots_le_neg_sequence_of_realrooted_of_shift_nonneg_coeffs
          $hrr $hnn)
  | `(tactic|
      rr_derivative_root_nonpos using
        realrooted := $hrr:term,
        nonneg := $hnn:term,
        derivative_ne := $hder_ne:term,
        root := $hr:term) =>
      `(tactic|
        exact RealRooted.derivative_root_nonpos_of_splits_of_nonneg_coeffs
          ($hrr).2 $hnn $hder_ne $hr)
  | `(tactic| rr_derivative_root_nonpos) =>
      `(tactic|
        exact RealRooted.derivative_root_nonpos_of_realrooted_of_nonneg_coeffs
          (by assumption) (by assumption) (by assumption) (by assumption))
  | `(tactic|
      rr_derivative_root_nonpos_sequence using
        realrooted := $hrr:term,
        nonneg := $hnn:term,
        derivative_ne := $hder_ne:term) =>
      `(tactic|
        exact RealRooted.derivative_roots_nonpos_sequence_of_realrooted_of_nonneg_coeffs
          $hrr $hnn $hder_ne)
  | `(tactic| rr_sign_at_roots using $hrr:term, $hnn:term) =>
      `(tactic|
        exact (rr_sign_at_roots_term $hrr, $hnn))
  | `(tactic|
      rr_sign_at_roots using
        realrooted := $hrr:term,
        nonneg := $hnn:term) =>
      `(tactic|
        rr_sign_at_roots using $hrr, $hnn)
  | `(rr_sign_at_roots_term $hrr:term, $hnn:term) =>
      `(rr_sign_at_roots_nonpos_term
          (RealRooted.roots_nonpos_of_realrooted_of_nonneg_coeffs $hrr $hnn))
  | `(rr_sign_at_roots_nonpos_term $hroot_nonpos:term) =>
      `(fun r hroot => by
          have hroot_nonpos : r ≤ 0 := $hroot_nonpos r hroot
          rr_sign)
  | `(tactic| rr_sign_at_roots) =>
      `(tactic|
        exact fun r hroot => by
          have hroot_nonpos : r ≤ 0 := by rr_root_nonpos
          rr_sign)
  | `(tactic|
      rr_sign_at_roots_sequence using
        realrooted := $hrr:term,
        nonneg := $hnn:term) =>
      `(tactic|
        exact (rr_sign_at_roots_sequence_term $hrr, $hnn))
  | `(rr_sign_at_roots_sequence_term $hrr:term, $hnn:term) =>
      `(fun n =>
          (rr_sign_at_roots_nonpos_term
            ((RealRooted.roots_nonpos_sequence_of_realrooted_of_nonneg_coeffs
              $hrr $hnn) n)))
  | `(tactic|
      rr_sign_at_roots_with_factor using $hrr:term, $hnn:term, $hq:term) =>
      `(tactic|
        exact (rr_sign_at_roots_factor_term $hrr, $hnn, $hq))
  | `(tactic|
      rr_sign_at_roots_with_factor using
        realrooted := $hrr:term,
        nonneg := $hnn:term,
        factor_nonneg := $hq:term) =>
      `(tactic|
        rr_sign_at_roots_with_factor using $hrr, $hnn, $hq)
  | `(rr_sign_at_roots_factor_term $hrr:term, $hnn:term, $hq:term) =>
      `(rr_sign_at_roots_nonpos_factor_term
          (RealRooted.roots_nonpos_of_realrooted_of_nonneg_coeffs $hrr $hnn),
          $hq)
  | `(rr_sign_at_roots_nonpos_factor_term $hroot_nonpos:term, $hq:term) =>
      `(fun r hroot => by
          have hroot_nonpos : r ≤ 0 := $hroot_nonpos r hroot
          have hfactor_nonneg := $hq r hroot
          rr_sign)
  | `(tactic|
      rr_sign_at_roots_with_factor using
        factor_nonneg := $hq:term) =>
      `(tactic|
        exact fun r hroot => by
          have hroot_nonpos : r ≤ 0 := by rr_root_nonpos
          have hfactor_nonneg := $hq r hroot
          rr_sign)
  | `(tactic|
      rr_sign_at_roots_sequence_with_factor using
        realrooted := $hrr:term,
        nonneg := $hnn:term,
        factor_nonneg := $hq:term) =>
      `(tactic|
        exact (rr_sign_at_roots_sequence_factor_term $hrr, $hnn, $hq))
  | `(rr_sign_at_roots_sequence_factor_term $hrr:term, $hnn:term, $hq:term) =>
      `(fun n =>
          (rr_sign_at_roots_nonpos_factor_term
            ((RealRooted.roots_nonpos_sequence_of_realrooted_of_nonneg_coeffs
              $hrr $hnn) n),
            ($hq n)))
  | `(tactic|
      rr_sign_at_roots_lower using $hlo:term) =>
      `(tactic|
        exact (rr_sign_at_roots_lower_term $hlo))
  | `(tactic|
      rr_sign_at_roots_lower using
        root_lower := $hlo:term) =>
      `(tactic|
        rr_sign_at_roots_lower using $hlo)
  | `(tactic|
      rr_sign_at_roots_upper using $hhi:term) =>
      `(tactic|
        exact (rr_sign_at_roots_upper_term $hhi))
  | `(tactic|
      rr_sign_at_roots_upper using
        root_upper := $hhi:term) =>
      `(tactic|
        rr_sign_at_roots_upper using $hhi)
  | `(rr_sign_at_roots_lower_seq $hlo:term) =>
      `(fun n => (rr_sign_at_roots_lower_term ($hlo n)))
  | `(rr_sign_at_roots_upper_seq $hhi:term) =>
      `(fun n => (rr_sign_at_roots_upper_term ($hhi n)))
  | `(rr_sign_at_roots_lower_term $hlo:term) =>
      `(fun r hroot => by
          have hroot_lower := $hlo r hroot
          rr_sign)
  | `(rr_sign_at_roots_upper_term $hhi:term) =>
      `(fun r hroot => by
          have hroot_upper := $hhi r hroot
          rr_sign)
  | `(tactic|
      rr_sign_at_roots_window using $hlo:term, $hhi:term) =>
      `(tactic|
        exact (rr_sign_at_roots_window_term $hlo, $hhi))
  | `(tactic|
      rr_sign_at_roots_window using
        root_lower := $hlo:term,
        root_upper := $hhi:term) =>
      `(tactic|
        rr_sign_at_roots_window using $hlo, $hhi)
  | `(rr_sign_at_roots_window_term $hlo:term, $hhi:term) =>
      `(fun r hroot => by
          have hroot_lower := $hlo r hroot
          have hroot_upper := $hhi r hroot
          rr_sign)

end Tactic
end RealRooted
