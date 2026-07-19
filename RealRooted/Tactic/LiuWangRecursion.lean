import RealRooted.Tactic.MaWang

/-!
# Liu--Wang recursion tactics

This file provides Liu--Wang-named tactic entry points for the derivative-lag
backend in `RealRooted.LiuWangRecursion`.

The older `rr_mw_lw_derivative_lag_*` commands remain available for existing
proofs.  These wrappers expose the same route under names that match the
backend theorem family.
-/

open Polynomial

namespace RealRooted
namespace Tactic

syntax (name := rr_lw_derivative_lag_sequence_sign_auto_named)
  "rr_lw_derivative_lag_sequence_sign_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_derivative_lag_sequence_realrooted_sign_auto_named)
  "rr_lw_derivative_lag_sequence_realrooted_sign_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_derivative_lag_sequence_window_sign_auto_named)
  "rr_lw_derivative_lag_sequence_window_sign_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "root_lower" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_derivative_lag_sequence_realrooted_window_sign_auto_named)
  "rr_lw_derivative_lag_sequence_realrooted_window_sign_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "root_lower" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_derivative_lag_sequence_den_coeff_sign_auto_named)
  "rr_lw_derivative_lag_sequence_den_coeff_sign_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "deriv_factor" ":=" term ","
    "lag_factor" ":=" term ","
    "norm_deriv_coeff" ":=" term ","
    "norm_lag_coeff" ":=" term ","
    "den" ":=" term ","
    "raw_deriv_coeff" ":=" term ","
    "raw_lag_coeff" ":=" term ","
    ("den_nonzero" ":=" term ",")?
    "deriv_coeff_eq" ":=" term ","
    "lag_coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_derivative_lag_sequence_den_coeff_realrooted_sign_auto_named)
  "rr_lw_derivative_lag_sequence_den_coeff_realrooted_sign_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "deriv_factor" ":=" term ","
    "lag_factor" ":=" term ","
    "norm_deriv_coeff" ":=" term ","
    "norm_lag_coeff" ":=" term ","
    "den" ":=" term ","
    "raw_deriv_coeff" ":=" term ","
    "raw_lag_coeff" ":=" term ","
    ("den_nonzero" ":=" term ",")?
    "deriv_coeff_eq" ":=" term ","
    "lag_coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_derivative_lag_sequence_den_coeff_window_sign_auto_named)
  "rr_lw_derivative_lag_sequence_den_coeff_window_sign_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "deriv_factor" ":=" term ","
    "lag_factor" ":=" term ","
    "norm_deriv_coeff" ":=" term ","
    "norm_lag_coeff" ":=" term ","
    "den" ":=" term ","
    "raw_deriv_coeff" ":=" term ","
    "raw_lag_coeff" ":=" term ","
    "root_lower" ":=" term ","
    "root_upper" ":=" term ","
    ("den_nonzero" ":=" term ",")?
    "deriv_coeff_eq" ":=" term ","
    "lag_coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_derivative_lag_sequence_den_coeff_realrooted_window_sign_auto_named)
  "rr_lw_derivative_lag_sequence_den_coeff_realrooted_window_sign_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "deriv_factor" ":=" term ","
    "lag_factor" ":=" term ","
    "norm_deriv_coeff" ":=" term ","
    "norm_lag_coeff" ":=" term ","
    "den" ":=" term ","
    "raw_deriv_coeff" ":=" term ","
    "raw_lag_coeff" ":=" term ","
    "root_lower" ":=" term ","
    "root_upper" ":=" term ","
    ("den_nonzero" ":=" term ",")?
    "deriv_coeff_eq" ":=" term ","
    "lag_coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

macro_rules
  | `(tactic|
      rr_lw_derivative_lag_sequence_sign_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact
          RealRooted.prec_lw_derivative_lag_sequence_of_root_signs
            $hbase $hpos $hdeg_two $hrec
            (by
              intro n hsource
              rr_sign_at_roots using hsource, ($hnonneg (n + 1)))
            (by
              intro n hsource
              rr_sign_at_roots using hsource, ($hnonneg (n + 1)))
            $hdeg_succ $hno)
  | `(tactic|
      rr_lw_derivative_lag_sequence_realrooted_sign_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_lw_derivative_lag_sequence_of_root_signs
            $hbase $hpos $hdeg_two $hrec
            (by
              intro n hsource
              rr_sign_at_roots using hsource, ($hnonneg (n + 1)))
            (by
              intro n hsource
              rr_sign_at_roots using hsource, ($hnonneg (n + 1)))
            $hdeg_succ $hno))
  | `(tactic|
      rr_lw_derivative_lag_sequence_window_sign_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        degree_two := $hdeg_two:term,
        root_lower := $hroot_lower:term,
        root_upper := $hroot_upper:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact
          RealRooted.prec_lw_derivative_lag_sequence_of_root_window
            $hbase $hpos $hdeg_two $hrec $hroot_lower $hroot_upper
            (by
              intro n r hr hroot_window_lower hroot_window_upper
              rr_mw_root_window_linear_facts
              rr_sign)
            (by
              intro n r hr hroot_window_lower hroot_window_upper
              rr_mw_root_window_linear_facts
              rr_sign)
            $hdeg_succ $hno)
  | `(tactic|
      rr_lw_derivative_lag_sequence_realrooted_window_sign_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        degree_two := $hdeg_two:term,
        root_lower := $hroot_lower:term,
        root_upper := $hroot_upper:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_lw_derivative_lag_sequence_of_root_window
            $hbase $hpos $hdeg_two $hrec $hroot_lower $hroot_upper
            (by
              intro n r hr hroot_window_lower hroot_window_upper
              rr_mw_root_window_linear_facts
              rr_sign)
            (by
              intro n r hr hroot_window_lower hroot_window_upper
              rr_mw_root_window_linear_facts
              rr_sign)
            $hdeg_succ $hno))
  | `(tactic|
      rr_lw_derivative_lag_sequence_den_coeff_sign_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        deriv_factor := $V:term,
        lag_factor := $W:term,
        norm_deriv_coeff := $cV:term,
        norm_lag_coeff := $cW:term,
        den := $d:term,
        raw_deriv_coeff := $b:term,
        raw_lag_coeff := $e:term,
        deriv_coeff_eq := $hcoeffV:term,
        lag_coeff_eq := $hcoeffW:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_derivative_lag_sequence_den_coeff_sign_auto using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          degree_two := $hdeg_two,
          deriv_factor := $V,
          lag_factor := $W,
          norm_deriv_coeff := $cV,
          norm_lag_coeff := $cW,
          den := $d,
          raw_deriv_coeff := $b,
          raw_lag_coeff := $e,
          den_nonzero := rr_scalar_active_den_all_term,
          deriv_coeff_eq := $hcoeffV,
          lag_coeff_eq := $hcoeffW,
          raw_recurrence := $hraw,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_derivative_lag_sequence_den_coeff_sign_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        deriv_factor := $V:term,
        lag_factor := $W:term,
        norm_deriv_coeff := $cV:term,
        norm_lag_coeff := $cW:term,
        den := $d:term,
        raw_deriv_coeff := $b:term,
        raw_lag_coeff := $e:term,
        den_nonzero := $hden:term,
        deriv_coeff_eq := $hcoeffV:term,
        lag_coeff_eq := $hcoeffW:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_mw_lw_derivative_lag_sequence_den_coeff_sign_auto using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          degree_two := $hdeg_two,
          deriv_factor := $V,
          lag_factor := $W,
          norm_deriv_coeff := $cV,
          norm_lag_coeff := $cW,
          den := $d,
          raw_deriv_coeff := $b,
          raw_lag_coeff := $e,
          den_nonzero := $hden,
          deriv_coeff_eq := $hcoeffV,
          lag_coeff_eq := $hcoeffW,
          raw_recurrence := $hraw,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_derivative_lag_sequence_den_coeff_realrooted_sign_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        deriv_factor := $V:term,
        lag_factor := $W:term,
        norm_deriv_coeff := $cV:term,
        norm_lag_coeff := $cW:term,
        den := $d:term,
        raw_deriv_coeff := $b:term,
        raw_lag_coeff := $e:term,
        deriv_coeff_eq := $hcoeffV:term,
        lag_coeff_eq := $hcoeffW:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_derivative_lag_sequence_den_coeff_realrooted_sign_auto using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          degree_two := $hdeg_two,
          deriv_factor := $V,
          lag_factor := $W,
          norm_deriv_coeff := $cV,
          norm_lag_coeff := $cW,
          den := $d,
          raw_deriv_coeff := $b,
          raw_lag_coeff := $e,
          den_nonzero := rr_scalar_active_den_all_term,
          deriv_coeff_eq := $hcoeffV,
          lag_coeff_eq := $hcoeffW,
          raw_recurrence := $hraw,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_derivative_lag_sequence_den_coeff_realrooted_sign_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        deriv_factor := $V:term,
        lag_factor := $W:term,
        norm_deriv_coeff := $cV:term,
        norm_lag_coeff := $cW:term,
        den := $d:term,
        raw_deriv_coeff := $b:term,
        raw_lag_coeff := $e:term,
        den_nonzero := $hden:term,
        deriv_coeff_eq := $hcoeffV:term,
        lag_coeff_eq := $hcoeffW:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_mw_lw_derivative_lag_sequence_den_coeff_realrooted_sign_auto using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          degree_two := $hdeg_two,
          deriv_factor := $V,
          lag_factor := $W,
          norm_deriv_coeff := $cV,
          norm_lag_coeff := $cW,
          den := $d,
          raw_deriv_coeff := $b,
          raw_lag_coeff := $e,
          den_nonzero := $hden,
          deriv_coeff_eq := $hcoeffV,
          lag_coeff_eq := $hcoeffW,
          raw_recurrence := $hraw,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_derivative_lag_sequence_den_coeff_window_sign_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        degree_two := $hdeg_two:term,
        deriv_factor := $V:term,
        lag_factor := $W:term,
        norm_deriv_coeff := $cV:term,
        norm_lag_coeff := $cW:term,
        den := $d:term,
        raw_deriv_coeff := $b:term,
        raw_lag_coeff := $e:term,
        root_lower := $hroot_lower:term,
        root_upper := $hroot_upper:term,
        deriv_coeff_eq := $hcoeffV:term,
        lag_coeff_eq := $hcoeffW:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_derivative_lag_sequence_den_coeff_window_sign_auto using
          base := $hbase,
          pos_lc := $hpos,
          degree_two := $hdeg_two,
          deriv_factor := $V,
          lag_factor := $W,
          norm_deriv_coeff := $cV,
          norm_lag_coeff := $cW,
          den := $d,
          raw_deriv_coeff := $b,
          raw_lag_coeff := $e,
          root_lower := $hroot_lower,
          root_upper := $hroot_upper,
          den_nonzero := rr_scalar_active_den_all_term,
          deriv_coeff_eq := $hcoeffV,
          lag_coeff_eq := $hcoeffW,
          raw_recurrence := $hraw,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_derivative_lag_sequence_den_coeff_window_sign_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        degree_two := $hdeg_two:term,
        deriv_factor := $V:term,
        lag_factor := $W:term,
        norm_deriv_coeff := $cV:term,
        norm_lag_coeff := $cW:term,
        den := $d:term,
        raw_deriv_coeff := $b:term,
        raw_lag_coeff := $e:term,
        root_lower := $hroot_lower:term,
        root_upper := $hroot_upper:term,
        den_nonzero := $hden:term,
        deriv_coeff_eq := $hcoeffV:term,
        lag_coeff_eq := $hcoeffW:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_mw_lw_derivative_lag_sequence_den_coeff_window_sign_auto using
          base := $hbase,
          pos_lc := $hpos,
          degree_two := $hdeg_two,
          deriv_factor := $V,
          lag_factor := $W,
          norm_deriv_coeff := $cV,
          norm_lag_coeff := $cW,
          den := $d,
          raw_deriv_coeff := $b,
          raw_lag_coeff := $e,
          root_lower := $hroot_lower,
          root_upper := $hroot_upper,
          den_nonzero := $hden,
          deriv_coeff_eq := $hcoeffV,
          lag_coeff_eq := $hcoeffW,
          raw_recurrence := $hraw,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_derivative_lag_sequence_den_coeff_realrooted_window_sign_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        degree_two := $hdeg_two:term,
        deriv_factor := $V:term,
        lag_factor := $W:term,
        norm_deriv_coeff := $cV:term,
        norm_lag_coeff := $cW:term,
        den := $d:term,
        raw_deriv_coeff := $b:term,
        raw_lag_coeff := $e:term,
        root_lower := $hroot_lower:term,
        root_upper := $hroot_upper:term,
        deriv_coeff_eq := $hcoeffV:term,
        lag_coeff_eq := $hcoeffW:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_derivative_lag_sequence_den_coeff_realrooted_window_sign_auto using
          base := $hbase,
          pos_lc := $hpos,
          degree_two := $hdeg_two,
          deriv_factor := $V,
          lag_factor := $W,
          norm_deriv_coeff := $cV,
          norm_lag_coeff := $cW,
          den := $d,
          raw_deriv_coeff := $b,
          raw_lag_coeff := $e,
          root_lower := $hroot_lower,
          root_upper := $hroot_upper,
          den_nonzero := rr_scalar_active_den_all_term,
          deriv_coeff_eq := $hcoeffV,
          lag_coeff_eq := $hcoeffW,
          raw_recurrence := $hraw,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_derivative_lag_sequence_den_coeff_realrooted_window_sign_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        degree_two := $hdeg_two:term,
        deriv_factor := $V:term,
        lag_factor := $W:term,
        norm_deriv_coeff := $cV:term,
        norm_lag_coeff := $cW:term,
        den := $d:term,
        raw_deriv_coeff := $b:term,
        raw_lag_coeff := $e:term,
        root_lower := $hroot_lower:term,
        root_upper := $hroot_upper:term,
        den_nonzero := $hden:term,
        deriv_coeff_eq := $hcoeffV:term,
        lag_coeff_eq := $hcoeffW:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_mw_lw_derivative_lag_sequence_den_coeff_realrooted_window_sign_auto using
          base := $hbase,
          pos_lc := $hpos,
          degree_two := $hdeg_two,
          deriv_factor := $V,
          lag_factor := $W,
          norm_deriv_coeff := $cV,
          norm_lag_coeff := $cW,
          den := $d,
          raw_deriv_coeff := $b,
          raw_lag_coeff := $e,
          root_lower := $hroot_lower,
          root_upper := $hroot_upper,
          den_nonzero := $hden,
          deriv_coeff_eq := $hcoeffV,
          lag_coeff_eq := $hcoeffW,
          raw_recurrence := $hraw,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)

end Tactic
end RealRooted
