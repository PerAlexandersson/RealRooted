import RealRooted.Tactic.MaWang.Sequences

/-!
# Ma--Wang tactic scalar-denominator rules

Elaboration rules for normalized scalar-denominator recurrence certificates.
-/

namespace RealRooted
namespace Tactic

macro_rules
  | `(tactic|
      rr_mw_lw_derivative_lag_sequence_den_coeff_sign_auto using
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
          den_nonzero := rr_mw_active_den_all_term,
          deriv_coeff_eq := rr_mw_coeff_all_term,
          lag_coeff_eq := rr_mw_coeff_all_term,
          raw_recurrence := $hraw,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_mw_lw_derivative_lag_sequence_den_coeff_sign_auto using
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
          den_nonzero := rr_mw_active_den_all_term,
          deriv_coeff_eq := $hcoeffV,
          lag_coeff_eq := $hcoeffW,
          raw_recurrence := $hraw,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_mw_lw_derivative_lag_sequence_den_coeff_sign_auto using
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
        exact
          RealRooted.prec_mw_lw_derivative_lag_sequence_den_coeff_of_nonneg_coeffs
            (V := $V) (W := $W) (b := $b) (c := $cV) (e := $e) (a := $cW)
            (d := $d)
            $hbase $hpos $hnonneg $hdeg_two
            rr_mw_active_nonneg
            rr_mw_active_nonneg
            (rr_mw_root_sign_seq)
            (rr_mw_root_sign_seq)
            $hden $hcoeffV $hcoeffW
            (rr_mw_raw_recurrence_seq $hraw)
            $hdeg_succ $hno)
  | `(tactic|
      rr_mw_lw_derivative_lag_sequence_den_coeff_realrooted_sign_auto using
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
          den_nonzero := rr_mw_active_den_all_term,
          deriv_coeff_eq := rr_mw_coeff_all_term,
          lag_coeff_eq := rr_mw_coeff_all_term,
          raw_recurrence := $hraw,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_mw_lw_derivative_lag_sequence_den_coeff_realrooted_sign_auto using
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
          den_nonzero := rr_mw_active_den_all_term,
          deriv_coeff_eq := $hcoeffV,
          lag_coeff_eq := $hcoeffW,
          raw_recurrence := $hraw,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_mw_lw_derivative_lag_sequence_den_coeff_realrooted_sign_auto using
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
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_mw_lw_derivative_lag_sequence_den_coeff_of_nonneg_coeffs
            (V := $V) (W := $W) (b := $b) (c := $cV) (e := $e) (a := $cW)
            (d := $d)
            $hbase $hpos $hnonneg $hdeg_two
            rr_mw_active_nonneg
            rr_mw_active_nonneg
            (rr_mw_root_sign_seq)
            (rr_mw_root_sign_seq)
            $hden $hcoeffV $hcoeffW
            (rr_mw_raw_recurrence_seq $hraw)
            $hdeg_succ $hno))
  | `(tactic|
      rr_mw_lw_derivative_lag_sequence_den_coeff_window_sign_auto using
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
          den_nonzero := rr_mw_active_den_all_term,
          deriv_coeff_eq := rr_mw_coeff_all_term,
          lag_coeff_eq := rr_mw_coeff_all_term,
          raw_recurrence := $hraw,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_mw_lw_derivative_lag_sequence_den_coeff_window_sign_auto using
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
          den_nonzero := rr_mw_active_den_all_term,
          deriv_coeff_eq := $hcoeffV,
          lag_coeff_eq := $hcoeffW,
          raw_recurrence := $hraw,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_mw_lw_derivative_lag_sequence_den_coeff_window_sign_auto using
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
        exact
          RealRooted.prec_mw_lw_derivative_lag_sequence_den_coeff_of_root_window
            (V := $V) (W := $W) (b := $b) (c := $cV) (e := $e) (a := $cW)
            (d := $d)
            $hbase $hpos $hdeg_two
            rr_mw_active_nonneg
            rr_mw_active_nonneg
            $hroot_lower $hroot_upper
            (by
              intro n r hr hroot_window_lower hroot_window_upper
              rr_mw_root_window_linear_facts
              rr_sign)
            (by
              intro n r hr hroot_window_lower hroot_window_upper
              rr_mw_root_window_linear_facts
              rr_sign)
            $hden $hcoeffV $hcoeffW
            (rr_mw_raw_recurrence_seq $hraw)
            $hdeg_succ $hno)
  | `(tactic|
      rr_mw_lw_derivative_lag_sequence_den_coeff_realrooted_window_sign_auto using
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
          den_nonzero := rr_mw_active_den_all_term,
          deriv_coeff_eq := rr_mw_coeff_all_term,
          lag_coeff_eq := rr_mw_coeff_all_term,
          raw_recurrence := $hraw,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_mw_lw_derivative_lag_sequence_den_coeff_realrooted_window_sign_auto using
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
          den_nonzero := rr_mw_active_den_all_term,
          deriv_coeff_eq := $hcoeffV,
          lag_coeff_eq := $hcoeffW,
          raw_recurrence := $hraw,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_mw_lw_derivative_lag_sequence_den_coeff_realrooted_window_sign_auto using
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
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_mw_lw_derivative_lag_sequence_den_coeff_of_root_window
            (V := $V) (W := $W) (b := $b) (c := $cV) (e := $e) (a := $cW)
            (d := $d)
            $hbase $hpos $hdeg_two
            rr_mw_active_nonneg
            rr_mw_active_nonneg
            $hroot_lower $hroot_upper
            (by
              intro n r hr hroot_window_lower hroot_window_upper
              rr_mw_root_window_linear_facts
              rr_sign)
            (by
              intro n r hr hroot_window_lower hroot_window_upper
              rr_mw_root_window_linear_facts
              rr_sign)
            $hden $hcoeffV $hcoeffW
            (rr_mw_raw_recurrence_seq $hraw)
            $hdeg_succ $hno))
  | `(tactic|
      rr_mw_derivative_nonpos_sequence_den_coeff_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        coeff := $c:term,
        coeff_nonneg := $hc:term,
        coeff_nonpos_of_nonpos := $hV:term,
        den_nonzero := $hden:term,
        coeff_eq := $hcoeff:term,
        raw_recurrence := $hraw:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        exact
          RealRooted.prec_mw_derivative_nonpos_sequence_den_coeff_of_nonneg_coeffs
            (c := $c) $hbase $hpos $hnonneg $hdeg_two $hc $hV $hden $hcoeff
            $hraw $hdeg_lo $hdeg_hi)
  | `(tactic|
      rr_mw_derivative_nonpos_sequence_den_coeff_nonneg_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        coeff := $c:term,
        coeff_nonpos_of_nonpos := $hV:term,
        den_nonzero := $hden:term,
        coeff_eq := $hcoeff:term,
        raw_recurrence := $hraw:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        exact
          RealRooted.prec_mw_derivative_nonpos_sequence_den_coeff_of_nonneg_coeffs
            (c := $c) $hbase $hpos $hnonneg $hdeg_two rr_mw_active_nonneg
            $hV $hden $hcoeff $hraw $hdeg_lo $hdeg_hi)
  | `(tactic|
      rr_mw_derivative_nonpos_sequence_den_coeff_nonneg_sign_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        coeff := $c:term,
        raw_recurrence := $hraw:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        rr_mw_derivative_nonpos_sequence_den_coeff_nonneg_sign_auto using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          degree_two := $hdeg_two,
          coeff := $c,
          den_nonzero := rr_mw_active_den_all_term,
          coeff_eq := rr_mw_coeff_all_term,
          raw_recurrence := $hraw,
          degree_lower := $hdeg_lo,
          degree_upper := $hdeg_hi)
  | `(tactic|
      rr_mw_derivative_nonpos_sequence_den_coeff_nonneg_sign_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        coeff := $c:term,
        den_nonzero := $hden:term,
        coeff_eq := $hcoeff:term,
        raw_recurrence := $hraw:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        exact
          RealRooted.prec_mw_derivative_nonpos_sequence_den_coeff_of_nonneg_coeffs
            (c := $c) $hbase $hpos $hnonneg $hdeg_two
            rr_mw_active_nonneg
            (rr_mw_root_sign_seq)
            $hden $hcoeff $hraw $hdeg_lo $hdeg_hi)
  | `(tactic|
      rr_mw_derivative_nonpos_sequence_den_coeff_nonneg_sign_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        coeff := $c:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg:term) =>
      `(tactic|
        rr_mw_derivative_nonpos_sequence_den_coeff_nonneg_sign_auto using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          degree_two := $hdeg_two,
          coeff := $c,
          den_nonzero := rr_mw_active_den_all_term,
          coeff_eq := rr_mw_coeff_all_term,
          raw_recurrence := $hraw,
          degree_succ := $hdeg)
  | `(tactic|
      rr_mw_derivative_nonpos_sequence_den_coeff_nonneg_sign_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        coeff := $c:term,
        den_nonzero := $hden:term,
        coeff_eq := $hcoeff:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg:term) =>
      `(tactic|
        rr_mw_derivative_nonpos_sequence_den_coeff_nonneg_sign_auto using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          degree_two := $hdeg_two,
          coeff := $c,
          den_nonzero := $hden,
          coeff_eq := $hcoeff,
          raw_recurrence := $hraw,
          degree_lower := rr_mw_degree_seq $hdeg,
          degree_upper := rr_mw_degree_seq $hdeg)
  | `(tactic|
      rr_mw_derivative_nonpos_sequence_den_coeff_nonneg_sign_auto_split using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        deriv_factor := $V:term,
        coeff := $c:term,
        den := $d:term,
        raw_coeff := $b:term,
        raw_recurrence := $hraw:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        rr_mw_derivative_nonpos_sequence_den_coeff_nonneg_sign_auto_split using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          degree_two := $hdeg_two,
          deriv_factor := $V,
          coeff := $c,
          den := $d,
          raw_coeff := $b,
          den_nonzero := rr_mw_active_den_all_term,
          coeff_eq := rr_mw_coeff_all_term,
          raw_recurrence := $hraw,
          degree_lower := $hdeg_lo,
          degree_upper := $hdeg_hi)
  | `(tactic|
      rr_mw_derivative_nonpos_sequence_den_coeff_nonneg_sign_auto_split using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        deriv_factor := $V:term,
        coeff := $c:term,
        den := $d:term,
        raw_coeff := $b:term,
        den_nonzero := $hden:term,
        coeff_eq := $hcoeff:term,
        raw_recurrence := $hraw:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        exact
          RealRooted.prec_mw_derivative_nonpos_sequence_den_coeff_of_nonneg_coeffs
            (V := $V) (b := $b) (c := $c) (d := $d)
            $hbase $hpos $hnonneg $hdeg_two
            rr_mw_active_nonneg
            (rr_mw_root_sign_seq)
            $hden $hcoeff
            (rr_mw_raw_recurrence_seq $hraw)
            $hdeg_lo $hdeg_hi)
  | `(tactic|
      rr_mw_derivative_nonpos_sequence_den_coeff_nonneg_sign_auto_split using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        deriv_factor := $V:term,
        coeff := $c:term,
        den := $d:term,
        raw_coeff := $b:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg:term) =>
      `(tactic|
        rr_mw_derivative_nonpos_sequence_den_coeff_nonneg_sign_auto_split using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          degree_two := $hdeg_two,
          deriv_factor := $V,
          coeff := $c,
          den := $d,
          raw_coeff := $b,
          den_nonzero := rr_mw_active_den_all_term,
          coeff_eq := rr_mw_coeff_all_term,
          raw_recurrence := $hraw,
          degree_succ := $hdeg)
  | `(tactic|
      rr_mw_derivative_nonpos_sequence_den_coeff_nonneg_sign_auto_split using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        deriv_factor := $V:term,
        coeff := $c:term,
        den := $d:term,
        raw_coeff := $b:term,
        den_nonzero := $hden:term,
        coeff_eq := $hcoeff:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg:term) =>
      `(tactic|
        rr_mw_derivative_nonpos_sequence_den_coeff_nonneg_sign_auto_split using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          degree_two := $hdeg_two,
          deriv_factor := $V,
          coeff := $c,
          den := $d,
          raw_coeff := $b,
          den_nonzero := $hden,
          coeff_eq := $hcoeff,
          raw_recurrence := $hraw,
          degree_lower := rr_mw_degree_seq $hdeg,
          degree_upper := rr_mw_degree_seq $hdeg)
  | `(tactic|
      rr_mw_derivative_nonpos_sequence_den_coeff_realrooted_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        coeff := $c:term,
        coeff_nonneg := $hc:term,
        coeff_nonpos_of_nonpos := $hV:term,
        den_nonzero := $hden:term,
        coeff_eq := $hcoeff:term,
        raw_recurrence := $hraw:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_mw_derivative_nonpos_sequence_den_coeff_of_nonneg_coeffs
            (c := $c) $hbase $hpos $hnonneg $hdeg_two $hc $hV $hden $hcoeff
            $hraw $hdeg_lo $hdeg_hi))
  | `(tactic|
      rr_mw_derivative_nonpos_sequence_den_coeff_realrooted_nonneg_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        coeff := $c:term,
        coeff_nonpos_of_nonpos := $hV:term,
        den_nonzero := $hden:term,
        coeff_eq := $hcoeff:term,
        raw_recurrence := $hraw:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_mw_derivative_nonpos_sequence_den_coeff_of_nonneg_coeffs
            (c := $c) $hbase $hpos $hnonneg $hdeg_two rr_mw_active_nonneg
            $hV $hden $hcoeff $hraw $hdeg_lo $hdeg_hi))
  | `(tactic|
      rr_mw_derivative_nonpos_sequence_den_coeff_realrooted_nonneg_sign_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        coeff := $c:term,
        raw_recurrence := $hraw:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        rr_mw_derivative_nonpos_sequence_den_coeff_realrooted_nonneg_sign_auto using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          degree_two := $hdeg_two,
          coeff := $c,
          den_nonzero := rr_mw_active_den_all_term,
          coeff_eq := rr_mw_coeff_all_term,
          raw_recurrence := $hraw,
          degree_lower := $hdeg_lo,
          degree_upper := $hdeg_hi)
  | `(tactic|
      rr_mw_derivative_nonpos_sequence_den_coeff_realrooted_nonneg_sign_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        coeff := $c:term,
        den_nonzero := $hden:term,
        coeff_eq := $hcoeff:term,
        raw_recurrence := $hraw:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_mw_derivative_nonpos_sequence_den_coeff_of_nonneg_coeffs
            (c := $c) $hbase $hpos $hnonneg $hdeg_two
            rr_mw_active_nonneg
            (rr_mw_root_sign_seq)
            $hden $hcoeff $hraw $hdeg_lo $hdeg_hi))
  | `(tactic|
      rr_mw_derivative_nonpos_sequence_den_coeff_realrooted_nonneg_sign_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        coeff := $c:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg:term) =>
      `(tactic|
        rr_mw_derivative_nonpos_sequence_den_coeff_realrooted_nonneg_sign_auto using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          degree_two := $hdeg_two,
          coeff := $c,
          den_nonzero := rr_mw_active_den_all_term,
          coeff_eq := rr_mw_coeff_all_term,
          raw_recurrence := $hraw,
          degree_succ := $hdeg)
  | `(tactic|
      rr_mw_derivative_nonpos_sequence_den_coeff_realrooted_nonneg_sign_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        coeff := $c:term,
        den_nonzero := $hden:term,
        coeff_eq := $hcoeff:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg:term) =>
      `(tactic|
        rr_mw_derivative_nonpos_sequence_den_coeff_realrooted_nonneg_sign_auto using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          degree_two := $hdeg_two,
          coeff := $c,
          den_nonzero := $hden,
          coeff_eq := $hcoeff,
          raw_recurrence := $hraw,
          degree_lower := rr_mw_degree_seq $hdeg,
          degree_upper := rr_mw_degree_seq $hdeg)
  | `(tactic|
      rr_mw_derivative_nonpos_sequence_den_coeff_realrooted_nonneg_sign_auto_split using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        deriv_factor := $V:term,
        coeff := $c:term,
        den := $d:term,
        raw_coeff := $b:term,
        raw_recurrence := $hraw:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        rr_mw_derivative_nonpos_sequence_den_coeff_realrooted_nonneg_sign_auto_split using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          degree_two := $hdeg_two,
          deriv_factor := $V,
          coeff := $c,
          den := $d,
          raw_coeff := $b,
          den_nonzero := rr_mw_active_den_all_term,
          coeff_eq := rr_mw_coeff_all_term,
          raw_recurrence := $hraw,
          degree_lower := $hdeg_lo,
          degree_upper := $hdeg_hi)
  | `(tactic|
      rr_mw_derivative_nonpos_sequence_den_coeff_realrooted_nonneg_sign_auto_split using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        deriv_factor := $V:term,
        coeff := $c:term,
        den := $d:term,
        raw_coeff := $b:term,
        den_nonzero := $hden:term,
        coeff_eq := $hcoeff:term,
        raw_recurrence := $hraw:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_mw_derivative_nonpos_sequence_den_coeff_of_nonneg_coeffs
            (V := $V) (b := $b) (c := $c) (d := $d)
            $hbase $hpos $hnonneg $hdeg_two
            rr_mw_active_nonneg
            (rr_mw_root_sign_seq)
            $hden $hcoeff
            (rr_mw_raw_recurrence_seq $hraw)
            $hdeg_lo $hdeg_hi))

end Tactic
end RealRooted
