import RealRooted.Tactic.MaWang.Denominator

/-!
# Ma--Wang tactic factor rules

Elaboration rules for specialized derivative-factor sequence certificates.
-/

namespace RealRooted
namespace Tactic

macro_rules
  | `(tactic|
      rr_mw_derivative_nonpos_nonneg_sequence_on_roots using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        coeff_nonpos_on_roots := $hV:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        exact
          RealRooted.MaWang.strictInterl_derivative_nonpos_sequence_of_nonneg_coeffs_on_roots
            $hbase $hpos $hnonneg $hV $hrec $hdeg_lo $hdeg_hi)
  | `(tactic|
      rr_mw_derivative_nonpos_nonneg_sequence_on_roots_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        coeff_nonpos_on_roots := $hV:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.MaWang.isRealRooted_of_derivative_nonpos_sequence_of_nonneg_coeffs_on_roots
            $hbase $hpos $hnonneg $hV $hrec $hdeg_lo $hdeg_hi))
  | `(tactic|
      rr_mw_derivative_X_mul_sequence_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        factor_nonneg := $hQ:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        exact RealRooted.MaWang.strictInterl_derivative_X_mul_sequence_of_nonneg_coeffs
          $hbase $hpos $hnonneg $hQ $hrec $hdeg_lo $hdeg_hi)
  | `(tactic|
      rr_mw_derivative_X_mul_sequence_realrooted_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        factor_nonneg := $hQ:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.MaWang.isRealRooted_of_derivative_X_mul_sequence_of_nonneg_coeffs
            $hbase $hpos $hnonneg $hQ $hrec $hdeg_lo $hdeg_hi))
  | `(tactic|
      rr_mw_derivative_X_sequence_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        exact RealRooted.MaWang.strictInterl_derivative_X_sequence_of_nonneg_coeffs
          $hbase $hpos $hnonneg $hrec $hdeg_lo $hdeg_hi)
  | `(tactic|
      rr_mw_derivative_X_sequence_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg:term) =>
      `(tactic|
        rr_mw_derivative_X_sequence_nonneg using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          recurrence := $hrec,
          degree_lower := rr_mw_tail_degree_seq $hdeg,
          degree_upper := rr_mw_tail_degree_seq $hdeg)
  | `(tactic|
      rr_mw_derivative_X_sequence_realrooted_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.MaWang.isRealRooted_of_derivative_X_sequence_of_nonneg_coeffs
            $hbase $hpos $hnonneg $hrec $hdeg_lo $hdeg_hi))
  | `(tactic|
      rr_mw_derivative_X_sequence_realrooted_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg:term) =>
      `(tactic|
        rr_mw_derivative_X_sequence_realrooted_nonneg using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          recurrence := $hrec,
          degree_lower := rr_mw_tail_degree_seq $hdeg,
          degree_upper := rr_mw_tail_degree_seq $hdeg)
  | `(tactic|
      rr_mw_derivative_C_mul_X_sequence_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        coeff_nonneg := $hc:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        exact RealRooted.MaWang.strictInterl_derivative_C_mul_X_sequence_of_nonneg_coeffs
          $hbase $hpos $hnonneg $hc $hrec $hdeg_lo $hdeg_hi)
  | `(tactic|
      rr_mw_derivative_C_mul_X_sequence_nonneg_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        exact RealRooted.MaWang.strictInterl_derivative_C_mul_X_sequence_of_nonneg_coeffs
          $hbase $hpos $hnonneg
          rr_mw_active_nonneg $hrec $hdeg_lo $hdeg_hi)
  | `(tactic|
      rr_mw_derivative_C_mul_X_sequence_realrooted_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        coeff_nonneg := $hc:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.MaWang.isRealRooted_of_derivative_C_mul_X_sequence_of_nonneg_coeffs
            $hbase $hpos $hnonneg $hc $hrec $hdeg_lo $hdeg_hi))
  | `(tactic|
      rr_mw_derivative_C_mul_X_sequence_realrooted_nonneg_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.MaWang.isRealRooted_of_derivative_C_mul_X_sequence_of_nonneg_coeffs
            $hbase $hpos $hnonneg
            rr_mw_active_nonneg $hrec $hdeg_lo $hdeg_hi))
  | `(tactic|
      rr_mw_derivative_C_mul_X_mul_sequence_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        coeff_nonneg := $hc:term,
        factor_nonneg := $hQ:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        exact RealRooted.MaWang.strictInterl_derivative_C_mul_X_mul_sequence_of_nonneg_coeffs
          $hbase $hpos $hnonneg $hc $hQ $hrec $hdeg_lo $hdeg_hi)
  | `(tactic|
      rr_mw_derivative_C_mul_X_mul_sequence_nonneg_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        factor_nonneg := $hQ:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        exact RealRooted.MaWang.strictInterl_derivative_C_mul_X_mul_sequence_of_nonneg_coeffs
          $hbase $hpos $hnonneg
          rr_mw_active_nonneg $hQ $hrec $hdeg_lo $hdeg_hi)
  | `(tactic|
      rr_mw_derivative_C_mul_X_mul_sequence_realrooted_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        coeff_nonneg := $hc:term,
        factor_nonneg := $hQ:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.MaWang.isRealRooted_of_derivative_C_mul_X_mul_sequence_of_nonneg_coeffs
            $hbase $hpos $hnonneg $hc $hQ $hrec $hdeg_lo $hdeg_hi))
  | `(tactic|
      rr_mw_derivative_C_mul_X_mul_sequence_realrooted_nonneg_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        factor_nonneg := $hQ:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.MaWang.isRealRooted_of_derivative_C_mul_X_mul_sequence_of_nonneg_coeffs
            $hbase $hpos $hnonneg
            rr_mw_active_nonneg $hQ $hrec $hdeg_lo $hdeg_hi))
  | `(tactic|
      rr_mw_derivative_C_mul_X_mul_sequence_den_coeff_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        coeff := $c:term,
        coeff_nonneg := $hc:term,
        factor_nonneg := $hQ:term,
        den_nonzero := $hden:term,
        coeff_eq := $hcoeff:term,
        raw_recurrence := $hraw:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        exact
          RealRooted.MaWang.strictInterl_derivative_C_mul_X_mul_sequence_den_coeff_of_nonneg_coeffs
            (c := $c) $hbase $hpos $hnonneg $hc $hQ $hden $hcoeff
            $hraw $hdeg_lo $hdeg_hi)
  | `(tactic|
      rr_mw_derivative_C_mul_X_mul_sequence_den_coeff_nonneg_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        coeff := $c:term,
        factor_nonneg := $hQ:term,
        den_nonzero := $hden:term,
        coeff_eq := $hcoeff:term,
        raw_recurrence := $hraw:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        exact
          RealRooted.MaWang.strictInterl_derivative_C_mul_X_mul_sequence_den_coeff_of_nonneg_coeffs
            (c := $c) $hbase $hpos $hnonneg rr_mw_active_nonneg
            $hQ $hden $hcoeff $hraw $hdeg_lo $hdeg_hi)
  | `(tactic|
      rr_mw_derivative_C_mul_X_mul_sequence_den_coeff_realrooted_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        coeff := $c:term,
        coeff_nonneg := $hc:term,
        factor_nonneg := $hQ:term,
        den_nonzero := $hden:term,
        coeff_eq := $hcoeff:term,
        raw_recurrence := $hraw:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (MaWang.isRealRooted_of_derivative_C_mul_X_mul_sequence_den_coeff_of_nonneg_coeffs
            (c := $c) $hbase $hpos $hnonneg $hc $hQ $hden $hcoeff
            $hraw $hdeg_lo $hdeg_hi))
  | `(tactic|
      rr_mw_derivative_C_mul_X_mul_sequence_den_coeff_realrooted_nonneg_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        coeff := $c:term,
        factor_nonneg := $hQ:term,
        den_nonzero := $hden:term,
        coeff_eq := $hcoeff:term,
        raw_recurrence := $hraw:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (MaWang.isRealRooted_of_derivative_C_mul_X_mul_sequence_den_coeff_of_nonneg_coeffs
            (c := $c) $hbase $hpos $hnonneg rr_mw_active_nonneg
            $hQ $hden $hcoeff $hraw $hdeg_lo $hdeg_hi))
  | `(tactic|
      rr_mw_derivative_X_one_add_sequence_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        exact
          RealRooted.MaWang.strictInterl_derivative_X_mul_one_add_X_sequence_of_nonneg_coeffs
            $hbase $hpos $hnonneg $hroot_lower $hrec $hdeg_lo $hdeg_hi)
  | `(tactic|
      rr_mw_derivative_X_one_add_sequence_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg:term) =>
      `(tactic|
        rr_mw_derivative_X_one_add_sequence_nonneg using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          root_lower := $hroot_lower,
          recurrence := $hrec,
          degree_lower := rr_mw_degree_seq $hdeg,
          degree_upper := rr_mw_degree_seq $hdeg)
  | `(tactic|
      rr_mw_derivative_X_one_add_sequence_realrooted_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.MaWang.isRealRooted_of_derivative_X_mul_one_add_X_sequence_of_nonneg_coeffs
            $hbase $hpos $hnonneg $hroot_lower $hrec $hdeg_lo $hdeg_hi))
  | `(tactic|
      rr_mw_derivative_C_mul_X_one_add_X_sequence_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        coeff_nonneg := $hc:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        exact
          RealRooted.MaWang.strictInterl_derivative_C_mul_X_mul_one_add_X_sequence_of_nonneg_coeffs
            $hbase $hpos $hnonneg $hc $hroot_lower
            $hrec $hdeg_lo $hdeg_hi)
  | `(tactic|
      rr_mw_derivative_C_mul_X_one_add_X_sequence_nonneg_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        rr_mw_refine_active_nonneg_seq
          (RealRooted.MaWang.strictInterl_derivative_C_mul_X_mul_one_add_X_sequence_of_nonneg_coeffs
            $hbase $hpos $hnonneg ?_ $hroot_lower
            $hrec $hdeg_lo $hdeg_hi))
  | `(tactic|
      rr_mw_derivative_C_mul_X_one_add_X_sequence_nonneg_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg:term) =>
      `(tactic|
        rr_mw_derivative_C_mul_X_one_add_X_sequence_nonneg_auto using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          root_lower := $hroot_lower,
          recurrence := $hrec,
          degree_lower := rr_mw_degree_seq $hdeg,
          degree_upper := rr_mw_degree_seq $hdeg)
  | `(tactic|
      rr_mw_derivative_C_mul_X_one_add_X_sequence_realrooted_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        coeff_nonneg := $hc:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (MaWang.isRealRooted_of_derivative_C_mul_X_mul_one_add_X_sequence_of_nonneg_coeffs
            $hbase $hpos $hnonneg $hc $hroot_lower
            $hrec $hdeg_lo $hdeg_hi))
  | `(tactic|
      rr_mw_derivative_C_mul_X_one_add_X_sequence_realrooted_nonneg_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        rr_mw_exact_realrooted_active_nonneg_seq
          (MaWang.isRealRooted_of_derivative_C_mul_X_mul_one_add_X_sequence_of_nonneg_coeffs
            $hbase $hpos $hnonneg ?_ $hroot_lower
            $hrec $hdeg_lo $hdeg_hi))
  | `(tactic|
      rr_mw_derivative_C_mul_X_one_add_X_sequence_realrooted_nonneg_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg:term) =>
      `(tactic|
        rr_mw_derivative_C_mul_X_one_add_X_sequence_realrooted_nonneg_auto using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          root_lower := $hroot_lower,
          recurrence := $hrec,
          degree_lower := rr_mw_degree_seq $hdeg,
          degree_upper := rr_mw_degree_seq $hdeg)
  | `(tactic|
      rr_mw_derivative_neg_X_one_add_outer_sequence using
        base := $hbase:term,
        pos_lc := $hpos:term,
        coeff_nonneg := $hc:term,
        root_upper := $hroot_upper:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        exact RealRooted.MaWang.strictInterl_derivative_neg_C_mul_X_mul_one_add_X_sequence
          $hbase $hpos $hc $hroot_upper $hrec $hdeg_lo $hdeg_hi)
  | `(tactic|
      rr_mw_derivative_neg_X_one_add_outer_sequence_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        root_upper := $hroot_upper:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        rr_mw_refine_active_nonneg_seq
          (RealRooted.MaWang.strictInterl_derivative_neg_C_mul_X_mul_one_add_X_sequence
            $hbase $hpos ?_ $hroot_upper $hrec $hdeg_lo $hdeg_hi))
  | `(tactic|
      rr_mw_derivative_neg_X_one_add_outer_sequence_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        coeff_nonneg := $hc:term,
        root_upper := $hroot_upper:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.MaWang.isRealRooted_of_derivative_neg_C_mul_X_mul_one_add_X_sequence
            $hbase $hpos $hc $hroot_upper $hrec $hdeg_lo $hdeg_hi))
  | `(tactic|
      rr_mw_derivative_neg_X_one_add_outer_sequence_realrooted_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        root_upper := $hroot_upper:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        rr_mw_exact_realrooted_active_nonneg_seq
          (RealRooted.MaWang.isRealRooted_of_derivative_neg_C_mul_X_mul_one_add_X_sequence
            $hbase $hpos ?_ $hroot_upper $hrec $hdeg_lo $hdeg_hi))
  | `(tactic|
      rr_mw_derivative_C_mul_X_one_sub_X_sequence using
        base := $hbase:term,
        pos_lc := $hpos:term,
        coeff_nonneg := $hc:term,
        roots_nonpos := $hroots:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        exact RealRooted.MaWang.strictInterl_derivative_C_mul_X_mul_one_sub_X_sequence
          $hbase $hpos $hc $hroots $hrec $hdeg_lo $hdeg_hi)
  | `(tactic|
      rr_mw_derivative_C_mul_X_one_sub_X_sequence_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        roots_nonpos := $hroots:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        rr_mw_refine_active_nonneg_seq
          (RealRooted.MaWang.strictInterl_derivative_C_mul_X_mul_one_sub_X_sequence
            $hbase $hpos ?_ $hroots $hrec $hdeg_lo $hdeg_hi))
  | `(tactic|
      rr_mw_derivative_C_mul_X_one_sub_X_sequence_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        roots_nonpos := $hroots:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg:term) =>
      `(tactic|
        rr_mw_derivative_C_mul_X_one_sub_X_sequence_auto using
          base := $hbase,
          pos_lc := $hpos,
          roots_nonpos := $hroots,
          recurrence := $hrec,
          degree_lower := rr_mw_degree_seq $hdeg,
          degree_upper := rr_mw_degree_seq $hdeg)
  | `(tactic|
      rr_mw_derivative_C_mul_X_one_sub_X_sequence_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        coeff_nonneg := $hc:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        exact
          RealRooted.MaWang.strictInterl_derivative_C_mul_X_mul_one_sub_X_sequence_of_nonneg_coeffs
            $hbase $hpos $hnonneg $hc $hrec $hdeg_lo $hdeg_hi)
  | `(tactic|
      rr_mw_derivative_C_mul_X_one_sub_X_sequence_nonneg_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        rr_mw_refine_active_nonneg_seq
          (RealRooted.MaWang.strictInterl_derivative_C_mul_X_mul_one_sub_X_sequence_of_nonneg_coeffs
            $hbase $hpos $hnonneg ?_ $hrec $hdeg_lo $hdeg_hi))
  | `(tactic|
      rr_mw_derivative_C_mul_X_one_sub_X_sequence_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        coeff_nonneg := $hc:term,
        roots_nonpos := $hroots:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.MaWang.isRealRooted_of_derivative_C_mul_X_mul_one_sub_X_sequence
            $hbase $hpos $hc $hroots $hrec $hdeg_lo $hdeg_hi))
  | `(tactic|
      rr_mw_derivative_C_mul_X_one_sub_X_sequence_realrooted_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        roots_nonpos := $hroots:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        rr_mw_exact_realrooted_active_nonneg_seq
          (RealRooted.MaWang.isRealRooted_of_derivative_C_mul_X_mul_one_sub_X_sequence
            $hbase $hpos ?_ $hroots $hrec $hdeg_lo $hdeg_hi))
  | `(tactic|
      rr_mw_derivative_C_mul_X_one_sub_X_sequence_realrooted_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        coeff_nonneg := $hc:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (MaWang.isRealRooted_of_derivative_C_mul_X_mul_one_sub_X_sequence_of_nonneg_coeffs
            $hbase $hpos $hnonneg $hc $hrec $hdeg_lo $hdeg_hi))
  | `(tactic|
      rr_mw_derivative_C_mul_X_one_sub_X_sequence_realrooted_nonneg_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        rr_mw_exact_realrooted_active_nonneg_seq
          (MaWang.isRealRooted_of_derivative_C_mul_X_mul_one_sub_X_sequence_of_nonneg_coeffs
            $hbase $hpos $hnonneg ?_ $hrec $hdeg_lo $hdeg_hi))

end Tactic
end RealRooted
