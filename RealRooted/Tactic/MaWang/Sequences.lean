import RealRooted.Tactic.MaWang.Steps

/-!
# Ma--Wang tactic sequence rules

Elaboration rules for ordinary derivative and derivative-plus-lag sequences.
-/

namespace RealRooted
namespace Tactic

macro_rules
  | `(tactic|
      rr_mw_derivative_neg_const using
        splits := $hf:term,
        degree_two := $hdegf:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term,
        target_pos_lc := $hF_pos:term,
        source_pos_lc := $hf_pos:term,
        coeff_nonneg := $hc:term) =>
      `(tactic|
        exact RealRooted.prec_mw_derivative_neg_const
          $hf $hdegf $hdeg_lo $hdeg_hi $hF_pos $hf_pos $hc)
  | `(tactic|
      rr_mw_derivative_neg_const_auto using
        splits := $hf:term,
        degree_two := $hdegf:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term,
        target_pos_lc := $hF_pos:term,
        source_pos_lc := $hf_pos:term) =>
      `(tactic|
        rr_refine_then
          (RealRooted.prec_mw_derivative_neg_const
            $hf $hdegf $hdeg_lo $hdeg_hi $hF_pos $hf_pos ?_)
          with rr_mw_active_nonneg_at 0)
  | `(tactic|
      rr_mw_derivative_neg_X_sq using
        splits := $hf:term,
        degree_two := $hdegf:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term,
        target_pos_lc := $hF_pos:term,
        source_pos_lc := $hf_pos:term,
        coeff_nonneg := $hc:term) =>
      `(tactic|
        exact RealRooted.prec_mw_derivative_neg_C_mul_X_sq
          $hf $hdegf $hdeg_lo $hdeg_hi $hF_pos $hf_pos $hc)
  | `(tactic|
      rr_mw_derivative_neg_X_sq_auto using
        splits := $hf:term,
        degree_two := $hdegf:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term,
        target_pos_lc := $hF_pos:term,
        source_pos_lc := $hf_pos:term) =>
      `(tactic|
        rr_refine_then
          (RealRooted.prec_mw_derivative_neg_C_mul_X_sq
            $hf $hdegf $hdeg_lo $hdeg_hi $hF_pos $hf_pos ?_)
          with rr_mw_active_nonneg_at 0)
  | `(tactic|
      rr_mw_derivative_nonpos_sequence using
        base := $hbase:term,
        pos_lc := $hpos:term,
        degree_two := $hdeg_two:term,
        coeff_nonpos := $hV:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        exact RealRooted.prec_mw_derivative_nonpos_sequence
          $hbase $hpos $hdeg_two $hV $hrec $hdeg_lo $hdeg_hi)
  | `(tactic|
      rr_mw_derivative_nonpos_sequence using recurrence := $hrec:term) =>
      `(tactic|
        rr_refine_then
          (RealRooted.prec_mw_derivative_nonpos_sequence
            ?_ ?_ ?_ ?_ $hrec ?_ ?_)
          with rr_lookup)
  | `(tactic|
      rr_mw_derivative_nonpos_sequence_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        degree_two := $hdeg_two:term,
        coeff_nonpos := $hV:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_mw_derivative_nonpos_sequence
            $hbase $hpos $hdeg_two $hV $hrec $hdeg_lo $hdeg_hi))
  | `(tactic|
      rr_mw_derivative_nonpos_sequence_realrooted using
        recurrence := $hrec:term) =>
      `(tactic|
        rr_exact_realrooted_refine_then
          (RealRooted.isRealRooted_of_mw_derivative_nonpos_sequence
            ?_ ?_ ?_ ?_ $hrec ?_ ?_)
          with rr_lookup)
  | `(tactic|
      rr_mw_derivative_global_nonpos_sequence_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        degree_two := $hdeg_two:term,
        deriv_factor := $V:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        exact RealRooted.prec_mw_derivative_nonpos_sequence
          (V := $V) $hbase $hpos $hdeg_two (by
            intro n r hr
            rr_sign) $hrec $hdeg_lo $hdeg_hi)
  | `(tactic|
      rr_mw_derivative_global_nonpos_sequence_realrooted_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        degree_two := $hdeg_two:term,
        deriv_factor := $V:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_mw_derivative_nonpos_sequence
            (V := $V) $hbase $hpos $hdeg_two (by
              intro n r hr
              rr_sign) $hrec $hdeg_lo $hdeg_hi))
  | `(tactic|
      rr_mw_derivative_neg_const_sequence using
        base := $hbase:term,
        pos_lc := $hpos:term,
        degree_two := $hdeg_two:term,
        coeff_nonneg := $hc:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        rr_mw_two_variants
          (RealRooted.prec_mw_derivative_neg_const_sequence
            $hbase $hpos $hdeg_two $hc $hrec $hdeg_lo $hdeg_hi),
          (RealRooted.prec_mw_derivative_neg_C_sequence
            $hbase $hpos $hdeg_two $hc $hrec $hdeg_lo $hdeg_hi))
  | `(tactic|
      rr_mw_derivative_neg_const_sequence_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        degree_two := $hdeg_two:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        rr_mw_two_variants
          (RealRooted.prec_mw_derivative_neg_const_sequence
            $hbase $hpos $hdeg_two rr_mw_active_nonneg
            $hrec $hdeg_lo $hdeg_hi),
          (RealRooted.prec_mw_derivative_neg_C_sequence
            $hbase $hpos $hdeg_two rr_mw_active_nonneg
            $hrec $hdeg_lo $hdeg_hi))
  | `(tactic|
      rr_mw_derivative_neg_const_sequence_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        degree_two := $hdeg_two:term,
        coeff_nonneg := $hc:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        rr_mw_two_variants
          (RealRooted.isRealRooted_of_mw_derivative_neg_const_sequence
            $hbase $hpos $hdeg_two $hc $hrec $hdeg_lo $hdeg_hi),
          (RealRooted.isRealRooted_of_mw_derivative_neg_C_sequence
            $hbase $hpos $hdeg_two $hc $hrec $hdeg_lo $hdeg_hi))
  | `(tactic|
      rr_mw_derivative_neg_const_sequence_realrooted_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        degree_two := $hdeg_two:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        rr_mw_two_variants
          (RealRooted.isRealRooted_of_mw_derivative_neg_const_sequence
            $hbase $hpos $hdeg_two rr_mw_active_nonneg
            $hrec $hdeg_lo $hdeg_hi),
          (RealRooted.isRealRooted_of_mw_derivative_neg_C_sequence
            $hbase $hpos $hdeg_two rr_mw_active_nonneg
            $hrec $hdeg_lo $hdeg_hi))
  | `(tactic|
      rr_mw_derivative_neg_X_sq_sequence using
        base := $hbase:term,
        pos_lc := $hpos:term,
        degree_two := $hdeg_two:term,
        coeff_nonneg := $hc:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        rr_mw_three_variants
          (RealRooted.prec_mw_derivative_neg_C_mul_X_sq_sequence
            $hbase $hpos $hdeg_two $hc $hrec $hdeg_lo $hdeg_hi),
          (RealRooted.prec_mw_derivative_C_neg_mul_X_sq_sequence
            $hbase $hpos $hdeg_two $hc $hrec $hdeg_lo $hdeg_hi),
          (RealRooted.prec_mw_derivative_neg_C_mul_X_sq_product_sequence
            $hbase $hpos $hdeg_two $hc $hrec $hdeg_lo $hdeg_hi))
  | `(tactic|
      rr_mw_derivative_neg_X_sq_sequence_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        degree_two := $hdeg_two:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        rr_mw_three_variants
          (RealRooted.prec_mw_derivative_neg_C_mul_X_sq_sequence
            $hbase $hpos $hdeg_two rr_mw_active_nonneg
            $hrec $hdeg_lo $hdeg_hi),
          (RealRooted.prec_mw_derivative_C_neg_mul_X_sq_sequence
            $hbase $hpos $hdeg_two rr_mw_active_nonneg
            $hrec $hdeg_lo $hdeg_hi),
          (RealRooted.prec_mw_derivative_neg_C_mul_X_sq_product_sequence
            $hbase $hpos $hdeg_two rr_mw_active_nonneg
            $hrec $hdeg_lo $hdeg_hi))
  | `(tactic|
      rr_mw_derivative_neg_X_sq_sequence_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        degree_two := $hdeg_two:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg:term) =>
      `(tactic|
        rr_mw_derivative_neg_X_sq_sequence_auto using
          base := $hbase,
          pos_lc := $hpos,
          degree_two := $hdeg_two,
          recurrence := $hrec,
          degree_lower := rr_mw_degree_seq $hdeg,
          degree_upper := rr_mw_degree_seq $hdeg)
  | `(tactic|
      rr_mw_derivative_neg_X_sq_sequence_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        degree_two := $hdeg_two:term,
        coeff_nonneg := $hc:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        rr_mw_three_variants
          (RealRooted.isRealRooted_of_mw_derivative_neg_C_mul_X_sq_sequence
            $hbase $hpos $hdeg_two $hc $hrec $hdeg_lo $hdeg_hi),
          (RealRooted.isRealRooted_of_mw_derivative_C_neg_mul_X_sq_sequence
            $hbase $hpos $hdeg_two $hc $hrec $hdeg_lo $hdeg_hi),
          (RealRooted.isRealRooted_of_mw_derivative_neg_C_mul_X_sq_product_sequence
            $hbase $hpos $hdeg_two $hc $hrec $hdeg_lo $hdeg_hi))
  | `(tactic|
      rr_mw_derivative_neg_X_sq_sequence_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        degree_two := $hdeg_two:term,
        coeff_nonneg := $hc:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg:term) =>
      `(tactic|
        first
          | rr_exact_realrooted_sequence_or_projection
              (RealRooted.isRealRooted_of_mw_derivative_neg_C_mul_X_sq_sequence
                $hbase $hpos $hdeg_two $hc $hrec
                (rr_mw_tail_degree_seq $hdeg) (rr_mw_tail_degree_seq $hdeg))
          | rr_exact_realrooted_sequence_or_projection
              (RealRooted.isRealRooted_of_mw_derivative_C_neg_mul_X_sq_sequence
                $hbase $hpos $hdeg_two $hc $hrec
                (rr_mw_tail_degree_seq $hdeg) (rr_mw_tail_degree_seq $hdeg))
          | rr_exact_realrooted_sequence_or_projection
              (RealRooted.isRealRooted_of_mw_derivative_neg_C_mul_X_sq_product_sequence
                $hbase $hpos $hdeg_two $hc $hrec
                (rr_mw_tail_degree_seq $hdeg) (rr_mw_tail_degree_seq $hdeg)))
  | `(tactic|
      rr_mw_derivative_neg_X_sq_sequence_realrooted_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        degree_two := $hdeg_two:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        rr_mw_three_variants
          (RealRooted.isRealRooted_of_mw_derivative_neg_C_mul_X_sq_sequence
            $hbase $hpos $hdeg_two rr_mw_active_nonneg
            $hrec $hdeg_lo $hdeg_hi),
          (RealRooted.isRealRooted_of_mw_derivative_C_neg_mul_X_sq_sequence
            $hbase $hpos $hdeg_two rr_mw_active_nonneg
            $hrec $hdeg_lo $hdeg_hi),
          (RealRooted.isRealRooted_of_mw_derivative_neg_C_mul_X_sq_product_sequence
            $hbase $hpos $hdeg_two rr_mw_active_nonneg
            $hrec $hdeg_lo $hdeg_hi))
  | `(tactic|
      rr_mw_derivative_neg_X_sq_sequence_realrooted_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        degree_two := $hdeg_two:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg:term) =>
      `(tactic|
        first
          | rr_exact_realrooted_sequence_or_projection
              (RealRooted.isRealRooted_of_mw_derivative_neg_C_mul_X_sq_sequence
                $hbase $hpos $hdeg_two rr_mw_active_nonneg $hrec
                (rr_mw_tail_degree_seq $hdeg) (rr_mw_tail_degree_seq $hdeg))
          | rr_exact_realrooted_sequence_or_projection
              (RealRooted.isRealRooted_of_mw_derivative_C_neg_mul_X_sq_sequence
                $hbase $hpos $hdeg_two rr_mw_active_nonneg $hrec
                (rr_mw_tail_degree_seq $hdeg) (rr_mw_tail_degree_seq $hdeg))
          | rr_exact_realrooted_sequence_or_projection
              (RealRooted.isRealRooted_of_mw_derivative_neg_C_mul_X_sq_product_sequence
                $hbase $hpos $hdeg_two rr_mw_active_nonneg $hrec
                (rr_mw_tail_degree_seq $hdeg) (rr_mw_tail_degree_seq $hdeg)))
  | `(tactic|
      rr_mw_derivative_one_add_X_sequence using
        base := $hbase:term,
        pos_lc := $hpos:term,
        degree_two := $hdeg_two:term,
        root_upper := $hroot_upper:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        exact RealRooted.prec_mw_derivative_one_add_X_sequence
          $hbase $hpos $hdeg_two $hroot_upper $hrec $hdeg_lo $hdeg_hi)
  | `(tactic|
      rr_mw_derivative_one_add_X_sequence_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        degree_two := $hdeg_two:term,
        root_upper := $hroot_upper:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_mw_derivative_one_add_X_sequence
            $hbase $hpos $hdeg_two $hroot_upper $hrec $hdeg_lo $hdeg_hi))
  | `(tactic|
      rr_mw_derivative_C_mul_one_add_X_sequence using
        base := $hbase:term,
        pos_lc := $hpos:term,
        degree_two := $hdeg_two:term,
        coeff_nonneg := $hc:term,
        root_upper := $hroot_upper:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        rr_mw_two_variants
          (RealRooted.prec_mw_derivative_C_mul_one_add_X_sequence
            $hbase $hpos $hdeg_two $hc $hroot_upper $hrec $hdeg_lo $hdeg_hi),
          (RealRooted.prec_mw_derivative_one_add_X_mul_C_sequence
            $hbase $hpos $hdeg_two $hc $hroot_upper $hrec $hdeg_lo $hdeg_hi))
  | `(tactic|
      rr_mw_derivative_C_mul_one_add_X_sequence_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        degree_two := $hdeg_two:term,
        root_upper := $hroot_upper:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        rr_mw_two_variants
          (RealRooted.prec_mw_derivative_C_mul_one_add_X_sequence
            $hbase $hpos $hdeg_two rr_mw_active_nonneg
            $hroot_upper $hrec $hdeg_lo $hdeg_hi),
          (RealRooted.prec_mw_derivative_one_add_X_mul_C_sequence
            $hbase $hpos $hdeg_two rr_mw_active_nonneg
            $hroot_upper $hrec $hdeg_lo $hdeg_hi))
  | `(tactic|
      rr_mw_derivative_C_mul_one_add_X_sequence_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        degree_two := $hdeg_two:term,
        coeff_nonneg := $hc:term,
        root_upper := $hroot_upper:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        rr_mw_two_variants
          (RealRooted.isRealRooted_of_mw_derivative_C_mul_one_add_X_sequence
            $hbase $hpos $hdeg_two $hc $hroot_upper $hrec $hdeg_lo $hdeg_hi),
          (RealRooted.isRealRooted_of_mw_derivative_one_add_X_mul_C_sequence
            $hbase $hpos $hdeg_two $hc $hroot_upper $hrec $hdeg_lo $hdeg_hi))
  | `(tactic|
      rr_mw_derivative_C_mul_one_add_X_sequence_realrooted_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        degree_two := $hdeg_two:term,
        root_upper := $hroot_upper:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        rr_mw_two_variants
          (RealRooted.isRealRooted_of_mw_derivative_C_mul_one_add_X_sequence
            $hbase $hpos $hdeg_two rr_mw_active_nonneg
            $hroot_upper $hrec $hdeg_lo $hdeg_hi),
          (RealRooted.isRealRooted_of_mw_derivative_one_add_X_mul_C_sequence
            $hbase $hpos $hdeg_two rr_mw_active_nonneg
            $hroot_upper $hrec $hdeg_lo $hdeg_hi))
  | `(tactic|
      rr_mw_derivative_X_sub_one_sequence using
        base := $hbase:term,
        pos_lc := $hpos:term,
        degree_two := $hdeg_two:term,
        root_upper := $hroot_upper:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        exact RealRooted.prec_mw_derivative_X_sub_one_sequence
          $hbase $hpos $hdeg_two $hroot_upper $hrec $hdeg_lo $hdeg_hi)
  | `(tactic|
      rr_mw_derivative_X_sub_one_sequence_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        degree_two := $hdeg_two:term,
        root_upper := $hroot_upper:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_mw_derivative_X_sub_one_sequence
            $hbase $hpos $hdeg_two $hroot_upper $hrec $hdeg_lo $hdeg_hi))
  | `(tactic|
      rr_mw_derivative_C_mul_X_sub_one_sequence using
        base := $hbase:term,
        pos_lc := $hpos:term,
        degree_two := $hdeg_two:term,
        coeff_nonneg := $hc:term,
        root_upper := $hroot_upper:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        rr_mw_two_variants
          (RealRooted.prec_mw_derivative_C_mul_X_sub_one_sequence
            $hbase $hpos $hdeg_two $hc $hroot_upper $hrec $hdeg_lo $hdeg_hi),
          (RealRooted.prec_mw_derivative_X_sub_one_mul_C_sequence
            $hbase $hpos $hdeg_two $hc $hroot_upper $hrec $hdeg_lo $hdeg_hi))
  | `(tactic|
      rr_mw_derivative_C_mul_X_sub_one_sequence_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        degree_two := $hdeg_two:term,
        root_upper := $hroot_upper:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        rr_mw_two_variants
          (RealRooted.prec_mw_derivative_C_mul_X_sub_one_sequence
            $hbase $hpos $hdeg_two rr_mw_active_nonneg
            $hroot_upper $hrec $hdeg_lo $hdeg_hi),
          (RealRooted.prec_mw_derivative_X_sub_one_mul_C_sequence
            $hbase $hpos $hdeg_two rr_mw_active_nonneg
            $hroot_upper $hrec $hdeg_lo $hdeg_hi))
  | `(tactic|
      rr_mw_derivative_C_mul_X_sub_one_sequence_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        degree_two := $hdeg_two:term,
        coeff_nonneg := $hc:term,
        root_upper := $hroot_upper:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        rr_mw_two_variants
          (RealRooted.isRealRooted_of_mw_derivative_C_mul_X_sub_one_sequence
            $hbase $hpos $hdeg_two $hc $hroot_upper $hrec $hdeg_lo $hdeg_hi),
          (RealRooted.isRealRooted_of_mw_derivative_X_sub_one_mul_C_sequence
            $hbase $hpos $hdeg_two $hc $hroot_upper $hrec $hdeg_lo $hdeg_hi))
  | `(tactic|
      rr_mw_derivative_C_mul_X_sub_one_sequence_realrooted_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        degree_two := $hdeg_two:term,
        root_upper := $hroot_upper:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        rr_mw_two_variants
          (RealRooted.isRealRooted_of_mw_derivative_C_mul_X_sub_one_sequence
            $hbase $hpos $hdeg_two rr_mw_active_nonneg
            $hroot_upper $hrec $hdeg_lo $hdeg_hi),
          (RealRooted.isRealRooted_of_mw_derivative_X_sub_one_mul_C_sequence
            $hbase $hpos $hdeg_two rr_mw_active_nonneg
            $hroot_upper $hrec $hdeg_lo $hdeg_hi))
  | `(tactic|
      rr_mw_derivative_nonpos_nonneg_sequence using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        coeff_nonpos_of_nonpos := $hV:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        exact RealRooted.prec_mw_derivative_nonpos_sequence_of_nonneg_coeffs
          $hbase $hpos $hnonneg $hdeg_two $hV $hrec $hdeg_lo $hdeg_hi)
  | `(tactic|
      rr_mw_derivative_nonpos_nonneg_sequence_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        coeff_nonpos_of_nonpos := $hV:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_mw_derivative_nonpos_sequence_of_nonneg_coeffs
            $hbase $hpos $hnonneg $hdeg_two $hV $hrec $hdeg_lo $hdeg_hi))
  | `(tactic|
      rr_mw_derivative_nonpos_nonneg_sequence_sign_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        exact RealRooted.prec_mw_derivative_nonpos_sequence_of_nonneg_coeffs
          $hbase $hpos $hnonneg $hdeg_two
          (rr_mw_root_sign_seq) $hrec $hdeg_lo $hdeg_hi)
  | `(tactic|
      rr_mw_derivative_nonpos_nonneg_sequence_sign_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg:term) =>
      `(tactic|
        rr_mw_derivative_nonpos_nonneg_sequence_sign_auto using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          degree_two := $hdeg_two,
          recurrence := $hrec,
          degree_lower := rr_mw_degree_seq $hdeg,
          degree_upper := rr_mw_degree_seq $hdeg)
  | `(tactic|
      rr_mw_derivative_nonpos_nonneg_sequence_realrooted_sign_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_mw_derivative_nonpos_sequence_of_nonneg_coeffs
            $hbase $hpos $hnonneg $hdeg_two
            (rr_mw_root_sign_seq) $hrec $hdeg_lo $hdeg_hi))
  | `(tactic|
      rr_mw_derivative_nonpos_nonneg_sequence_realrooted_sign_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg:term) =>
      `(tactic|
        rr_mw_derivative_nonpos_nonneg_sequence_realrooted_sign_auto using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          degree_two := $hdeg_two,
          recurrence := $hrec,
          degree_lower := rr_mw_degree_seq $hdeg,
          degree_upper := rr_mw_degree_seq $hdeg)
  | `(tactic|
      rr_mw_lw_derivative_lag_sequence_sign_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact
          RealRooted.prec_mw_lw_derivative_lag_sequence_of_nonneg_coeffs_on_roots
            $hbase $hpos $hnonneg $hdeg_two $hrec
            (by intro n r hr hroot_nonpos; rr_sign)
            (by intro n r hr hroot_nonpos; rr_sign)
            $hdeg_succ $hno)
  | `(tactic|
      rr_mw_lw_derivative_lag_sequence_root_upper_sign_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        degree_two := $hdeg_two:term,
        root_upper := $hroot_upper:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact
          RealRooted.prec_mw_lw_derivative_lag_sequence
            $hbase $hpos $hdeg_two $hrec
            (rr_sign_at_roots_upper_seq $hroot_upper)
            (rr_sign_at_roots_upper_seq $hroot_upper)
            $hdeg_succ $hno)
  | `(tactic|
      rr_mw_lw_derivative_lag_sequence_realrooted_sign_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_mw_lw_derivative_lag_sequence_of_nonneg_coeffs_on_roots
            $hbase $hpos $hnonneg $hdeg_two $hrec
            (by intro n r hr hroot_nonpos; rr_sign)
            (by intro n r hr hroot_nonpos; rr_sign)
            $hdeg_succ $hno))

  | `(tactic|
      rr_mw_lw_derivative_lag_sequence_realrooted_root_upper_sign_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        degree_two := $hdeg_two:term,
        root_upper := $hroot_upper:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_mw_lw_derivative_lag_sequence
            $hbase $hpos $hdeg_two $hrec
            (rr_sign_at_roots_upper_seq $hroot_upper)
            (rr_sign_at_roots_upper_seq $hroot_upper)
            $hdeg_succ $hno))
  | `(tactic|
      rr_mw_lw_derivative_lag_sequence_window_sign_auto using
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
          RealRooted.prec_mw_lw_derivative_lag_sequence_of_root_window
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
      rr_mw_lw_derivative_lag_sequence_realrooted_window_sign_auto using
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
          (RealRooted.isRealRooted_of_mw_lw_derivative_lag_sequence_of_root_window
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

end Tactic
end RealRooted
