import RealRooted.Tactic.LiuWang.Step

/-!
# Positive-lag Liu--Wang sequence tactics

Parser declarations and macro implementations for this Liu--Wang tactic family.
-/

namespace RealRooted
namespace Tactic

syntax (name := rr_lw_positive_t_sequence_named)
  "rr_lw_positive_t_sequence" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_positive_t_sequence_auto_named)
  "rr_lw_positive_t_sequence_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_positive_t_sequence_realrooted_named)
  "rr_lw_positive_t_sequence_realrooted" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_positive_t_sequence_realrooted_auto_named)
  "rr_lw_positive_t_sequence_realrooted_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_positive_t_lag_step_named)
  "rr_lw_positive_t_lag_step" " using "
    "interlaces" ":=" term ","
    "interlacer_pos_lc" ":=" term ","
    "source_nonneg_coeffs" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "target_pos_lc" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_positive_X_lag_sequence_named)
  "rr_lw_positive_X_lag_sequence" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_positive_X_lag_sequence_realrooted_named)
  "rr_lw_positive_X_lag_sequence_realrooted" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_C_mul_X_sub_C_lag_sequence_named)
  "rr_lw_C_mul_X_sub_C_lag_sequence" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "scalar_nonneg" ":=" term ","
    "constant_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_C_mul_X_sub_C_lag_sequence_auto_named)
  "rr_lw_C_mul_X_sub_C_lag_sequence_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_C_mul_X_sub_C_lag_sequence_realrooted_named)
  "rr_lw_C_mul_X_sub_C_lag_sequence_realrooted" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "scalar_nonneg" ":=" term ","
    "constant_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_C_mul_X_sub_C_lag_sequence_realrooted_auto_named)
  "rr_lw_C_mul_X_sub_C_lag_sequence_realrooted_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_positive_affine_lag_sequence_named)
  "rr_lw_positive_affine_lag_sequence" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_positive_affine_lag_sequence_auto_named)
  "rr_lw_positive_affine_lag_sequence_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_positive_affine_lag_sequence_realrooted_named)
  "rr_lw_positive_affine_lag_sequence_realrooted" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_positive_affine_lag_sequence_realrooted_auto_named)
  "rr_lw_positive_affine_lag_sequence_realrooted_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_positive_affine_lag_sequence_shift_nonneg_named)
  "rr_lw_positive_affine_lag_sequence_shift_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "shift_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_positive_affine_lag_sequence_shift_nonneg_auto_named)
  "rr_lw_positive_affine_lag_sequence_shift_nonneg_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "shift_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_positive_affine_lag_sequence_realrooted_shift_nonneg_named)
  "rr_lw_positive_affine_lag_sequence_realrooted_shift_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "shift_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_positive_affine_lag_sequence_realrooted_shift_nonneg_auto_named)
  "rr_lw_positive_affine_lag_sequence_realrooted_shift_nonneg_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "shift_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_C_add_X_lag_sequence_named)
  "rr_lw_C_add_X_lag_sequence" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_C_add_X_lag_sequence_realrooted_named)
  "rr_lw_C_add_X_lag_sequence_realrooted" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_C_add_X_lag_sequence_shift_nonneg_named)
  "rr_lw_C_add_X_lag_sequence_shift_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "shift_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_C_add_X_lag_sequence_realrooted_shift_nonneg_named)
  "rr_lw_C_add_X_lag_sequence_realrooted_shift_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "shift_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_X_one_add_X_lag_sequence_nonneg_named)
  "rr_lw_X_one_add_X_lag_sequence_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "root_lower" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_X_one_add_X_lag_sequence_realrooted_nonneg_named)
  "rr_lw_X_one_add_X_lag_sequence_realrooted_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "root_lower" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_X_one_sub_X_one_add_X_lag_sequence_nonneg_named)
  "rr_lw_X_one_sub_X_one_add_X_lag_sequence_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "root_lower" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name :=
    rr_lw_X_one_sub_X_one_add_X_lag_sequence_realrooted_nonneg_named)
  "rr_lw_X_one_sub_X_one_add_X_lag_sequence_realrooted_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "root_lower" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_X_sub_X_pow_three_lag_sequence_nonneg_named)
  "rr_lw_X_sub_X_pow_three_lag_sequence_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "root_lower" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_X_sub_X_pow_three_lag_sequence_realrooted_nonneg_named)
  "rr_lw_X_sub_X_pow_three_lag_sequence_realrooted_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "root_lower" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_C_mul_X_one_add_X_lag_sequence_nonneg_named)
  "rr_lw_C_mul_X_one_add_X_lag_sequence_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "root_lower" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_C_mul_X_one_add_X_lag_sequence_nonneg_auto_named)
  "rr_lw_C_mul_X_one_add_X_lag_sequence_nonneg_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "root_lower" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_C_mul_X_one_add_X_lag_sequence_realrooted_nonneg_named)
  "rr_lw_C_mul_X_one_add_X_lag_sequence_realrooted_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "root_lower" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_C_mul_X_one_add_X_lag_sequence_realrooted_nonneg_auto_named)
  "rr_lw_C_mul_X_one_add_X_lag_sequence_realrooted_nonneg_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "root_lower" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_C_mul_X_one_sub_X_one_add_X_lag_sequence_nonneg_named)
  "rr_lw_C_mul_X_one_sub_X_one_add_X_lag_sequence_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "root_lower" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_C_mul_X_one_sub_X_one_add_X_lag_sequence_nonneg_auto_named)
  "rr_lw_C_mul_X_one_sub_X_one_add_X_lag_sequence_nonneg_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "root_lower" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name :=
    rr_lw_C_mul_X_one_sub_X_one_add_X_lag_sequence_realrooted_nonneg_named)
  "rr_lw_C_mul_X_one_sub_X_one_add_X_lag_sequence_realrooted_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "root_lower" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name :=
    rr_lw_C_mul_X_one_sub_X_one_add_X_lag_sequence_realrooted_nonneg_auto_named)
  "rr_lw_C_mul_X_one_sub_X_one_add_X_lag_sequence_realrooted_nonneg_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "root_lower" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_C_mul_X_sub_X_pow_three_lag_sequence_nonneg_named)
  "rr_lw_C_mul_X_sub_X_pow_three_lag_sequence_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "root_lower" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_C_mul_X_sub_X_pow_three_lag_sequence_nonneg_auto_named)
  "rr_lw_C_mul_X_sub_X_pow_three_lag_sequence_nonneg_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "root_lower" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_lw_C_mul_X_sub_X_pow_three_lag_sequence_realrooted_nonneg_named)
  "rr_lw_C_mul_X_sub_X_pow_three_lag_sequence_realrooted_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "root_lower" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name :=
    rr_lw_C_mul_X_sub_X_pow_three_lag_sequence_realrooted_nonneg_auto_named)
  "rr_lw_C_mul_X_sub_X_pow_three_lag_sequence_realrooted_nonneg_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "root_lower" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

macro_rules
  | `(tactic|
      rr_lw_positive_t_lag_step using
        interlaces := $hInter:term,
        interlacer_pos_lc := $hg_pos:term,
        source_nonneg_coeffs := $hf_nonneg:term,
        coeff_nonneg := $hc:term,
        target_pos_lc := $hF_pos:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact RealRooted.prec_lw_positive_t_lag_of_nonneg_coeffs_of_recurrence
          $hInter $hg_pos $hf_nonneg $hc $hrec $hF_pos $hdeg_succ $hno)
  | `(tactic|
      rr_lw_positive_t_sequence using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        coeff_nonneg := $hc:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact RealRooted.prec_lw_positive_t_lag_sequence
          $hbase $hpos $hnonneg $hc $hrec $hdeg_succ $hno)
  | `(tactic|
      rr_lw_positive_t_sequence_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact RealRooted.prec_lw_positive_t_lag_sequence
          $hbase $hpos $hnonneg rr_lw_active_nonneg $hrec $hdeg_succ
          $hno)
  | `(tactic|
      rr_lw_positive_t_sequence_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        coeff_nonneg := $hc:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_lw_positive_t_lag_sequence
            $hbase $hpos $hnonneg $hc $hrec $hdeg_succ $hno))
  | `(tactic|
      rr_lw_positive_t_sequence_realrooted_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_lw_positive_t_lag_sequence
            $hbase $hpos $hnonneg rr_lw_active_nonneg $hrec
            $hdeg_succ $hno))
  | `(tactic|
      rr_lw_positive_X_lag_sequence using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact RealRooted.prec_lw_positive_X_lag_sequence
          $hbase $hpos $hnonneg $hrec $hdeg_succ $hno)
  | `(tactic|
      rr_lw_positive_X_lag_sequence_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_lw_positive_X_lag_sequence
            $hbase $hpos $hnonneg $hrec $hdeg_succ $hno))
  | `(tactic|
      rr_lw_C_mul_X_sub_C_lag_sequence using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        scalar_nonneg := $hc:term,
        constant_nonneg := $ha:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact RealRooted.prec_lw_C_mul_X_sub_C_lag_sequence
          $hbase $hpos $hnonneg $hc $ha $hrec $hdeg_succ $hno)
  | `(tactic|
      rr_lw_C_mul_X_sub_C_lag_sequence_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_refine_active_nonneg_seq
          (RealRooted.prec_lw_C_mul_X_sub_C_lag_sequence
            $hbase $hpos $hnonneg ?_ ?_ $hrec $hdeg_succ $hno))
  | `(tactic|
      rr_lw_C_mul_X_sub_C_lag_sequence_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        scalar_nonneg := $hc:term,
        constant_nonneg := $ha:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_lw_C_mul_X_sub_C_lag_sequence
            $hbase $hpos $hnonneg $hc $ha $hrec $hdeg_succ $hno))
  | `(tactic|
      rr_lw_C_mul_X_sub_C_lag_sequence_realrooted_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_exact_realrooted_active_nonneg_seq
          (RealRooted.isRealRooted_of_lw_C_mul_X_sub_C_lag_sequence
            $hbase $hpos $hnonneg ?_ ?_ $hrec $hdeg_succ $hno))
  | `(tactic|
      rr_lw_positive_affine_lag_sequence using
        base := $hbase:term,
        pos_lc := $hpos:term,
        coeff_nonneg := $hc:term,
        root_upper := $hroot_upper:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact RealRooted.prec_lw_positive_affine_lag_sequence
          $hbase $hpos $hc $hroot_upper $hrec $hdeg_succ $hno)
  | `(tactic|
      rr_lw_positive_affine_lag_sequence_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        root_upper := $hroot_upper:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_refine_active_nonneg_seq
          (RealRooted.prec_lw_positive_affine_lag_sequence
            $hbase $hpos ?_ $hroot_upper $hrec $hdeg_succ $hno))
  | `(tactic|
      rr_lw_positive_affine_lag_sequence_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        coeff_nonneg := $hc:term,
        root_upper := $hroot_upper:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_lw_positive_affine_lag_sequence
            $hbase $hpos $hc $hroot_upper $hrec $hdeg_succ $hno))
  | `(tactic|
      rr_lw_positive_affine_lag_sequence_realrooted_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        root_upper := $hroot_upper:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_exact_realrooted_active_nonneg_seq
          (RealRooted.isRealRooted_of_lw_positive_affine_lag_sequence
            $hbase $hpos ?_ $hroot_upper $hrec $hdeg_succ $hno))
  | `(tactic|
      rr_lw_positive_affine_lag_sequence_shift_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        coeff_nonneg := $hc:term,
        shift_nonneg := $hshift_nonneg:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact RealRooted.prec_lw_positive_affine_lag_sequence_of_shift_nonneg_coeffs
          $hbase $hpos $hc $hshift_nonneg $hrec $hdeg_succ $hno)
  | `(tactic|
      rr_lw_positive_affine_lag_sequence_shift_nonneg_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        shift_nonneg := $hshift_nonneg:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_refine_active_nonneg_seq
          (RealRooted.prec_lw_positive_affine_lag_sequence_of_shift_nonneg_coeffs
            $hbase $hpos ?_ $hshift_nonneg $hrec $hdeg_succ $hno))
  | `(tactic|
      rr_lw_positive_affine_lag_sequence_realrooted_shift_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        coeff_nonneg := $hc:term,
        shift_nonneg := $hshift_nonneg:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_lw_positive_affine_lag_sequence_of_shift_nonneg_coeffs
            $hbase $hpos $hc $hshift_nonneg $hrec $hdeg_succ $hno))
  | `(tactic|
      rr_lw_positive_affine_lag_sequence_realrooted_shift_nonneg_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        shift_nonneg := $hshift_nonneg:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_exact_realrooted_active_nonneg_seq
          (RealRooted.isRealRooted_of_lw_positive_affine_lag_sequence_of_shift_nonneg_coeffs
            $hbase $hpos ?_ $hshift_nonneg $hrec $hdeg_succ $hno))
  | `(tactic|
      rr_lw_C_add_X_lag_sequence using
        base := $hbase:term,
        pos_lc := $hpos:term,
        root_upper := $hroot_upper:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact RealRooted.prec_lw_C_add_X_lag_sequence
          $hbase $hpos $hroot_upper $hrec $hdeg_succ $hno)
  | `(tactic|
      rr_lw_C_add_X_lag_sequence_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        root_upper := $hroot_upper:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_lw_C_add_X_lag_sequence
            $hbase $hpos $hroot_upper $hrec $hdeg_succ $hno))
  | `(tactic|
      rr_lw_C_add_X_lag_sequence_shift_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        shift_nonneg := $hshift_nonneg:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact RealRooted.prec_lw_C_add_X_lag_sequence_of_shift_nonneg_coeffs
          $hbase $hpos $hshift_nonneg $hrec $hdeg_succ $hno)
  | `(tactic|
      rr_lw_C_add_X_lag_sequence_realrooted_shift_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        shift_nonneg := $hshift_nonneg:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_lw_C_add_X_lag_sequence_of_shift_nonneg_coeffs
            $hbase $hpos $hshift_nonneg $hrec $hdeg_succ $hno))
  | `(tactic|
      rr_lw_X_one_add_X_lag_sequence_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact RealRooted.prec_lw_X_mul_one_add_X_lag_sequence_of_nonneg_coeffs
          $hbase $hpos $hnonneg $hroot_lower $hrec $hdeg_succ $hno)
  | `(tactic|
      rr_lw_X_one_add_X_lag_sequence_realrooted_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_lw_X_mul_one_add_X_lag_sequence_of_nonneg_coeffs
            $hbase $hpos $hnonneg $hroot_lower $hrec $hdeg_succ $hno))
  | `(tactic|
      rr_lw_X_one_sub_X_one_add_X_lag_sequence_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact
          RealRooted.prec_lw_X_mul_one_sub_X_mul_one_add_X_lag_sequence_of_nonneg_coeffs
            $hbase $hpos $hnonneg $hroot_lower $hrec $hdeg_succ $hno)
  | `(tactic|
      rr_lw_X_one_sub_X_one_add_X_lag_sequence_realrooted_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_lw_X_mul_one_sub_X_mul_one_add_X_lag_sequence_of_nonneg_coeffs
            $hbase $hpos $hnonneg $hroot_lower $hrec $hdeg_succ $hno))
  | `(tactic|
      rr_lw_X_sub_X_pow_three_lag_sequence_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact RealRooted.prec_lw_X_sub_X_pow_three_lag_sequence_of_nonneg_coeffs
          $hbase $hpos $hnonneg $hroot_lower $hrec $hdeg_succ $hno)
  | `(tactic|
      rr_lw_X_sub_X_pow_three_lag_sequence_realrooted_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_lw_X_sub_X_pow_three_lag_sequence_of_nonneg_coeffs
            $hbase $hpos $hnonneg $hroot_lower $hrec $hdeg_succ $hno))
  | `(tactic|
      rr_lw_C_mul_X_one_add_X_lag_sequence_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        coeff_nonneg := $hc:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact RealRooted.prec_lw_C_mul_X_mul_one_add_X_lag_sequence_of_nonneg_coeffs
          $hbase $hpos $hnonneg $hc $hroot_lower $hrec $hdeg_succ $hno)
  | `(tactic|
      rr_lw_C_mul_X_one_add_X_lag_sequence_nonneg_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_refine_active_nonneg_seq
          (RealRooted.prec_lw_C_mul_X_mul_one_add_X_lag_sequence_of_nonneg_coeffs
            $hbase $hpos $hnonneg ?_ $hroot_lower $hrec $hdeg_succ $hno))
  | `(tactic|
      rr_lw_C_mul_X_one_add_X_lag_sequence_realrooted_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        coeff_nonneg := $hc:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_lw_C_mul_X_mul_one_add_X_lag_sequence_of_nonneg_coeffs
            $hbase $hpos $hnonneg $hc $hroot_lower $hrec $hdeg_succ $hno))
  | `(tactic|
      rr_lw_C_mul_X_one_add_X_lag_sequence_realrooted_nonneg_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_exact_realrooted_active_nonneg_seq
          (RealRooted.isRealRooted_of_lw_C_mul_X_mul_one_add_X_lag_sequence_of_nonneg_coeffs
            $hbase $hpos $hnonneg ?_ $hroot_lower $hrec $hdeg_succ $hno))
  | `(tactic|
      rr_lw_C_mul_X_one_sub_X_one_add_X_lag_sequence_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        coeff_nonneg := $hc:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact
          RealRooted.prec_lw_C_mul_X_mul_one_sub_X_mul_one_add_X_lag_sequence_of_nonneg_coeffs
            $hbase $hpos $hnonneg $hc $hroot_lower $hrec $hdeg_succ $hno)
  | `(tactic|
      rr_lw_C_mul_X_one_sub_X_one_add_X_lag_sequence_nonneg_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_refine_active_nonneg_seq
          (RealRooted.prec_lw_C_mul_X_mul_one_sub_X_mul_one_add_X_lag_sequence_of_nonneg_coeffs
            $hbase $hpos $hnonneg ?_ $hroot_lower $hrec $hdeg_succ $hno))
  | `(tactic|
      rr_lw_C_mul_X_one_sub_X_one_add_X_lag_sequence_realrooted_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        coeff_nonneg := $hc:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (isRealRooted_of_lw_C_mul_X_mul_one_sub_X_mul_one_add_X_lag_sequence_of_nonneg_coeffs
            $hbase $hpos $hnonneg $hc $hroot_lower $hrec $hdeg_succ $hno))
  | `(tactic|
      rr_lw_C_mul_X_one_sub_X_one_add_X_lag_sequence_realrooted_nonneg_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_exact_realrooted_active_nonneg_seq
          (isRealRooted_of_lw_C_mul_X_mul_one_sub_X_mul_one_add_X_lag_sequence_of_nonneg_coeffs
            $hbase $hpos $hnonneg ?_ $hroot_lower $hrec $hdeg_succ $hno))
  | `(tactic|
      rr_lw_C_mul_X_sub_X_pow_three_lag_sequence_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        coeff_nonneg := $hc:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact
          RealRooted.prec_lw_C_mul_X_sub_X_pow_three_lag_sequence_of_nonneg_coeffs
            $hbase $hpos $hnonneg $hc $hroot_lower $hrec $hdeg_succ $hno)
  | `(tactic|
      rr_lw_C_mul_X_sub_X_pow_three_lag_sequence_nonneg_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_refine_active_nonneg_seq
          (RealRooted.prec_lw_C_mul_X_sub_X_pow_three_lag_sequence_of_nonneg_coeffs
            $hbase $hpos $hnonneg ?_ $hroot_lower $hrec $hdeg_succ $hno))
  | `(tactic|
      rr_lw_C_mul_X_sub_X_pow_three_lag_sequence_realrooted_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        coeff_nonneg := $hc:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_lw_C_mul_X_sub_X_pow_three_lag_sequence_of_nonneg_coeffs
            $hbase $hpos $hnonneg $hc $hroot_lower $hrec $hdeg_succ $hno))
  | `(tactic|
      rr_lw_C_mul_X_sub_X_pow_three_lag_sequence_realrooted_nonneg_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_exact_realrooted_active_nonneg_seq
          (RealRooted.isRealRooted_of_lw_C_mul_X_sub_X_pow_three_lag_sequence_of_nonneg_coeffs
            $hbase $hpos $hnonneg ?_ $hroot_lower $hrec $hdeg_succ $hno))

end Tactic
end RealRooted
