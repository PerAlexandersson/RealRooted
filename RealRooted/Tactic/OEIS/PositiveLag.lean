import RealRooted.Tactic.LiuWang.SequenceProducts
import RealRooted.Tactic.WagnerX

/-!
# OEIS positive-lag certificate frontend

Parser declarations and dispatch rules for positive t-lag recurrence
certificates. This frontend is independent of denominator normalization and
the degree-two derivative-lag certificate language.
-/

namespace RealRooted
namespace Tactic

syntax (name := rr_e_positive_t_lag_sequence_strict)
  "rr_e_positive_t_lag_sequence" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term ","
    "certificate" ":="
      ("currentX" <|> "currentCX" <|> "currentOneAddX" <|> "xOneSubX" <|>
        "xCSubCMulX" <|> "cMulXCSubCMulX") :
  tactic

syntax (name := rr_e_positive_t_lag_sequence_realrooted_strict)
  "rr_e_positive_t_lag_sequence_realrooted" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term ","
    "certificate" ":="
      ("currentX" <|> "currentCX" <|> "currentOneAddX" <|> "xOneSubX" <|>
        "xCSubCMulX" <|> "cMulXCSubCMulX") :
  tactic

syntax (name := rr_e_positive_t_lag_sequence_plateau_x)
  "rr_e_positive_t_lag_sequence" " using "
    "base" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "recurrence" ":=" term ","
    "certificate" ":=" "plateauX" :
  tactic

syntax (name := rr_e_positive_t_lag_sequence_realrooted_plateau_x)
  "rr_e_positive_t_lag_sequence_realrooted" " using "
    "base" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "recurrence" ":=" term ","
    "certificate" ":=" "plateauX" :
  tactic

syntax (name := rr_e_positive_t_lag_sequence_tR)
  "rr_e_positive_t_lag_sequence" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "factor_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term ","
    "certificate" ":=" "tR" :
  tactic

syntax (name := rr_e_positive_t_lag_sequence_realrooted_tR)
  "rr_e_positive_t_lag_sequence_realrooted" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "factor_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term ","
    "certificate" ":=" "tR" :
  tactic

syntax (name := rr_e_positive_t_lag_sequence_cTR)
  "rr_e_positive_t_lag_sequence" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "factor_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term ","
    "certificate" ":=" "cTR" :
  tactic

syntax (name := rr_e_positive_t_lag_sequence_realrooted_cTR)
  "rr_e_positive_t_lag_sequence_realrooted" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "factor_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term ","
    "certificate" ":=" "cTR" :
  tactic

syntax (name := rr_e_positive_t_lag_sequence_cTR_auto)
  "rr_e_positive_t_lag_sequence" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "factor_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term ","
    "certificate" ":=" "cTRAuto" :
  tactic

syntax (name := rr_e_positive_t_lag_sequence_realrooted_cTR_auto)
  "rr_e_positive_t_lag_sequence_realrooted" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "factor_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term ","
    "certificate" ":=" "cTRAuto" :
  tactic
macro_rules
  | `(tactic|
      rr_e_positive_t_lag_sequence using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        factor_nonneg := $hR:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term,
        certificate := tR) =>
      `(tactic|
        rr_lw_tR_lag_sequence using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          factor_nonneg := $hR,
          recurrence := $hrec,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_e_positive_t_lag_sequence_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        factor_nonneg := $hR:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term,
        certificate := tR) =>
      `(tactic|
        rr_lw_tR_lag_sequence_realrooted using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          factor_nonneg := $hR,
          recurrence := $hrec,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_e_positive_t_lag_sequence using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        coeff_nonneg := $hc:term,
        factor_nonneg := $hR:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term,
        certificate := cTR) =>
      `(tactic|
        rr_lw_c_tR_lag_sequence using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          coeff_nonneg := $hc,
          factor_nonneg := $hR,
          recurrence := $hrec,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_e_positive_t_lag_sequence_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        coeff_nonneg := $hc:term,
        factor_nonneg := $hR:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term,
        certificate := cTR) =>
      `(tactic|
        rr_lw_c_tR_lag_sequence_realrooted using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          coeff_nonneg := $hc,
          factor_nonneg := $hR,
          recurrence := $hrec,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_e_positive_t_lag_sequence using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        factor_nonneg := $hR:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term,
        certificate := cTRAuto) =>
      `(tactic|
        rr_lw_c_tR_lag_sequence_auto using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          factor_nonneg := $hR,
          recurrence := $hrec,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_e_positive_t_lag_sequence_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        factor_nonneg := $hR:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term,
        certificate := cTRAuto) =>
      `(tactic|
        rr_lw_c_tR_lag_sequence_realrooted_auto using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          factor_nonneg := $hR,
          recurrence := $hrec,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_e_positive_t_lag_sequence using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term,
        certificate := currentX) =>
      `(tactic|
        rr_lw_current_X_sequence_auto using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          recurrence := $hrec,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_e_positive_t_lag_sequence_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term,
        certificate := currentX) =>
      `(tactic|
        rr_lw_current_X_sequence_realrooted_auto using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          recurrence := $hrec,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_e_positive_t_lag_sequence using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term,
        certificate := currentCX) =>
      `(tactic|
        rr_lw_current_CX_sequence_auto using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          recurrence := $hrec,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_e_positive_t_lag_sequence_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term,
        certificate := currentCX) =>
      `(tactic|
        rr_lw_current_CX_sequence_realrooted_auto using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          recurrence := $hrec,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_e_positive_t_lag_sequence using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term,
        certificate := currentOneAddX) =>
      `(tactic|
        rr_lw_current_one_add_X_sequence_auto using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          recurrence := $hrec,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_e_positive_t_lag_sequence_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term,
        certificate := currentOneAddX) =>
      `(tactic|
        rr_lw_current_one_add_X_sequence_realrooted_auto using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          recurrence := $hrec,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_e_positive_t_lag_sequence using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term,
        certificate := xOneSubX) =>
      `(tactic|
        rr_lw_X_one_sub_X_lag_sequence using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          recurrence := $hrec,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_e_positive_t_lag_sequence_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term,
        certificate := xOneSubX) =>
      `(tactic|
        rr_lw_X_one_sub_X_lag_sequence_realrooted using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          recurrence := $hrec,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_e_positive_t_lag_sequence using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term,
        certificate := xCSubCMulX) =>
      `(tactic|
        rr_lw_X_C_sub_C_mul_X_lag_sequence_auto using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          recurrence := $hrec,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_e_positive_t_lag_sequence_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term,
        certificate := xCSubCMulX) =>
      `(tactic|
        rr_lw_X_C_sub_C_mul_X_lag_sequence_realrooted_auto using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          recurrence := $hrec,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_e_positive_t_lag_sequence using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term,
        certificate := cMulXCSubCMulX) =>
      `(tactic|
        rr_lw_C_mul_X_C_sub_C_mul_X_lag_sequence_auto using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          recurrence := $hrec,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_e_positive_t_lag_sequence_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term,
        certificate := cMulXCSubCMulX) =>
      `(tactic|
        rr_lw_C_mul_X_C_sub_C_mul_X_lag_sequence_realrooted_auto using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          recurrence := $hrec,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_e_positive_t_lag_sequence using
        base := $hbase:term,
        nonneg_coeffs := $hnonneg:term,
        recurrence := $hrec:term,
        certificate := plateauX) =>
      `(tactic|
        rr_prec_pos_X_lag_sequence_auto using
          base := $hbase,
          nonneg_coeffs := $hnonneg,
          recurrence := $hrec)
  | `(tactic|
      rr_e_positive_t_lag_sequence_realrooted using
        base := $hbase:term,
        nonneg_coeffs := $hnonneg:term,
        recurrence := $hrec:term,
        certificate := plateauX) =>
      `(tactic|
        rr_prec_pos_X_lag_sequence_realrooted_auto using
          base := $hbase,
          nonneg_coeffs := $hnonneg,
          recurrence := $hrec)
end Tactic
end RealRooted
