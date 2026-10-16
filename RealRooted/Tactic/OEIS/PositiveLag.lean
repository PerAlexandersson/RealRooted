module

public import RealRooted.Tactic.LiuWang.SequenceProducts
public import RealRooted.Tactic.WagnerX

/-!
# OEIS positive-lag certificate frontend

Parser declarations and dispatch rules for positive t-lag recurrence
certificates. This frontend is independent of denominator normalization and
the degree-two derivative-lag certificate language.
-/

public section

namespace RealRooted
namespace Tactic

/-- Closes `∀ n, StrictInterl (P n) (P (n + 1))` for a positive-lag recurrence
`P (n + 2) = A n * P (n + 1) + T n * P n` whose factors have a shape from the Liu--Wang family;
`certificate` selects the shape of the recurrence: `currentX`, `currentCX`, `currentOneAddX`,
`xOneSubX`, `xCSubCMulX` or
`cMulXCSubCMulX`, and the arguments are the standard certificates `base`,
`pos_lc`, `nonneg_coeffs`, `recurrence`, `degree_succ` and `no_common_roots`. -/
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

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for a positive-lag recurrence whose factors have a
shape from the Liu--Wang family; `certificate` selects the shape of the recurrence: `currentX`,
`currentCX`, `currentOneAddX`, `xOneSubX`, `xCSubCMulX` or
`cMulXCSubCMulX`, and the arguments are the standard certificates `base`,
`pos_lc`, `nonneg_coeffs`, `recurrence`, `degree_succ` and `no_common_roots`. -/
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

/-- Closes `∀ n, StrictInterl (P n) (P (n + 1))` for
`P (n + 2) = C (a n) * P (n + 1) + (C (c n) * X) * P n` with positive `a` and `c`
(`certificate := plateauX`); `a` and `c` are inferred from
`recurrence`, and the arguments are `base`, `nonneg_coeffs` and `recurrence`. -/
syntax (name := rr_e_positive_t_lag_sequence_plateau_x)
  "rr_e_positive_t_lag_sequence" " using "
    "base" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "recurrence" ":=" term ","
    "certificate" ":=" "plateauX" :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for
`P (n + 2) = C (a n) * P (n + 1) + (C (c n) * X) * P n` with positive `a` and `c`
(`certificate := plateauX`); the arguments are `base`, `nonneg_coeffs` and `recurrence`. -/
syntax (name := rr_e_positive_t_lag_sequence_realrooted_plateau_x)
  "rr_e_positive_t_lag_sequence_realrooted" " using "
    "base" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "recurrence" ":=" term ","
    "certificate" ":=" "plateauX" :
  tactic

/-- Closes `∀ n, StrictInterl (P n) (P (n + 1))` for
`P (n + 2) = A n * P (n + 1) + (X * R n) * P n` (`certificate := tR`, as
`rr_lw_tR_lag_sequence`); `factor_nonneg : 0 ≤ (R n).eval r` at every root `r` of `P (n + 1)`,
and the other arguments are the standard certificates `base`, `pos_lc`,
`nonneg_coeffs`, `recurrence`, `degree_succ` and `no_common_roots`. -/
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

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for `P (n + 2) = A n * P (n + 1) + (X * R n) * P n`
(`certificate := tR`, as `rr_lw_tR_lag_sequence_realrooted`); `factor_nonneg : 0 ≤ (R n).eval
r` at every root `r` of `P (n + 1)`, and the other arguments are the standard certificates
`base`, `pos_lc`, `nonneg_coeffs`, `recurrence`, `degree_succ` and `no_common_roots`. -/
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

/-- Closes `∀ n, StrictInterl (P n) (P (n + 1))` for
`P (n + 2) = A n * P (n + 1) + (C (c n) * X * R n) * P n` (`certificate := cTR`, as
`rr_lw_c_tR_lag_sequence`); `coeff_nonneg : 0 ≤ c n`, `factor_nonneg : 0 ≤ (R n).eval
r` at every root `r` of `P (n + 1)`, and the other arguments are the standard certificates
`base`, `pos_lc`, `nonneg_coeffs`, `recurrence`, `degree_succ` and `no_common_roots`. -/
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

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for
`P (n + 2) = A n * P (n + 1) + (C (c n) * X * R n) * P n` (`certificate := cTR`, as
`rr_lw_c_tR_lag_sequence_realrooted`); `coeff_nonneg : 0 ≤ c n`, `factor_nonneg : 0 ≤ (R n).eval
r` at every root `r` of `P (n + 1)`, and the other arguments are the standard certificates
`base`, `pos_lc`, `nonneg_coeffs`, `recurrence`, `degree_succ` and `no_common_roots`. -/
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

/-- Variant of the `cTR` form of `rr_e_positive_t_lag_sequence` with `certificate := cTRAuto`:
the nonnegativity of the scalar coefficients `c n` is proved automatically, so `coeff_nonneg` is
omitted. -/
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

/-- Variant of the `cTR` form of `rr_e_positive_t_lag_sequence_realrooted` with
`certificate := cTRAuto`: the nonnegativity of the scalar coefficients `c n` is proved
automatically, so `coeff_nonneg` is omitted. -/
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
        rr_strict_interl_pos_X_lag_sequence_auto using
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
        rr_strict_interl_pos_X_lag_sequence_realrooted_auto using
          base := $hbase,
          nonneg_coeffs := $hnonneg,
          recurrence := $hrec)
end Tactic
end RealRooted
