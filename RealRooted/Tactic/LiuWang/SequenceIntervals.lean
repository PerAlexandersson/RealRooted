module

public import RealRooted.Tactic.LiuWang.Step

/-!
# Interval-lag Liu--Wang sequence tactics

Parser declarations and macro implementations for this Liu--Wang tactic family.
-/

public section

namespace RealRooted
namespace Tactic

/-- Denominator-fused form of the `-(C (c n)) * (1 + X)` lag on the inner root window `[-1, 0]`: it
closes `∀ n, StrictInterl (P n) (P (n + 1))` from
`raw_recurrence : C (d n) * P (n + 2) = C (d n) * (A n * P (n + 1)) + (C (b n) * (1 + X)) * P n`,
where `d n ≠ 0` and `(d n)⁻¹ * b n = -c n`. The arguments are the standard certificates `base`,
`pos_lc`, `nonneg_coeffs`, `raw_recurrence`, `degree_succ` and `no_common_roots` (as for
`rr_lw_positive_X_mul_sequence`), together with `coeff`, the sequence `c`; `coeff_nonneg : 0 ≤ c n`;
`root_lower : -1 ≤ r` at every root `r` of `P (n + 1)`; `den_nonzero : d n ≠ 0`; and
`coeff_eq : (d n)⁻¹ * b n = -c n`. -/
syntax (name := rr_lw_neg_C_mul_one_add_X_lag_sequence_den_coeff_nonneg_named)
  "rr_lw_neg_C_mul_one_add_X_lag_sequence_den_coeff_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "coeff" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "root_lower" ":=" term ","
    "den_nonzero" ":=" term ","
    "coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Denominator-fused form of the `-(C (c n)) * (1 + X)` lag on the inner root window `[-1, 0]`: it
closes `∀ n, StrictInterl (P n) (P (n + 1))` from
`raw_recurrence : C (d n) * P (n + 2) = C (d n) * (A n * P (n + 1)) + (C (b n) * (1 + X)) * P n`,
where `d n ≠ 0` and `(d n)⁻¹ * b n = -c n`. The arguments are the standard certificates `base`,
`pos_lc`, `nonneg_coeffs`, `raw_recurrence`, `degree_succ` and `no_common_roots` (as for
`rr_lw_positive_X_mul_sequence`), together with `coeff`, the sequence `c`; `coeff_nonneg : 0 ≤ c n`;
and `root_lower : -1 ≤ r` at every root `r` of `P (n + 1)`. The scalar side conditions `d n ≠ 0` and
`(d n)⁻¹ * b n = -c n` are proved automatically. -/
syntax (name := rr_lw_neg_C_mul_one_add_X_lag_sequence_den_coeff_nonneg_scalar_named)
  "rr_lw_neg_C_mul_one_add_X_lag_sequence_den_coeff_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "coeff" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "root_lower" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Denominator-fused form of the `-(C (c n)) * (1 + X)` lag on the inner root window `[-1, 0]`: it
closes `∀ n, StrictInterl (P n) (P (n + 1))` from
`raw_recurrence : C (d n) * P (n + 2) = C (d n) * (A n * P (n + 1)) + (C (b n) * (1 + X)) * P n`,
where `d n ≠ 0` and `(d n)⁻¹ * b n = -c n`. The arguments are the standard certificates `base`,
`pos_lc`, `nonneg_coeffs`, `raw_recurrence`, `degree_succ` and `no_common_roots` (as for
`rr_lw_positive_X_mul_sequence`), together with `coeff`, the sequence `c`; `root_lower : -1 ≤ r` at
every root `r` of `P (n + 1)`; `den_nonzero : d n ≠ 0`; and `coeff_eq : (d n)⁻¹ * b n = -c n`. The
nonnegativity of `c n` is proved automatically. -/
syntax (name := rr_lw_neg_C_mul_one_add_X_lag_sequence_den_coeff_nonneg_auto_named)
  "rr_lw_neg_C_mul_one_add_X_lag_sequence_den_coeff_nonneg_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "coeff" ":=" term ","
    "root_lower" ":=" term ","
    "den_nonzero" ":=" term ","
    "coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Denominator-fused form of the `-(C (c n)) * (1 + X)` lag on the inner root window `[-1, 0]`: it
closes `∀ n, StrictInterl (P n) (P (n + 1))` from
`raw_recurrence : C (d n) * P (n + 2) = C (d n) * (A n * P (n + 1)) + (C (b n) * (1 + X)) * P n`,
where `d n ≠ 0` and `(d n)⁻¹ * b n = -c n`. The arguments are the standard certificates `base`,
`pos_lc`, `nonneg_coeffs`, `raw_recurrence`, `degree_succ` and `no_common_roots` (as for
`rr_lw_positive_X_mul_sequence`), together with `coeff`, the sequence `c`; and `root_lower : -1 ≤ r`
at every root `r` of `P (n + 1)`. The scalar side conditions `d n ≠ 0` and `(d n)⁻¹ * b n = -c n`,
as well as the nonnegativity of `c n`, are proved automatically. -/
syntax (name := rr_lw_neg_C_mul_one_add_X_lag_sequence_den_coeff_nonneg_auto_scalar_named)
  "rr_lw_neg_C_mul_one_add_X_lag_sequence_den_coeff_nonneg_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "coeff" ":=" term ","
    "root_lower" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Denominator-fused form of the `-(C (c n)) * (1 + X)` lag on the inner root window `[-1, 0]`: it
closes `∀ n, P n ≠ 0 ∧ (P n).Splits` from
`raw_recurrence : C (d n) * P (n + 2) = C (d n) * (A n * P (n + 1)) + (C (b n) * (1 + X)) * P n`,
where `d n ≠ 0` and `(d n)⁻¹ * b n = -c n`. The arguments are the standard certificates `base`,
`pos_lc`, `nonneg_coeffs`, `raw_recurrence`, `degree_succ` and `no_common_roots` (as for
`rr_lw_positive_X_mul_sequence`), together with `coeff`, the sequence `c`; `coeff_nonneg : 0 ≤ c n`;
`root_lower : -1 ≤ r` at every root `r` of `P (n + 1)`; `den_nonzero : d n ≠ 0`; and
`coeff_eq : (d n)⁻¹ * b n = -c n`. -/
syntax (name := rr_lw_neg_C_mul_one_add_X_lag_sequence_den_coeff_realrooted_nonneg_named)
  "rr_lw_neg_C_mul_one_add_X_lag_sequence_den_coeff_realrooted_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "coeff" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "root_lower" ":=" term ","
    "den_nonzero" ":=" term ","
    "coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Denominator-fused form of the `-(C (c n)) * (1 + X)` lag on the inner root window `[-1, 0]`: it
closes `∀ n, P n ≠ 0 ∧ (P n).Splits` from
`raw_recurrence : C (d n) * P (n + 2) = C (d n) * (A n * P (n + 1)) + (C (b n) * (1 + X)) * P n`,
where `d n ≠ 0` and `(d n)⁻¹ * b n = -c n`. The arguments are the standard certificates `base`,
`pos_lc`, `nonneg_coeffs`, `raw_recurrence`, `degree_succ` and `no_common_roots` (as for
`rr_lw_positive_X_mul_sequence`), together with `coeff`, the sequence `c`; `coeff_nonneg : 0 ≤ c n`;
and `root_lower : -1 ≤ r` at every root `r` of `P (n + 1)`. The scalar side conditions `d n ≠ 0` and
`(d n)⁻¹ * b n = -c n` are proved automatically. -/
syntax (name := rr_lw_neg_C_mul_one_add_X_lag_sequence_den_coeff_realrooted_nonneg_scalar_named)
  "rr_lw_neg_C_mul_one_add_X_lag_sequence_den_coeff_realrooted_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "coeff" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "root_lower" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Denominator-fused form of the `-(C (c n)) * (1 + X)` lag on the inner root window `[-1, 0]`: it
closes `∀ n, P n ≠ 0 ∧ (P n).Splits` from
`raw_recurrence : C (d n) * P (n + 2) = C (d n) * (A n * P (n + 1)) + (C (b n) * (1 + X)) * P n`,
where `d n ≠ 0` and `(d n)⁻¹ * b n = -c n`. The arguments are the standard certificates `base`,
`pos_lc`, `nonneg_coeffs`, `raw_recurrence`, `degree_succ` and `no_common_roots` (as for
`rr_lw_positive_X_mul_sequence`), together with `coeff`, the sequence `c`; `root_lower : -1 ≤ r` at
every root `r` of `P (n + 1)`; `den_nonzero : d n ≠ 0`; and `coeff_eq : (d n)⁻¹ * b n = -c n`. The
nonnegativity of `c n` is proved automatically. -/
syntax (name := rr_lw_neg_C_mul_one_add_X_lag_sequence_den_coeff_realrooted_nonneg_auto_named)
  "rr_lw_neg_C_mul_one_add_X_lag_sequence_den_coeff_realrooted_nonneg_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "coeff" ":=" term ","
    "root_lower" ":=" term ","
    "den_nonzero" ":=" term ","
    "coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Denominator-fused form of the `-(C (c n)) * (1 + X)` lag on the inner root window `[-1, 0]`: it
closes `∀ n, P n ≠ 0 ∧ (P n).Splits` from
`raw_recurrence : C (d n) * P (n + 2) = C (d n) * (A n * P (n + 1)) + (C (b n) * (1 + X)) * P n`,
where `d n ≠ 0` and `(d n)⁻¹ * b n = -c n`. The arguments are the standard certificates `base`,
`pos_lc`, `nonneg_coeffs`, `raw_recurrence`, `degree_succ` and `no_common_roots` (as for
`rr_lw_positive_X_mul_sequence`), together with `coeff`, the sequence `c`; and `root_lower : -1 ≤ r`
at every root `r` of `P (n + 1)`. The scalar side conditions `d n ≠ 0` and `(d n)⁻¹ * b n = -c n`,
as well as the nonnegativity of `c n`, are proved automatically. -/
syntax
  (name := rr_lw_neg_C_mul_one_add_X_lag_sequence_den_coeff_realrooted_nonneg_auto_scalar_named)
  "rr_lw_neg_C_mul_one_add_X_lag_sequence_den_coeff_realrooted_nonneg_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "coeff" ":=" term ","
    "root_lower" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

macro_rules
  | `(tactic|
      rr_lw_neg_C_mul_one_add_X_lag_sequence_den_coeff_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        coeff := $c:term,
        coeff_nonneg := $hc:term,
        root_lower := $hroot_lower:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_neg_C_mul_one_add_X_lag_sequence_den_coeff_nonneg using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          coeff := $c,
          coeff_nonneg := $hc,
          root_lower := $hroot_lower,
          den_nonzero := rr_lw_active_den_all_term,
          coeff_eq := rr_lw_coeff_all_term,
          raw_recurrence := $hraw,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_neg_C_mul_one_add_X_lag_sequence_den_coeff_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        coeff := $c:term,
        coeff_nonneg := $hc:term,
        root_lower := $hroot_lower:term,
        den_nonzero := $hden:term,
        coeff_eq := $hcoeff:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact
          LiuWang.strictInterl_neg_C_mul_one_add_X_lag_sequence_den_coeff_of_nonneg_coeffs
            (c := $c) $hbase $hpos $hnonneg $hc $hroot_lower $hden $hcoeff
            $hraw $hdeg_succ $hno)
  | `(tactic|
      rr_lw_neg_C_mul_one_add_X_lag_sequence_den_coeff_nonneg_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        coeff := $c:term,
        root_lower := $hroot_lower:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_neg_C_mul_one_add_X_lag_sequence_den_coeff_nonneg_auto using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          coeff := $c,
          root_lower := $hroot_lower,
          den_nonzero := rr_lw_active_den_all_term,
          coeff_eq := rr_lw_coeff_all_term,
          raw_recurrence := $hraw,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_neg_C_mul_one_add_X_lag_sequence_den_coeff_nonneg_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        coeff := $c:term,
        root_lower := $hroot_lower:term,
        den_nonzero := $hden:term,
        coeff_eq := $hcoeff:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_refine_active_nonneg_seq
          (LiuWang.strictInterl_neg_C_mul_one_add_X_lag_sequence_den_coeff_of_nonneg_coeffs
            (c := $c) $hbase $hpos $hnonneg ?_ $hroot_lower $hden $hcoeff
            $hraw $hdeg_succ $hno))
  | `(tactic|
      rr_lw_neg_C_mul_one_add_X_lag_sequence_den_coeff_realrooted_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        coeff := $c:term,
        coeff_nonneg := $hc:term,
        root_lower := $hroot_lower:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_neg_C_mul_one_add_X_lag_sequence_den_coeff_realrooted_nonneg using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          coeff := $c,
          coeff_nonneg := $hc,
          root_lower := $hroot_lower,
          den_nonzero := rr_lw_active_den_all_term,
          coeff_eq := rr_lw_coeff_all_term,
          raw_recurrence := $hraw,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_neg_C_mul_one_add_X_lag_sequence_den_coeff_realrooted_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        coeff := $c:term,
        coeff_nonneg := $hc:term,
        root_lower := $hroot_lower:term,
        den_nonzero := $hden:term,
        coeff_eq := $hcoeff:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (LiuWang.isRealRooted_of_neg_C_mul_one_add_X_lag_sequence_den_coeff_of_nonneg_coeffs
            (c := $c) $hbase $hpos $hnonneg $hc $hroot_lower $hden $hcoeff
            $hraw $hdeg_succ $hno))
  | `(tactic|
      rr_lw_neg_C_mul_one_add_X_lag_sequence_den_coeff_realrooted_nonneg_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        coeff := $c:term,
        root_lower := $hroot_lower:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_neg_C_mul_one_add_X_lag_sequence_den_coeff_realrooted_nonneg_auto using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          coeff := $c,
          root_lower := $hroot_lower,
          den_nonzero := rr_lw_active_den_all_term,
          coeff_eq := rr_lw_coeff_all_term,
          raw_recurrence := $hraw,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_neg_C_mul_one_add_X_lag_sequence_den_coeff_realrooted_nonneg_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        coeff := $c:term,
        root_lower := $hroot_lower:term,
        den_nonzero := $hden:term,
        coeff_eq := $hcoeff:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_exact_realrooted_active_nonneg_seq
          (LiuWang.isRealRooted_of_neg_C_mul_one_add_X_lag_sequence_den_coeff_of_nonneg_coeffs
            (c := $c) $hbase $hpos $hnonneg ?_ $hroot_lower $hden $hcoeff
            $hraw $hdeg_succ $hno))

end Tactic
end RealRooted
