module

public import RealRooted.Tactic.LiuWang.Step

/-!
# Quadratic-lag Liu--Wang sequence tactics

Parser declarations and macro implementations for this Liu--Wang tactic family.
-/

public section

namespace RealRooted
namespace Tactic

/-- Closes `∀ n, StrictInterl (P n) (P (n + 1))` for
`P (n + 2) = A n * P (n + 1) + (-(X ^ 2 + C (b n) * X + C (c n))) * P n`;
`discriminant : ∀ n, b n ^ 2 ≤ 4 * c n`, and the standard certificates `base`, `pos_lc`,
`recurrence`, `degree_succ` and `no_common_roots`. -/
syntax (name := rr_lw_negative_monic_quadratic_sequence_named)
  "rr_lw_negative_monic_quadratic_sequence" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "discriminant" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for
`P (n + 2) = A n * P (n + 1) + (-(X ^ 2 + C (b n) * X + C (c n))) * P n`;
`discriminant : ∀ n, b n ^ 2 ≤ 4 * c n`, and the standard certificates `base`, `pos_lc`,
`recurrence`, `degree_succ` and `no_common_roots`. -/
syntax (name := rr_lw_negative_monic_quadratic_sequence_realrooted_named)
  "rr_lw_negative_monic_quadratic_sequence_realrooted" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "discriminant" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `∀ n, StrictInterl (P n) (P (n + 1))` for
`P (n + 2) = A n * P (n + 1) + (-(X ^ 2 + C (b n) * X + C (c n))) * P n`; the discriminant
condition is proved by `rr_lw_quadratic_discriminant`, and the arguments are the standard
certificates `base`, `pos_lc`, `recurrence`, `degree_succ` and `no_common_roots`. -/
syntax (name := rr_lw_negative_monic_quadratic_sequence_auto_named)
  "rr_lw_negative_monic_quadratic_sequence_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for
`P (n + 2) = A n * P (n + 1) + (-(X ^ 2 + C (b n) * X + C (c n))) * P n`; the discriminant
condition is proved by `rr_lw_quadratic_discriminant`, and the arguments are the standard
certificates `base`, `pos_lc`, `recurrence`, `degree_succ` and `no_common_roots`. -/
syntax (name := rr_lw_negative_monic_quadratic_sequence_realrooted_auto_named)
  "rr_lw_negative_monic_quadratic_sequence_realrooted_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `∀ n, StrictInterl (P n) (P (n + 1))` for `P (n + 2) = A n * P (n + 1) + (-(C (a n) *
X ^ 2 + C (b n) * X + C (c n))) * P n`; the arguments are `leading_nonneg`, `constant_nonneg`
and `discriminant : ∀ n, b n ^ 2 ≤ 4 * a n * c n`, and the standard certificates
`base`, `pos_lc`, `recurrence`, `degree_succ` and `no_common_roots`. -/
syntax (name := rr_lw_negative_quadratic_sequence_named)
  "rr_lw_negative_quadratic_sequence" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "leading_nonneg" ":=" term ","
    "constant_nonneg" ":=" term ","
    "discriminant" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for `P (n + 2) = A n * P (n + 1) + (-(C (a n) * X ^ 2 +
C (b n) * X + C (c n))) * P n`; the arguments are `leading_nonneg`, `constant_nonneg` and
`discriminant : ∀ n, b n ^ 2 ≤ 4 * a n * c n`, and the standard certificates `base`, `pos_lc`,
`recurrence`, `degree_succ` and `no_common_roots`. -/
syntax (name := rr_lw_negative_quadratic_sequence_realrooted_named)
  "rr_lw_negative_quadratic_sequence_realrooted" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "leading_nonneg" ":=" term ","
    "constant_nonneg" ":=" term ","
    "discriminant" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `∀ n, StrictInterl (P n) (P (n + 1))` for `P (n + 2) = A n * P (n + 1) + (-(C (a n) *
X ^ 2 + C (b n) * X + C (c n))) * P n`; the sign conditions are proved by
`rr_lw_negative_quadratic_side`, and the arguments are the standard certificates `base`,
`pos_lc`, `recurrence`, `degree_succ` and `no_common_roots`. -/
syntax (name := rr_lw_negative_quadratic_sequence_auto_named)
  "rr_lw_negative_quadratic_sequence_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for `P (n + 2) = A n * P (n + 1) + (-(C (a n) * X ^ 2 +
C (b n) * X + C (c n))) * P n`; the sign conditions are proved by
`rr_lw_negative_quadratic_side`, and the arguments are the standard certificates `base`,
`pos_lc`, `recurrence`, `degree_succ` and `no_common_roots`. -/
syntax (name := rr_lw_negative_quadratic_sequence_realrooted_auto_named)
  "rr_lw_negative_quadratic_sequence_realrooted_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `∀ n, StrictInterl (P n) (P (n + 1))` for the quadratic lag recurrence of
`rr_lw_negative_quadratic_sequence` given with a common denominator `den`:
`raw_recurrence` has the raw coefficients `raw_leading`, `raw_linear` and `raw_constant`, and
`leading`, `linear` and
`constant` are the normalized ones. The sign conditions are `leading_nonneg`,
`constant_nonneg` and `discriminant : ∀ n, b n ^ 2 ≤ 4 * a n * c
n`. The equations are `den_nonzero`, `leading_coeff_eq`, `linear_coeff_eq` and
`constant_coeff_eq`. -/
syntax (name := rr_lw_negative_quadratic_sequence_den_coeff_split_named)
  "rr_lw_negative_quadratic_sequence_den_coeff_split" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "leading" ":=" term ","
    "linear" ":=" term ","
    "constant" ":=" term ","
    "raw_leading" ":=" term ","
    "raw_linear" ":=" term ","
    "raw_constant" ":=" term ","
    "den" ":=" term ","
    "leading_nonneg" ":=" term ","
    "constant_nonneg" ":=" term ","
    "discriminant" ":=" term ","
    "den_nonzero" ":=" term ","
    "leading_coeff_eq" ":=" term ","
    "linear_coeff_eq" ":=" term ","
    "constant_coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `∀ n, StrictInterl (P n) (P (n + 1))` for the quadratic lag recurrence of
`rr_lw_negative_quadratic_sequence` given with a common denominator `den`:
`raw_recurrence` has the raw coefficients `raw_leading`, `raw_linear` and `raw_constant`, and
`leading`, `linear` and
`constant` are the normalized ones. The sign conditions are `leading_nonneg`,
`constant_nonneg` and `discriminant : ∀ n, b n ^ 2 ≤ 4 * a n * c n`. The denominator and
coefficient equations are proved automatically. -/
syntax (name := rr_lw_negative_quadratic_sequence_den_coeff_split_scalar_named)
  "rr_lw_negative_quadratic_sequence_den_coeff_split" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "leading" ":=" term ","
    "linear" ":=" term ","
    "constant" ":=" term ","
    "raw_leading" ":=" term ","
    "raw_linear" ":=" term ","
    "raw_constant" ":=" term ","
    "den" ":=" term ","
    "leading_nonneg" ":=" term ","
    "constant_nonneg" ":=" term ","
    "discriminant" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `∀ n, StrictInterl (P n) (P (n + 1))` for the quadratic lag recurrence of
`rr_lw_negative_quadratic_sequence` given with a common denominator `den`:
`raw_recurrence` has the raw coefficients `raw_leading`, `raw_linear` and `raw_constant`, and
`leading`, `linear` and `constant` are the normalized ones. The sign conditions are proved
automatically. The equations are `den_nonzero`, `leading_coeff_eq`, `linear_coeff_eq` and
`constant_coeff_eq`. -/
syntax (name := rr_lw_negative_quadratic_sequence_den_coeff_auto_split_named)
  "rr_lw_negative_quadratic_sequence_den_coeff_auto_split" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "leading" ":=" term ","
    "linear" ":=" term ","
    "constant" ":=" term ","
    "raw_leading" ":=" term ","
    "raw_linear" ":=" term ","
    "raw_constant" ":=" term ","
    "den" ":=" term ","
    ("den_nonzero" ":=" term ",")?
    "leading_coeff_eq" ":=" term ","
    "linear_coeff_eq" ":=" term ","
    "constant_coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `∀ n, StrictInterl (P n) (P (n + 1))` for the quadratic lag recurrence of
`rr_lw_negative_quadratic_sequence` given with a common denominator `den`:
`raw_recurrence` has the raw coefficients `raw_leading`, `raw_linear` and `raw_constant`, and
`leading`, `linear` and `constant` are the normalized ones. The sign conditions are proved
automatically. The denominator and coefficient equations are proved automatically. -/
syntax (name := rr_lw_negative_quadratic_sequence_den_coeff_auto_split_scalar_named)
  "rr_lw_negative_quadratic_sequence_den_coeff_auto_split" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "leading" ":=" term ","
    "linear" ":=" term ","
    "constant" ":=" term ","
    "raw_leading" ":=" term ","
    "raw_linear" ":=" term ","
    "raw_constant" ":=" term ","
    "den" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for the quadratic lag recurrence of
`rr_lw_negative_quadratic_sequence` given with a common denominator `den`:
`raw_recurrence` has the raw coefficients `raw_leading`, `raw_linear` and `raw_constant`, and
`leading`, `linear` and
`constant` are the normalized ones. The sign conditions are `leading_nonneg`,
`constant_nonneg` and `discriminant : ∀ n, b n ^ 2 ≤ 4 * a n * c
n`. The equations are `den_nonzero`, `leading_coeff_eq`, `linear_coeff_eq` and
`constant_coeff_eq`. -/
syntax (name := rr_lw_negative_quadratic_sequence_den_coeff_realrooted_split_named)
  "rr_lw_negative_quadratic_sequence_den_coeff_realrooted_split" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "leading" ":=" term ","
    "linear" ":=" term ","
    "constant" ":=" term ","
    "raw_leading" ":=" term ","
    "raw_linear" ":=" term ","
    "raw_constant" ":=" term ","
    "den" ":=" term ","
    "leading_nonneg" ":=" term ","
    "constant_nonneg" ":=" term ","
    "discriminant" ":=" term ","
    "den_nonzero" ":=" term ","
    "leading_coeff_eq" ":=" term ","
    "linear_coeff_eq" ":=" term ","
    "constant_coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for the quadratic lag recurrence of
`rr_lw_negative_quadratic_sequence` given with a common denominator `den`:
`raw_recurrence` has the raw coefficients `raw_leading`, `raw_linear` and `raw_constant`, and
`leading`, `linear` and
`constant` are the normalized ones. The sign conditions are `leading_nonneg`,
`constant_nonneg` and `discriminant : ∀ n, b n ^ 2 ≤ 4 * a n * c n`. The denominator and
coefficient equations are proved automatically. -/
syntax (name := rr_lw_negative_quadratic_sequence_den_coeff_realrooted_split_scalar_named)
  "rr_lw_negative_quadratic_sequence_den_coeff_realrooted_split" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "leading" ":=" term ","
    "linear" ":=" term ","
    "constant" ":=" term ","
    "raw_leading" ":=" term ","
    "raw_linear" ":=" term ","
    "raw_constant" ":=" term ","
    "den" ":=" term ","
    "leading_nonneg" ":=" term ","
    "constant_nonneg" ":=" term ","
    "discriminant" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for the quadratic lag recurrence of
`rr_lw_negative_quadratic_sequence` given with a common denominator `den`:
`raw_recurrence` has the raw coefficients `raw_leading`, `raw_linear` and `raw_constant`, and
`leading`, `linear` and `constant` are the normalized ones. The sign conditions are proved
automatically. The equations are `den_nonzero`, `leading_coeff_eq`, `linear_coeff_eq` and
`constant_coeff_eq`. -/
syntax (name := rr_lw_negative_quadratic_sequence_den_coeff_realrooted_auto_split_named)
  "rr_lw_negative_quadratic_sequence_den_coeff_realrooted_auto_split" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "leading" ":=" term ","
    "linear" ":=" term ","
    "constant" ":=" term ","
    "raw_leading" ":=" term ","
    "raw_linear" ":=" term ","
    "raw_constant" ":=" term ","
    "den" ":=" term ","
    ("den_nonzero" ":=" term ",")?
    "leading_coeff_eq" ":=" term ","
    "linear_coeff_eq" ":=" term ","
    "constant_coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for the quadratic lag recurrence of
`rr_lw_negative_quadratic_sequence` given with a common denominator `den`:
`raw_recurrence` has the raw coefficients `raw_leading`, `raw_linear` and `raw_constant`, and
`leading`, `linear` and `constant` are the normalized ones. The sign conditions are proved
automatically. The denominator and coefficient equations are proved automatically. -/
syntax (name := rr_lw_negative_quadratic_sequence_den_coeff_realrooted_auto_split_scalar_named)
  "rr_lw_negative_quadratic_sequence_den_coeff_realrooted_auto_split" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "leading" ":=" term ","
    "linear" ":=" term ","
    "constant" ":=" term ","
    "raw_leading" ":=" term ","
    "raw_linear" ":=" term ","
    "raw_constant" ":=" term ","
    "den" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

macro_rules
  | `(tactic|
      rr_lw_negative_monic_quadratic_sequence using
        base := $hbase:term,
        pos_lc := $hpos:term,
        discriminant := $hdisc:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact RealRooted.LiuWang.strictInterl_negative_monic_quadratic_lag_sequence
          $hbase $hpos $hdisc $hrec $hdeg_succ $hno)
  | `(tactic|
      rr_lw_negative_monic_quadratic_sequence_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        discriminant := $hdisc:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.LiuWang.isRealRooted_of_negative_monic_quadratic_lag_sequence
            $hbase $hpos $hdisc $hrec $hdeg_succ $hno))
  | `(tactic|
      rr_lw_negative_monic_quadratic_sequence_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact RealRooted.LiuWang.strictInterl_negative_monic_quadratic_lag_sequence
          $hbase $hpos rr_lw_quadratic_discriminant $hrec $hdeg_succ $hno)
  | `(tactic|
      rr_lw_negative_monic_quadratic_sequence_realrooted_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.LiuWang.isRealRooted_of_negative_monic_quadratic_lag_sequence
            $hbase $hpos rr_lw_quadratic_discriminant $hrec $hdeg_succ $hno))
  | `(tactic|
      rr_lw_negative_quadratic_sequence using
        base := $hbase:term,
        pos_lc := $hpos:term,
        leading_nonneg := $ha:term,
        constant_nonneg := $hc:term,
        discriminant := $hdisc:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact RealRooted.LiuWang.strictInterl_negative_quadratic_lag_sequence
          $hbase $hpos $ha $hc $hdisc $hrec $hdeg_succ $hno)
  | `(tactic|
      rr_lw_negative_quadratic_sequence_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        leading_nonneg := $ha:term,
        constant_nonneg := $hc:term,
        discriminant := $hdisc:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.LiuWang.isRealRooted_of_negative_quadratic_lag_sequence
            $hbase $hpos $ha $hc $hdisc $hrec $hdeg_succ $hno))
  | `(tactic|
      rr_lw_negative_quadratic_sequence_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact RealRooted.LiuWang.strictInterl_negative_quadratic_lag_sequence
          (hrec := $hrec) $hbase $hpos
          rr_lw_negative_quadratic_side rr_lw_negative_quadratic_side
          rr_lw_negative_quadratic_side $hdeg_succ $hno)
  | `(tactic|
      rr_lw_negative_quadratic_sequence_realrooted_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        (have hcertificate :=
          RealRooted.LiuWang.isRealRooted_of_negative_quadratic_lag_sequence
            (hrec := $hrec) $hbase $hpos
            rr_lw_negative_quadratic_side rr_lw_negative_quadratic_side
            rr_lw_negative_quadratic_side $hdeg_succ $hno
         rr_exact_realrooted_sequence_or_projection hcertificate))
  | `(tactic|
      rr_lw_negative_quadratic_sequence_den_coeff_split using
        base := $hbase:term,
        pos_lc := $hpos:term,
        leading := $a:term,
        linear := $b:term,
        constant := $c:term,
        raw_leading := $araw:term,
        raw_linear := $braw:term,
        raw_constant := $craw:term,
        den := $d:term,
        leading_nonneg := $ha:term,
        constant_nonneg := $hc:term,
        discriminant := $hdisc:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_negative_quadratic_sequence_den_coeff_split using
          base := $hbase,
          pos_lc := $hpos,
          leading := $a,
          linear := $b,
          constant := $c,
          raw_leading := $araw,
          raw_linear := $braw,
          raw_constant := $craw,
          den := $d,
          leading_nonneg := $ha,
          constant_nonneg := $hc,
          discriminant := $hdisc,
          den_nonzero := rr_lw_active_den_all_term,
          leading_coeff_eq := rr_lw_coeff_all_term,
          linear_coeff_eq := rr_lw_coeff_all_term,
          constant_coeff_eq := rr_lw_coeff_all_term,
          raw_recurrence := $hraw,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_negative_quadratic_sequence_den_coeff_split using
        base := $hbase:term,
        pos_lc := $hpos:term,
        leading := $a:term,
        linear := $b:term,
        constant := $c:term,
        raw_leading := $araw:term,
        raw_linear := $braw:term,
        raw_constant := $craw:term,
        den := $d:term,
        leading_nonneg := $ha:term,
        constant_nonneg := $hc:term,
        discriminant := $hdisc:term,
        den_nonzero := $hden:term,
        leading_coeff_eq := $ha_coeff:term,
        linear_coeff_eq := $hb_coeff:term,
        constant_coeff_eq := $hc_coeff:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact
          RealRooted.LiuWang.strictInterl_negative_quadratic_lag_sequence_den_coeff
            (araw := $araw) (braw := $braw) (craw := $craw)
            (a := $a) (b := $b) (c := $c) (d := $d)
            $hbase $hpos $ha $hc $hdisc $hden $ha_coeff $hb_coeff $hc_coeff
            $hraw $hdeg_succ $hno)
  | `(tactic|
      rr_lw_negative_quadratic_sequence_den_coeff_auto_split using
        base := $hbase:term,
        pos_lc := $hpos:term,
        leading := $a:term,
        linear := $b:term,
        constant := $c:term,
        raw_leading := $araw:term,
        raw_linear := $braw:term,
        raw_constant := $craw:term,
        den := $d:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_negative_quadratic_sequence_den_coeff_auto_split using
          base := $hbase,
          pos_lc := $hpos,
          leading := $a,
          linear := $b,
          constant := $c,
          raw_leading := $araw,
          raw_linear := $braw,
          raw_constant := $craw,
          den := $d,
          den_nonzero := rr_lw_active_den_all_term,
          leading_coeff_eq := rr_lw_coeff_all_term,
          linear_coeff_eq := rr_lw_coeff_all_term,
          constant_coeff_eq := rr_lw_coeff_all_term,
          raw_recurrence := $hraw,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_negative_quadratic_sequence_den_coeff_auto_split using
        base := $hbase:term,
        pos_lc := $hpos:term,
        leading := $a:term,
        linear := $b:term,
        constant := $c:term,
        raw_leading := $araw:term,
        raw_linear := $braw:term,
        raw_constant := $craw:term,
        den := $d:term,
        leading_coeff_eq := $ha_coeff:term,
        linear_coeff_eq := $hb_coeff:term,
        constant_coeff_eq := $hc_coeff:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_negative_quadratic_sequence_den_coeff_auto_split using
          base := $hbase,
          pos_lc := $hpos,
          leading := $a,
          linear := $b,
          constant := $c,
          raw_leading := $araw,
          raw_linear := $braw,
          raw_constant := $craw,
          den := $d,
          den_nonzero := rr_lw_active_den_all_term,
          leading_coeff_eq := $ha_coeff,
          linear_coeff_eq := $hb_coeff,
          constant_coeff_eq := $hc_coeff,
          raw_recurrence := $hraw,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_negative_quadratic_sequence_den_coeff_auto_split using
        base := $hbase:term,
        pos_lc := $hpos:term,
        leading := $a:term,
        linear := $b:term,
        constant := $c:term,
        raw_leading := $araw:term,
        raw_linear := $braw:term,
        raw_constant := $craw:term,
        den := $d:term,
        den_nonzero := $hden:term,
        leading_coeff_eq := $ha_coeff:term,
        linear_coeff_eq := $hb_coeff:term,
        constant_coeff_eq := $hc_coeff:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact
          RealRooted.LiuWang.strictInterl_negative_quadratic_lag_sequence_den_coeff
            (araw := $araw) (braw := $braw) (craw := $craw)
            (a := $a) (b := $b) (c := $c) (d := $d)
            $hbase $hpos rr_lw_negative_quadratic_side rr_lw_negative_quadratic_side
            rr_lw_negative_quadratic_side $hden $ha_coeff $hb_coeff $hc_coeff $hraw
            $hdeg_succ $hno)
  | `(tactic|
      rr_lw_negative_quadratic_sequence_den_coeff_realrooted_split using
        base := $hbase:term,
        pos_lc := $hpos:term,
        leading := $a:term,
        linear := $b:term,
        constant := $c:term,
        raw_leading := $araw:term,
        raw_linear := $braw:term,
        raw_constant := $craw:term,
        den := $d:term,
        leading_nonneg := $ha:term,
        constant_nonneg := $hc:term,
        discriminant := $hdisc:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_negative_quadratic_sequence_den_coeff_realrooted_split using
          base := $hbase,
          pos_lc := $hpos,
          leading := $a,
          linear := $b,
          constant := $c,
          raw_leading := $araw,
          raw_linear := $braw,
          raw_constant := $craw,
          den := $d,
          leading_nonneg := $ha,
          constant_nonneg := $hc,
          discriminant := $hdisc,
          den_nonzero := rr_lw_active_den_all_term,
          leading_coeff_eq := rr_lw_coeff_all_term,
          linear_coeff_eq := rr_lw_coeff_all_term,
          constant_coeff_eq := rr_lw_coeff_all_term,
          raw_recurrence := $hraw,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_negative_quadratic_sequence_den_coeff_realrooted_split using
        base := $hbase:term,
        pos_lc := $hpos:term,
        leading := $a:term,
        linear := $b:term,
        constant := $c:term,
        raw_leading := $araw:term,
        raw_linear := $braw:term,
        raw_constant := $craw:term,
        den := $d:term,
        leading_nonneg := $ha:term,
        constant_nonneg := $hc:term,
        discriminant := $hdisc:term,
        den_nonzero := $hden:term,
        leading_coeff_eq := $ha_coeff:term,
        linear_coeff_eq := $hb_coeff:term,
        constant_coeff_eq := $hc_coeff:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.LiuWang.isRealRooted_of_negative_quadratic_lag_sequence_den_coeff
            (araw := $araw) (braw := $braw) (craw := $craw)
            (a := $a) (b := $b) (c := $c) (d := $d)
            $hbase $hpos $ha $hc $hdisc $hden $ha_coeff $hb_coeff $hc_coeff
            $hraw $hdeg_succ $hno))
  | `(tactic|
      rr_lw_negative_quadratic_sequence_den_coeff_realrooted_auto_split using
        base := $hbase:term,
        pos_lc := $hpos:term,
        leading := $a:term,
        linear := $b:term,
        constant := $c:term,
        raw_leading := $araw:term,
        raw_linear := $braw:term,
        raw_constant := $craw:term,
        den := $d:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_negative_quadratic_sequence_den_coeff_realrooted_auto_split using
          base := $hbase,
          pos_lc := $hpos,
          leading := $a,
          linear := $b,
          constant := $c,
          raw_leading := $araw,
          raw_linear := $braw,
          raw_constant := $craw,
          den := $d,
          den_nonzero := rr_lw_active_den_all_term,
          leading_coeff_eq := rr_lw_coeff_all_term,
          linear_coeff_eq := rr_lw_coeff_all_term,
          constant_coeff_eq := rr_lw_coeff_all_term,
          raw_recurrence := $hraw,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_negative_quadratic_sequence_den_coeff_realrooted_auto_split using
        base := $hbase:term,
        pos_lc := $hpos:term,
        leading := $a:term,
        linear := $b:term,
        constant := $c:term,
        raw_leading := $araw:term,
        raw_linear := $braw:term,
        raw_constant := $craw:term,
        den := $d:term,
        leading_coeff_eq := $ha_coeff:term,
        linear_coeff_eq := $hb_coeff:term,
        constant_coeff_eq := $hc_coeff:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_negative_quadratic_sequence_den_coeff_realrooted_auto_split using
          base := $hbase,
          pos_lc := $hpos,
          leading := $a,
          linear := $b,
          constant := $c,
          raw_leading := $araw,
          raw_linear := $braw,
          raw_constant := $craw,
          den := $d,
          den_nonzero := rr_lw_active_den_all_term,
          leading_coeff_eq := $ha_coeff,
          linear_coeff_eq := $hb_coeff,
          constant_coeff_eq := $hc_coeff,
          raw_recurrence := $hraw,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_negative_quadratic_sequence_den_coeff_realrooted_auto_split using
        base := $hbase:term,
        pos_lc := $hpos:term,
        leading := $a:term,
        linear := $b:term,
        constant := $c:term,
        raw_leading := $araw:term,
        raw_linear := $braw:term,
        raw_constant := $craw:term,
        den := $d:term,
        den_nonzero := $hden:term,
        leading_coeff_eq := $ha_coeff:term,
        linear_coeff_eq := $hb_coeff:term,
        constant_coeff_eq := $hc_coeff:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.LiuWang.isRealRooted_of_negative_quadratic_lag_sequence_den_coeff
            (araw := $araw) (braw := $braw) (craw := $craw)
            (a := $a) (b := $b) (c := $c) (d := $d)
            $hbase $hpos rr_lw_negative_quadratic_side rr_lw_negative_quadratic_side
            rr_lw_negative_quadratic_side $hden $ha_coeff $hb_coeff $hc_coeff $hraw
            $hdeg_succ $hno))

end Tactic
end RealRooted
