import RealRooted.Tactic.LiuWang.SequenceNonpositive
import RealRooted.Tactic.LiuWang.SequenceQuadratic
import RealRooted.Tactic.OEIS.Basic

/-!
# OEIS negative-lag certificate frontend

Parser declarations and dispatch rules for global-nonpositive, square, and
quadratic negative-lag certificates, including denominator normalization.
-/

namespace RealRooted
namespace Tactic

/-- Closes `∀ n, StrictInterl (P n) (P (n + 1))` for a Liu--Wang lag recurrence whose lag factor
is negative; `certificate` selects the shape of the lag factor `B n`: `negativeSquare`
(`-(C (c n)) * (q n) ^ 2`), `negativeMonicQuadratic` or `negativeQuadratic`, and the arguments
are the standard certificates `base`, `pos_lc`, `degree_succ` and `no_common_roots` and
`recurrence`. -/
syntax (name := rr_g_negative_lag_sequence_auto)
  "rr_g_negative_lag_sequence" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term ","
    "certificate" ":="
      ("negativeSquare" <|> "negativeMonicQuadratic" <|> "negativeQuadratic") :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for a Liu--Wang lag recurrence whose lag factor is
negative; `certificate` selects the shape of the lag factor `B n`: `negativeSquare`
(`-(C (c n)) * (q n) ^ 2`), `negativeMonicQuadratic` or `negativeQuadratic`, and the arguments
are the standard certificates `base`, `pos_lc`, `degree_succ` and `no_common_roots` and
`recurrence`. -/
syntax (name := rr_g_negative_lag_sequence_realrooted_auto)
  "rr_g_negative_lag_sequence_realrooted" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term ","
    "certificate" ":="
      ("negativeSquare" <|> "negativeMonicQuadratic" <|> "negativeQuadratic") :
  tactic

/-- Closes `∀ n, StrictInterl (P n) (P (n + 1))` for a Liu--Wang lag recurrence
`P (n + 2) = A n * P (n + 1) + B n * P n` with an arbitrary polynomial `A n`, with
`certificate := globalNonpos`; `lag : B` is the lag coefficient sequence, its sign condition at
the roots is proved automatically, and the other arguments are the standard certificates
`base`, `pos_lc`, `degree_succ` and `no_common_roots` and `recurrence`. -/
syntax (name := rr_g_negative_lag_sequence_global_nonpos)
  "rr_g_negative_lag_sequence" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "lag" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term ","
    "certificate" ":=" "globalNonpos" :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for a Liu--Wang lag recurrence
`P (n + 2) = A n * P (n + 1) + B n * P n` with an arbitrary polynomial `A n`, with
`certificate := globalNonpos`; `lag : B` is the lag coefficient sequence, its sign condition at
the roots is proved automatically, and the other arguments are the standard certificates
`base`, `pos_lc`, `degree_succ` and `no_common_roots` and `recurrence`. -/
syntax (name := rr_g_negative_lag_sequence_realrooted_global_nonpos)
  "rr_g_negative_lag_sequence_realrooted" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "lag" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term ","
    "certificate" ":=" "globalNonpos" :
  tactic

/-- Closes `∀ n, StrictInterl (P n) (P (n + 1))` for a Liu--Wang lag recurrence
`P (n + 2) = A n * P (n + 1) + B n * P n` with an arbitrary polynomial `A n` given with a
denominator by `raw_recurrence : ∀ n, C (d n) * P (n + 2) = C (d n) * (A n * P (n + 1) + B n * P
n)`; `lag : B`, `certificate := globalNonpos`, and `den_nonzero : ∀ n, d n ≠ 0` is optional
(proved automatically when omitted). -/
syntax (name := rr_g_negative_lag_sequence_den_global_nonpos)
  "rr_g_negative_lag_sequence_den" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "lag" ":=" term ","
    ("den_nonzero" ":=" term ",")?
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term ","
    "certificate" ":=" "globalNonpos" :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for a Liu--Wang lag recurrence
`P (n + 2) = A n * P (n + 1) + B n * P n` with an arbitrary polynomial `A n` given with a
denominator by `raw_recurrence : ∀ n, C (d n) * P (n + 2) = C (d n) * (A n * P (n + 1) + B n * P
n)`; `lag : B`, `certificate := globalNonpos`, and `den_nonzero : ∀ n, d n ≠ 0` is optional
(proved automatically when omitted). -/
syntax (name := rr_g_negative_lag_sequence_den_realrooted_global_nonpos)
  "rr_g_negative_lag_sequence_den_realrooted" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "lag" ":=" term ","
    ("den_nonzero" ":=" term ",")?
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term ","
    "certificate" ":=" "globalNonpos" :
  tactic

/-- Closes `∀ n, StrictInterl (P n) (P (n + 1))` for a negative-square lag with a common
denominator: `square_factor : q`, `coeff : c`, `raw_coeff : b`, `den : d`, and `raw_recurrence :
∀ n, C (d n) * P (n + 2) = C (d n) * (A n * P (n + 1)) + C (b n) * (-(q n) ^ 2 * P n)`, with
`coeff_eq : (d n)⁻¹ * b n = c n` and `den_nonzero` optional (proved automatically when omitted),
and the standard certificates `base`, `pos_lc`, `degree_succ` and
`no_common_roots`. The certificate is `negativeSquare`. -/
syntax (name := rr_g_neg_lag_den_sq)
  "rr_g_negative_lag_sequence_den_coeff" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "square_factor" ":=" term ","
    "coeff" ":=" term ","
    "raw_coeff" ":=" term ","
    "den" ":=" term ","
    ("den_nonzero" ":=" term ",")?
    ("coeff_eq" ":=" term ",")?
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term ","
    "certificate" ":=" "negativeSquare" :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for a negative-square lag with a common denominator:
`square_factor : q`, `coeff : c`, `raw_coeff : b`, `den : d`, and `raw_recurrence : ∀ n, C (d n)
* P (n + 2) = C (d n) * (A n * P (n + 1)) + C (b n) * (-(q n) ^ 2 * P n)`, with
`coeff_eq : (d n)⁻¹ * b n = c n` and `den_nonzero` optional (proved automatically when omitted),
and the standard certificates `base`, `pos_lc`, `degree_succ` and
`no_common_roots`. The certificate is `negativeSquare`. -/
syntax (name := rr_g_neg_lag_den_sq_rr)
  "rr_g_negative_lag_sequence_den_coeff_realrooted" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "square_factor" ":=" term ","
    "coeff" ":=" term ","
    "raw_coeff" ":=" term ","
    "den" ":=" term ","
    ("den_nonzero" ":=" term ",")?
    ("coeff_eq" ":=" term ",")?
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term ","
    "certificate" ":=" "negativeSquare" :
  tactic

/-- Closes `∀ n, StrictInterl (P n) (P (n + 1))` for a negative-quadratic lag with a common
denominator, as in `rr_lw_negative_quadratic_sequence_den_coeff_auto_split`: `leading`,
`linear` and `constant` are the normalized coefficients, `raw_leading`, `raw_linear` and
`raw_constant` the raw ones, `den` the denominator, and `den_nonzero` and the coefficient
equations are optional (proved automatically when omitted). The certificate is
`negativeQuadratic`. -/
syntax (name := rr_g_neg_lag_den_quad)
  "rr_g_negative_lag_sequence_den_coeff" " using "
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
    ("leading_coeff_eq" ":=" term ","
    "linear_coeff_eq" ":=" term ","
    "constant_coeff_eq" ":=" term ",")?
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term ","
    "certificate" ":=" "negativeQuadratic" :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for a negative-quadratic lag with a common denominator,
as in `rr_lw_negative_quadratic_sequence_den_coeff_auto_split`: `leading`,
`linear` and `constant` are the normalized coefficients, `raw_leading`, `raw_linear` and
`raw_constant` the raw ones, `den` the denominator, and `den_nonzero` and the coefficient
equations are optional (proved automatically when omitted). The certificate is
`negativeQuadratic`. -/
syntax (name := rr_g_neg_lag_den_quad_rr)
  "rr_g_negative_lag_sequence_den_coeff_realrooted" " using "
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
    ("leading_coeff_eq" ":=" term ","
    "linear_coeff_eq" ":=" term ","
    "constant_coeff_eq" ":=" term ",")?
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term ","
    "certificate" ":=" "negativeQuadratic" :
  tactic
macro_rules
  | `(tactic|
      rr_g_negative_lag_sequence using
        base := $hbase:term,
        pos_lc := $hpos:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term,
        certificate := negativeSquare) =>
      `(tactic|
        rr_lw_negative_square_sequence_auto using
          base := $hbase,
          pos_lc := $hpos,
          recurrence := $hrec,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_g_negative_lag_sequence_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term,
        certificate := negativeSquare) =>
      `(tactic|
        rr_lw_negative_square_sequence_realrooted_auto using
          base := $hbase,
          pos_lc := $hpos,
          recurrence := $hrec,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_g_negative_lag_sequence using
        base := $hbase:term,
        pos_lc := $hpos:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term,
        certificate := negativeMonicQuadratic) =>
      `(tactic|
        rr_lw_negative_monic_quadratic_sequence_auto using
          base := $hbase,
          pos_lc := $hpos,
          recurrence := $hrec,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_g_negative_lag_sequence_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term,
        certificate := negativeMonicQuadratic) =>
      `(tactic|
        rr_lw_negative_monic_quadratic_sequence_realrooted_auto using
          base := $hbase,
          pos_lc := $hpos,
          recurrence := $hrec,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_g_negative_lag_sequence using
        base := $hbase:term,
        pos_lc := $hpos:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term,
        certificate := negativeQuadratic) =>
      `(tactic|
        rr_lw_negative_quadratic_sequence_auto using
          base := $hbase,
          pos_lc := $hpos,
          recurrence := $hrec,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_g_negative_lag_sequence_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term,
        certificate := negativeQuadratic) =>
      `(tactic|
        rr_lw_negative_quadratic_sequence_realrooted_auto using
          base := $hbase,
          pos_lc := $hpos,
          recurrence := $hrec,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_g_negative_lag_sequence using
        base := $hbase:term,
        pos_lc := $hpos:term,
        lag := $B:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term,
        certificate := globalNonpos) =>
      `(tactic|
        rr_lw_global_nonpos_sequence_auto using
          base := $hbase,
          pos_lc := $hpos,
          lag := $B,
          recurrence := $hrec,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_g_negative_lag_sequence_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        lag := $B:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term,
        certificate := globalNonpos) =>
      `(tactic|
        rr_lw_global_nonpos_sequence_realrooted_auto using
          base := $hbase,
          pos_lc := $hpos,
          lag := $B,
          recurrence := $hrec,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_g_negative_lag_sequence_den using
        base := $hbase:term,
        pos_lc := $hpos:term,
        lag := $B:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term,
        certificate := globalNonpos) =>
      `(tactic|
        rr_g_negative_lag_sequence_den using
          base := $hbase,
          pos_lc := $hpos,
          lag := $B,
          den_nonzero := rr_oeis_active_den_all_term,
          raw_recurrence := $hraw,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno,
          certificate := globalNonpos)
  | `(tactic|
      rr_g_negative_lag_sequence_den using
        base := $hbase:term,
        pos_lc := $hpos:term,
        lag := $B:term,
        den_nonzero := $hden:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term,
        certificate := globalNonpos) =>
      `(tactic|
        rr_lw_global_nonpos_sequence_den_auto using
          base := $hbase,
          pos_lc := $hpos,
          lag := $B,
          den_nonzero := $hden,
          raw_recurrence := $hraw,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_g_negative_lag_sequence_den_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        lag := $B:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term,
        certificate := globalNonpos) =>
      `(tactic|
        rr_g_negative_lag_sequence_den_realrooted using
          base := $hbase,
          pos_lc := $hpos,
          lag := $B,
          den_nonzero := rr_oeis_active_den_all_term,
          raw_recurrence := $hraw,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno,
          certificate := globalNonpos)
  | `(tactic|
      rr_g_negative_lag_sequence_den_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        lag := $B:term,
        den_nonzero := $hden:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term,
        certificate := globalNonpos) =>
      `(tactic|
        rr_lw_global_nonpos_sequence_den_realrooted_auto using
          base := $hbase,
          pos_lc := $hpos,
          lag := $B,
          den_nonzero := $hden,
          raw_recurrence := $hraw,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_g_negative_lag_sequence_den_coeff using
        base := $hbase:term,
        pos_lc := $hpos:term,
        square_factor := $q:term,
        coeff := $c:term,
        raw_coeff := $b:term,
        den := $d:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term,
        certificate := negativeSquare) =>
      `(tactic|
        rr_g_negative_lag_sequence_den_coeff using
          base := $hbase,
          pos_lc := $hpos,
          square_factor := $q,
          coeff := $c,
          raw_coeff := $b,
          den := $d,
          coeff_eq := rr_oeis_coeff_all_term,
          raw_recurrence := $hraw,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno,
          certificate := negativeSquare)
  | `(tactic|
      rr_g_negative_lag_sequence_den_coeff using
        base := $hbase:term,
        pos_lc := $hpos:term,
        square_factor := $q:term,
        coeff := $c:term,
        raw_coeff := $b:term,
        den := $d:term,
        coeff_eq := $hcoeff:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term,
        certificate := negativeSquare) =>
      `(tactic|
        rr_g_negative_lag_sequence_den_coeff using
          base := $hbase,
          pos_lc := $hpos,
          square_factor := $q,
          coeff := $c,
          raw_coeff := $b,
          den := $d,
          den_nonzero := rr_oeis_active_den_all_term,
          coeff_eq := $hcoeff,
          raw_recurrence := $hraw,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno,
          certificate := negativeSquare)
  | `(tactic|
      rr_g_negative_lag_sequence_den_coeff using
        base := $hbase:term,
        pos_lc := $hpos:term,
        square_factor := $q:term,
        coeff := $c:term,
        raw_coeff := $b:term,
        den := $d:term,
        den_nonzero := $hden:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term,
        certificate := negativeSquare) =>
      `(tactic|
        rr_g_negative_lag_sequence_den_coeff using
          base := $hbase,
          pos_lc := $hpos,
          square_factor := $q,
          coeff := $c,
          raw_coeff := $b,
          den := $d,
          den_nonzero := $hden,
          coeff_eq := rr_oeis_coeff_all_term,
          raw_recurrence := $hraw,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno,
          certificate := negativeSquare)
  | `(tactic|
      rr_g_negative_lag_sequence_den_coeff using
        base := $hbase:term,
        pos_lc := $hpos:term,
        square_factor := $q:term,
        coeff := $c:term,
        raw_coeff := $b:term,
        den := $d:term,
        den_nonzero := $hden:term,
        coeff_eq := $hcoeff:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term,
        certificate := negativeSquare) =>
      `(tactic|
        rr_lw_negative_square_sequence_den_coeff_auto_split using
          base := $hbase,
          pos_lc := $hpos,
          square_factor := $q,
          coeff := $c,
          raw_coeff := $b,
          den := $d,
          den_nonzero := $hden,
          coeff_eq := $hcoeff,
          raw_recurrence := $hraw,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_g_negative_lag_sequence_den_coeff_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        square_factor := $q:term,
        coeff := $c:term,
        raw_coeff := $b:term,
        den := $d:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term,
        certificate := negativeSquare) =>
      `(tactic|
        rr_g_negative_lag_sequence_den_coeff_realrooted using
          base := $hbase,
          pos_lc := $hpos,
          square_factor := $q,
          coeff := $c,
          raw_coeff := $b,
          den := $d,
          coeff_eq := rr_oeis_coeff_all_term,
          raw_recurrence := $hraw,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno,
          certificate := negativeSquare)
  | `(tactic|
      rr_g_negative_lag_sequence_den_coeff_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        square_factor := $q:term,
        coeff := $c:term,
        raw_coeff := $b:term,
        den := $d:term,
        coeff_eq := $hcoeff:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term,
        certificate := negativeSquare) =>
      `(tactic|
        rr_g_negative_lag_sequence_den_coeff_realrooted using
          base := $hbase,
          pos_lc := $hpos,
          square_factor := $q,
          coeff := $c,
          raw_coeff := $b,
          den := $d,
          den_nonzero := rr_oeis_active_den_all_term,
          coeff_eq := $hcoeff,
          raw_recurrence := $hraw,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno,
          certificate := negativeSquare)
  | `(tactic|
      rr_g_negative_lag_sequence_den_coeff_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        square_factor := $q:term,
        coeff := $c:term,
        raw_coeff := $b:term,
        den := $d:term,
        den_nonzero := $hden:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term,
        certificate := negativeSquare) =>
      `(tactic|
        rr_g_negative_lag_sequence_den_coeff_realrooted using
          base := $hbase,
          pos_lc := $hpos,
          square_factor := $q,
          coeff := $c,
          raw_coeff := $b,
          den := $d,
          den_nonzero := $hden,
          coeff_eq := rr_oeis_coeff_all_term,
          raw_recurrence := $hraw,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno,
          certificate := negativeSquare)
  | `(tactic|
      rr_g_negative_lag_sequence_den_coeff_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        square_factor := $q:term,
        coeff := $c:term,
        raw_coeff := $b:term,
        den := $d:term,
        den_nonzero := $hden:term,
        coeff_eq := $hcoeff:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term,
        certificate := negativeSquare) =>
      `(tactic|
        rr_lw_negative_square_sequence_den_coeff_realrooted_auto_split using
          base := $hbase,
          pos_lc := $hpos,
          square_factor := $q,
          coeff := $c,
          raw_coeff := $b,
          den := $d,
          den_nonzero := $hden,
          coeff_eq := $hcoeff,
          raw_recurrence := $hraw,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_g_negative_lag_sequence_den_coeff using
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
        no_common_roots := $hno:term,
        certificate := negativeQuadratic) =>
      `(tactic|
        rr_g_negative_lag_sequence_den_coeff using
          base := $hbase,
          pos_lc := $hpos,
          leading := $a,
          linear := $b,
          constant := $c,
          raw_leading := $araw,
          raw_linear := $braw,
          raw_constant := $craw,
          den := $d,
          leading_coeff_eq := rr_oeis_coeff_all_term,
          linear_coeff_eq := rr_oeis_coeff_all_term,
          constant_coeff_eq := rr_oeis_coeff_all_term,
          raw_recurrence := $hraw,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno,
          certificate := negativeQuadratic)
  | `(tactic|
      rr_g_negative_lag_sequence_den_coeff using
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
        no_common_roots := $hno:term,
        certificate := negativeQuadratic) =>
      `(tactic|
        rr_g_negative_lag_sequence_den_coeff using
          base := $hbase,
          pos_lc := $hpos,
          leading := $a,
          linear := $b,
          constant := $c,
          raw_leading := $araw,
          raw_linear := $braw,
          raw_constant := $craw,
          den := $d,
          den_nonzero := rr_oeis_active_den_all_term,
          leading_coeff_eq := $ha_coeff,
          linear_coeff_eq := $hb_coeff,
          constant_coeff_eq := $hc_coeff,
          raw_recurrence := $hraw,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno,
          certificate := negativeQuadratic)
  | `(tactic|
      rr_g_negative_lag_sequence_den_coeff using
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
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term,
        certificate := negativeQuadratic) =>
      `(tactic|
        rr_g_negative_lag_sequence_den_coeff using
          base := $hbase,
          pos_lc := $hpos,
          leading := $a,
          linear := $b,
          constant := $c,
          raw_leading := $araw,
          raw_linear := $braw,
          raw_constant := $craw,
          den := $d,
          den_nonzero := $hden,
          leading_coeff_eq := rr_oeis_coeff_all_term,
          linear_coeff_eq := rr_oeis_coeff_all_term,
          constant_coeff_eq := rr_oeis_coeff_all_term,
          raw_recurrence := $hraw,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno,
          certificate := negativeQuadratic)
  | `(tactic|
      rr_g_negative_lag_sequence_den_coeff using
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
        no_common_roots := $hno:term,
        certificate := negativeQuadratic) =>
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
          den_nonzero := $hden,
          leading_coeff_eq := $ha_coeff,
          linear_coeff_eq := $hb_coeff,
          constant_coeff_eq := $hc_coeff,
          raw_recurrence := $hraw,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_g_negative_lag_sequence_den_coeff_realrooted using
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
        no_common_roots := $hno:term,
        certificate := negativeQuadratic) =>
      `(tactic|
        rr_g_negative_lag_sequence_den_coeff_realrooted using
          base := $hbase,
          pos_lc := $hpos,
          leading := $a,
          linear := $b,
          constant := $c,
          raw_leading := $araw,
          raw_linear := $braw,
          raw_constant := $craw,
          den := $d,
          leading_coeff_eq := rr_oeis_coeff_all_term,
          linear_coeff_eq := rr_oeis_coeff_all_term,
          constant_coeff_eq := rr_oeis_coeff_all_term,
          raw_recurrence := $hraw,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno,
          certificate := negativeQuadratic)
  | `(tactic|
      rr_g_negative_lag_sequence_den_coeff_realrooted using
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
        no_common_roots := $hno:term,
        certificate := negativeQuadratic) =>
      `(tactic|
        rr_g_negative_lag_sequence_den_coeff_realrooted using
          base := $hbase,
          pos_lc := $hpos,
          leading := $a,
          linear := $b,
          constant := $c,
          raw_leading := $araw,
          raw_linear := $braw,
          raw_constant := $craw,
          den := $d,
          den_nonzero := rr_oeis_active_den_all_term,
          leading_coeff_eq := $ha_coeff,
          linear_coeff_eq := $hb_coeff,
          constant_coeff_eq := $hc_coeff,
          raw_recurrence := $hraw,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno,
          certificate := negativeQuadratic)
  | `(tactic|
      rr_g_negative_lag_sequence_den_coeff_realrooted using
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
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term,
        certificate := negativeQuadratic) =>
      `(tactic|
        rr_g_negative_lag_sequence_den_coeff_realrooted using
          base := $hbase,
          pos_lc := $hpos,
          leading := $a,
          linear := $b,
          constant := $c,
          raw_leading := $araw,
          raw_linear := $braw,
          raw_constant := $craw,
          den := $d,
          den_nonzero := $hden,
          leading_coeff_eq := rr_oeis_coeff_all_term,
          linear_coeff_eq := rr_oeis_coeff_all_term,
          constant_coeff_eq := rr_oeis_coeff_all_term,
          raw_recurrence := $hraw,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno,
          certificate := negativeQuadratic)
  | `(tactic|
      rr_g_negative_lag_sequence_den_coeff_realrooted using
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
        no_common_roots := $hno:term,
        certificate := negativeQuadratic) =>
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
          den_nonzero := $hden,
          leading_coeff_eq := $ha_coeff,
          linear_coeff_eq := $hb_coeff,
          constant_coeff_eq := $hc_coeff,
          raw_recurrence := $hraw,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
end Tactic
end RealRooted
