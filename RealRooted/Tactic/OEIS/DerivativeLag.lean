module

public import RealRooted.Tactic.LiuWangRecursion
public import RealRooted.Tactic.OEIS.Basic
public import RealRooted.Tactic.WagnerX
public meta import RealRooted.Tactic.LiuWangRecursion
public meta import RealRooted.Tactic.OEIS.Basic
public meta import RealRooted.Tactic.WagnerX

/-!
# OEIS derivative-lag certificate frontend

Parser declarations and dispatch rules for the degree-two derivative-lag
certificate family.  The wrapper deliberately rejects certificates requiring
classical root-location or vector/PF bridges rather than disguising them as
scalar recurrence proofs.
-/

public meta section

open Lean.Elab.Tactic

namespace RealRooted
namespace Tactic

/-- Closes `∀ n, StrictInterl (P n) (P (n + 1))` for a degree-two derivative-lag recurrence
`P (n + 2) = U n * P (n + 1) + V n * (P (n + 1))' + W n * P n` with
`certificate := directHalfLine`; the sign conditions are proved automatically from
`nonneg_coeffs`, and the arguments are `base`, `pos_lc`, `nonneg_coeffs`,
`recurrence`, `degree_succ` and `no_common_roots`. -/
syntax (name := rr_i2_derivative_lag_sequence_direct_halfline)
  "rr_i2_derivative_lag_sequence" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term ","
    "certificate" ":=" "directHalfLine" :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for a degree-two derivative-lag recurrence
`P (n + 2) = U n * P (n + 1) + V n * (P (n + 1))' + W n * P n` with
`certificate := directHalfLine`; the sign conditions are proved automatically from
`nonneg_coeffs`, and the arguments are `base`, `pos_lc`, `nonneg_coeffs`,
`recurrence`, `degree_succ` and `no_common_roots`. -/
syntax (name := rr_i2_derivative_lag_sequence_realrooted_direct_halfline)
  "rr_i2_derivative_lag_sequence_realrooted" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term ","
    "certificate" ":=" "directHalfLine" :
  tactic

/-- Closes `∀ n, StrictInterl (P n) (P (n + 1))` for a degree-two derivative-lag recurrence
`P (n + 2) = U n * P (n + 1) + V n * (P (n + 1))' + W n * P n` with
`certificate := directHalfLine`; the recurrence is given after clearing a denominator as
`raw_recurrence`, with scalar sequences `den`, `raw_deriv_coeff`, `raw_lag_coeff`,
`norm_deriv_coeff` and `norm_lag_coeff` and polynomial sequences
`deriv_factor` and `lag_factor`; the equations `deriv_coeff_eq`, `lag_coeff_eq` and
`den_nonzero` are optional (proved automatically when omitted). The other arguments are `base`,
`pos_lc`, `nonneg_coeffs`, `degree_succ` and `no_common_roots`. -/
syntax (name := rr_i2_derivative_lag_sequence_den_direct_halfline)
  "rr_i2_derivative_lag_sequence_den_coeff" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "deriv_factor" ":=" term ","
    "lag_factor" ":=" term ","
    "norm_deriv_coeff" ":=" term ","
    "norm_lag_coeff" ":=" term ","
    "den" ":=" term ","
    "raw_deriv_coeff" ":=" term ","
    "raw_lag_coeff" ":=" term ","
    ("den_nonzero" ":=" term ",")?
    ("deriv_coeff_eq" ":=" term ","
    "lag_coeff_eq" ":=" term ",")?
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term ","
    "certificate" ":=" "directHalfLine" :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for a degree-two derivative-lag recurrence
`P (n + 2) = U n * P (n + 1) + V n * (P (n + 1))' + W n * P n` with
`certificate := directHalfLine`; the recurrence is given after clearing a denominator as
`raw_recurrence`, with scalar sequences `den`, `raw_deriv_coeff`, `raw_lag_coeff`,
`norm_deriv_coeff` and `norm_lag_coeff` and polynomial sequences
`deriv_factor` and `lag_factor`; the equations `deriv_coeff_eq`, `lag_coeff_eq` and
`den_nonzero` are optional (proved automatically when omitted). The other arguments are `base`,
`pos_lc`, `nonneg_coeffs`, `degree_succ` and `no_common_roots`. -/
syntax (name := rr_i2_derivative_lag_sequence_den_realrooted_direct_halfline)
  "rr_i2_derivative_lag_sequence_den_coeff_realrooted" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "deriv_factor" ":=" term ","
    "lag_factor" ":=" term ","
    "norm_deriv_coeff" ":=" term ","
    "norm_lag_coeff" ":=" term ","
    "den" ":=" term ","
    "raw_deriv_coeff" ":=" term ","
    "raw_lag_coeff" ":=" term ","
    ("den_nonzero" ":=" term ",")?
    ("deriv_coeff_eq" ":=" term ","
    "lag_coeff_eq" ":=" term ",")?
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term ","
    "certificate" ":=" "directHalfLine" :
  tactic

/-- Closes `∀ n, StrictInterl (P n) (P (n + 1))` for
`P (n + 2) = X * (C (c n) * (P (n + 1))' + C (a n) * P n)` with `lag_coeff_pos : ∀ n, 0 < a n`
and `derivative_coeff_pos : ∀ n, 0 < c n` (`certificate := wagnerGap`, as
`rr_strict_interl_wagner_derivative_gap_lag_sequence`); the other arguments are `base`,
`nonneg_coeffs`, `degree_two` and `recurrence`. -/
syntax (name := rr_i2_derivative_lag_sequence_wagner_gap)
  "rr_i2_derivative_lag_sequence" " using "
    "base" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "lag_coeff_pos" ":=" term ","
    "derivative_coeff_pos" ":=" term ","
    "recurrence" ":=" term ","
    "certificate" ":=" "wagnerGap" :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for
`P (n + 2) = X * (C (c n) * (P (n + 1))' + C (a n) * P n)` with `lag_coeff_pos : ∀ n, 0 < a n`
and `derivative_coeff_pos : ∀ n, 0 < c n` (`certificate := wagnerGap`, as
`rr_strict_interl_wagner_derivative_gap_lag_sequence_realrooted`); the other arguments are
`base`, `nonneg_coeffs`, `degree_two` and `recurrence`. -/
syntax (name := rr_i2_derivative_lag_sequence_realrooted_wagner_gap)
  "rr_i2_derivative_lag_sequence_realrooted" " using "
    "base" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "lag_coeff_pos" ":=" term ","
    "derivative_coeff_pos" ":=" term ","
    "recurrence" ":=" term ","
    "certificate" ":=" "wagnerGap" :
  tactic

/-- Denominator form of the `wagnerGap` certificate of `rr_i2_derivative_lag_sequence`:
`denom_pos : ∀ n, 0 < d n` and `recurrence : C (d n) * P (n + 2) = X * (C (c n) * (P (n + 1))' +
C (a n) * P n)`; closes `∀ n, StrictInterl (P n) (P (n + 1))`. -/
syntax (name := rr_i2_derivative_lag_sequence_den_wagner_gap)
  "rr_i2_derivative_lag_sequence_den" " using "
    "base" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "lag_coeff_pos" ":=" term ","
    "derivative_coeff_pos" ":=" term ","
    "denom_pos" ":=" term ","
    "recurrence" ":=" term ","
    "certificate" ":=" "wagnerGap" :
  tactic

/-- Denominator form of the
`wagnerGap` certificate of `rr_i2_derivative_lag_sequence_realrooted`:
`denom_pos : ∀ n, 0 < d n` and `recurrence : C (d n) * P (n + 2) = X * (C (c n) * (P (n + 1))' +
C (a n) * P n)`; closes `∀ n, P n ≠ 0 ∧ (P n).Splits`. -/
syntax (name := rr_i2_derivative_lag_sequence_den_realrooted_wagner_gap)
  "rr_i2_derivative_lag_sequence_den_realrooted" " using "
    "base" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "lag_coeff_pos" ":=" term ","
    "derivative_coeff_pos" ":=" term ","
    "denom_pos" ":=" term ","
    "recurrence" ":=" term ","
    "certificate" ":=" "wagnerGap" :
  tactic

/-- Rejection form of
`rr_i2_derivative_lag_sequence`: always fails, since the `jacobiOrHypergeom` certificate needs a
classical coefficient-formula or root-location bridge. -/
syntax (name := rr_i2_derivative_lag_sequence_jacobi)
  "rr_i2_derivative_lag_sequence" " using "
    "certificate" ":=" "jacobiOrHypergeom" :
  tactic

/-- Rejection form of `rr_i2_derivative_lag_sequence_realrooted`: always fails, since the
`jacobiOrHypergeom` certificate needs a classical coefficient-formula or root-location bridge. -/
syntax (name := rr_i2_derivative_lag_sequence_realrooted_jacobi)
  "rr_i2_derivative_lag_sequence_realrooted" " using "
    "certificate" ":=" "jacobiOrHypergeom" :
  tactic

/-- Rejection form of `rr_i2_derivative_lag_sequence`: always fails, since the `transformNeeded`
certificate needs an explicit transformed recurrence and root-window certificate. -/
syntax (name := rr_i2_derivative_lag_sequence_transform)
  "rr_i2_derivative_lag_sequence" " using "
    "certificate" ":=" "transformNeeded" :
  tactic

/-- Rejection form of `rr_i2_derivative_lag_sequence_realrooted`: always fails, since the
`transformNeeded` certificate needs an explicit transformed recurrence and root-window
certificate. -/
syntax (name := rr_i2_derivative_lag_sequence_realrooted_transform)
  "rr_i2_derivative_lag_sequence_realrooted" " using "
    "certificate" ":=" "transformNeeded" :
  tactic

/-- Rejection form of `rr_i2_derivative_lag_sequence`: always fails, since the `vectorNeeded`
certificate means the scalar derivative-lag wrapper does not apply and a vector or PF
certificate is needed. -/
syntax (name := rr_i2_derivative_lag_sequence_vector)
  "rr_i2_derivative_lag_sequence" " using "
    "certificate" ":=" "vectorNeeded" :
  tactic

/-- Rejection form of `rr_i2_derivative_lag_sequence_realrooted`: always fails, since the
`vectorNeeded` certificate means the scalar derivative-lag wrapper does not apply and a vector
or PF certificate is needed. -/
syntax (name := rr_i2_derivative_lag_sequence_realrooted_vector)
  "rr_i2_derivative_lag_sequence_realrooted" " using "
    "certificate" ":=" "vectorNeeded" :
  tactic
macro_rules
  | `(tactic|
      rr_i2_derivative_lag_sequence using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term,
        certificate := directHalfLine) =>
      `(tactic|
        rr_lw_derivative_lag_sequence_sign_auto using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          recurrence := $hrec,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_i2_derivative_lag_sequence_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term,
        certificate := directHalfLine) =>
      `(tactic|
        rr_lw_derivative_lag_sequence_realrooted_sign_auto using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          recurrence := $hrec,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_i2_derivative_lag_sequence_den_coeff using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        deriv_factor := $V:term,
        lag_factor := $W:term,
        norm_deriv_coeff := $cV:term,
        norm_lag_coeff := $cW:term,
        den := $d:term,
        raw_deriv_coeff := $b:term,
        raw_lag_coeff := $e:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term,
        certificate := directHalfLine) =>
      `(tactic|
        rr_i2_derivative_lag_sequence_den_coeff using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          deriv_factor := $V,
          lag_factor := $W,
          norm_deriv_coeff := $cV,
          norm_lag_coeff := $cW,
          den := $d,
          raw_deriv_coeff := $b,
          raw_lag_coeff := $e,
          deriv_coeff_eq := rr_oeis_coeff_all_term,
          lag_coeff_eq := rr_oeis_coeff_all_term,
          raw_recurrence := $hraw,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno,
          certificate := directHalfLine)
  | `(tactic|
      rr_i2_derivative_lag_sequence_den_coeff using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
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
        no_common_roots := $hno:term,
        certificate := directHalfLine) =>
      `(tactic|
        rr_i2_derivative_lag_sequence_den_coeff using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          deriv_factor := $V,
          lag_factor := $W,
          norm_deriv_coeff := $cV,
          norm_lag_coeff := $cW,
          den := $d,
          raw_deriv_coeff := $b,
          raw_lag_coeff := $e,
          den_nonzero := rr_oeis_active_den_all_term,
          deriv_coeff_eq := $hcoeffV,
          lag_coeff_eq := $hcoeffW,
          raw_recurrence := $hraw,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno,
          certificate := directHalfLine)
  | `(tactic|
      rr_i2_derivative_lag_sequence_den_coeff using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        deriv_factor := $V:term,
        lag_factor := $W:term,
        norm_deriv_coeff := $cV:term,
        norm_lag_coeff := $cW:term,
        den := $d:term,
        raw_deriv_coeff := $b:term,
        raw_lag_coeff := $e:term,
        den_nonzero := $hden:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term,
        certificate := directHalfLine) =>
      `(tactic|
        rr_i2_derivative_lag_sequence_den_coeff using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          deriv_factor := $V,
          lag_factor := $W,
          norm_deriv_coeff := $cV,
          norm_lag_coeff := $cW,
          den := $d,
          raw_deriv_coeff := $b,
          raw_lag_coeff := $e,
          den_nonzero := $hden,
          deriv_coeff_eq := rr_oeis_coeff_all_term,
          lag_coeff_eq := rr_oeis_coeff_all_term,
          raw_recurrence := $hraw,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno,
          certificate := directHalfLine)
  | `(tactic|
      rr_i2_derivative_lag_sequence_den_coeff using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
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
        no_common_roots := $hno:term,
        certificate := directHalfLine) =>
      `(tactic|
        rr_lw_derivative_lag_sequence_den_coeff_sign_auto using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
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
      rr_i2_derivative_lag_sequence_den_coeff_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        deriv_factor := $V:term,
        lag_factor := $W:term,
        norm_deriv_coeff := $cV:term,
        norm_lag_coeff := $cW:term,
        den := $d:term,
        raw_deriv_coeff := $b:term,
        raw_lag_coeff := $e:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term,
        certificate := directHalfLine) =>
      `(tactic|
        rr_i2_derivative_lag_sequence_den_coeff_realrooted using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          deriv_factor := $V,
          lag_factor := $W,
          norm_deriv_coeff := $cV,
          norm_lag_coeff := $cW,
          den := $d,
          raw_deriv_coeff := $b,
          raw_lag_coeff := $e,
          deriv_coeff_eq := rr_oeis_coeff_all_term,
          lag_coeff_eq := rr_oeis_coeff_all_term,
          raw_recurrence := $hraw,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno,
          certificate := directHalfLine)
  | `(tactic|
      rr_i2_derivative_lag_sequence_den_coeff_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
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
        no_common_roots := $hno:term,
        certificate := directHalfLine) =>
      `(tactic|
        rr_i2_derivative_lag_sequence_den_coeff_realrooted using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          deriv_factor := $V,
          lag_factor := $W,
          norm_deriv_coeff := $cV,
          norm_lag_coeff := $cW,
          den := $d,
          raw_deriv_coeff := $b,
          raw_lag_coeff := $e,
          den_nonzero := rr_oeis_active_den_all_term,
          deriv_coeff_eq := $hcoeffV,
          lag_coeff_eq := $hcoeffW,
          raw_recurrence := $hraw,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno,
          certificate := directHalfLine)
  | `(tactic|
      rr_i2_derivative_lag_sequence_den_coeff_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        deriv_factor := $V:term,
        lag_factor := $W:term,
        norm_deriv_coeff := $cV:term,
        norm_lag_coeff := $cW:term,
        den := $d:term,
        raw_deriv_coeff := $b:term,
        raw_lag_coeff := $e:term,
        den_nonzero := $hden:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term,
        certificate := directHalfLine) =>
      `(tactic|
        rr_i2_derivative_lag_sequence_den_coeff_realrooted using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          deriv_factor := $V,
          lag_factor := $W,
          norm_deriv_coeff := $cV,
          norm_lag_coeff := $cW,
          den := $d,
          raw_deriv_coeff := $b,
          raw_lag_coeff := $e,
          den_nonzero := $hden,
          deriv_coeff_eq := rr_oeis_coeff_all_term,
          lag_coeff_eq := rr_oeis_coeff_all_term,
          raw_recurrence := $hraw,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno,
          certificate := directHalfLine)
  | `(tactic|
      rr_i2_derivative_lag_sequence_den_coeff_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
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
        no_common_roots := $hno:term,
        certificate := directHalfLine) =>
      `(tactic|
        rr_lw_derivative_lag_sequence_den_coeff_realrooted_sign_auto using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
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
      rr_i2_derivative_lag_sequence using
        base := $hbase:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg:term,
        lag_coeff_pos := $ha:term,
        derivative_coeff_pos := $hc:term,
        recurrence := $hrec:term,
        certificate := wagnerGap) =>
      `(tactic|
        rr_strict_interl_wagner_derivative_gap_lag_sequence using
          base := $hbase,
          nonneg_coeffs := $hnonneg,
          degree_two := $hdeg,
          lag_coeff_pos := $ha,
          derivative_coeff_pos := $hc,
          recurrence := $hrec)
  | `(tactic|
      rr_i2_derivative_lag_sequence_realrooted using
        base := $hbase:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg:term,
        lag_coeff_pos := $ha:term,
        derivative_coeff_pos := $hc:term,
        recurrence := $hrec:term,
        certificate := wagnerGap) =>
      `(tactic|
        rr_strict_interl_wagner_derivative_gap_lag_sequence_realrooted using
          base := $hbase,
          nonneg_coeffs := $hnonneg,
          degree_two := $hdeg,
          lag_coeff_pos := $ha,
          derivative_coeff_pos := $hc,
          recurrence := $hrec)
  | `(tactic|
      rr_i2_derivative_lag_sequence_den using
        base := $hbase:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg:term,
        lag_coeff_pos := $ha:term,
        derivative_coeff_pos := $hc:term,
        denom_pos := $hd:term,
        recurrence := $hrec:term,
        certificate := wagnerGap) =>
      `(tactic|
        rr_strict_interl_wagner_derivative_gap_lag_sequence_den using
          base := $hbase,
          nonneg_coeffs := $hnonneg,
          degree_two := $hdeg,
          lag_coeff_pos := $ha,
          derivative_coeff_pos := $hc,
          denom_pos := $hd,
          recurrence := $hrec)
  | `(tactic|
      rr_i2_derivative_lag_sequence_den_realrooted using
        base := $hbase:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg:term,
        lag_coeff_pos := $ha:term,
        derivative_coeff_pos := $hc:term,
        denom_pos := $hd:term,
        recurrence := $hrec:term,
        certificate := wagnerGap) =>
      `(tactic|
        rr_strict_interl_wagner_derivative_gap_lag_sequence_den_realrooted using
          base := $hbase,
          nonneg_coeffs := $hnonneg,
          degree_two := $hdeg,
          lag_coeff_pos := $ha,
          derivative_coeff_pos := $hc,
          denom_pos := $hd,
          recurrence := $hrec)

elab_rules : tactic
  | `(tactic| rr_i2_derivative_lag_sequence using certificate := jacobiOrHypergeom) =>
      throwError
        "rr_i2_derivative_lag_sequence: jacobiOrHypergeom requires a classical \
        coefficient-formula/root-location bridge"
  | `(tactic| rr_i2_derivative_lag_sequence_realrooted using
        certificate := jacobiOrHypergeom) =>
      throwError
        "rr_i2_derivative_lag_sequence_realrooted: jacobiOrHypergeom requires a \
        classical coefficient-formula/root-location bridge"
  | `(tactic| rr_i2_derivative_lag_sequence using certificate := transformNeeded) =>
      throwError
        "rr_i2_derivative_lag_sequence: transformNeeded requires an explicit \
        transformed recurrence and root-window certificate"
  | `(tactic| rr_i2_derivative_lag_sequence_realrooted using
        certificate := transformNeeded) =>
      throwError
        "rr_i2_derivative_lag_sequence_realrooted: transformNeeded requires an \
        explicit transformed recurrence and root-window certificate"
  | `(tactic| rr_i2_derivative_lag_sequence using certificate := vectorNeeded) =>
      throwError
        "rr_i2_derivative_lag_sequence: vectorNeeded means the scalar \
        derivative-lag wrapper is invalid; provide a vector/PF certificate"
  | `(tactic| rr_i2_derivative_lag_sequence_realrooted using
        certificate := vectorNeeded) =>
      throwError
        "rr_i2_derivative_lag_sequence_realrooted: vectorNeeded means the scalar \
        derivative-lag wrapper is invalid; provide a vector/PF certificate"
end Tactic
end RealRooted
