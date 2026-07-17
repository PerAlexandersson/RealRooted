import RealRooted.Tactic.MaWang
import RealRooted.Tactic.Favard
import RealRooted.Tactic.LiuWang
import RealRooted.Tactic.LiuWangRecursion
import RealRooted.Tactic.Matrix
import RealRooted.Tactic.WagnerX

/-!
# OEIS tactic wrapper stub

Planned user-facing dispatch:

```lean
rr_oeis ma_wang
rr_oeis favard
rr_oeis liu_wang
rr_oeis matrix
rr_i2_derivative_lag_sequence using ... certificate := directHalfLine
rr_i2_derivative_lag_sequence using ... certificate := wagnerGap
```

This should remain a thin wrapper over explicit family tactics.  Generated
OEIS files should expose the recurrence and certificate lemmas, then call the
appropriate engine-specific tactic.
-/

open Lean.Elab.Tactic

namespace RealRooted
namespace Tactic

syntax (name := rr_i2_derivative_lag_sequence_direct_halfline)
  "rr_i2_derivative_lag_sequence" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term ","
    "certificate" ":=" "directHalfLine" :
  tactic

syntax (name := rr_i2_derivative_lag_sequence_realrooted_direct_halfline)
  "rr_i2_derivative_lag_sequence_realrooted" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term ","
    "certificate" ":=" "directHalfLine" :
  tactic

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

syntax (name := rr_i2_derivative_lag_sequence_jacobi)
  "rr_i2_derivative_lag_sequence" " using "
    "certificate" ":=" "jacobiOrHypergeom" :
  tactic

syntax (name := rr_i2_derivative_lag_sequence_realrooted_jacobi)
  "rr_i2_derivative_lag_sequence_realrooted" " using "
    "certificate" ":=" "jacobiOrHypergeom" :
  tactic

syntax (name := rr_i2_derivative_lag_sequence_transform)
  "rr_i2_derivative_lag_sequence" " using "
    "certificate" ":=" "transformNeeded" :
  tactic

syntax (name := rr_i2_derivative_lag_sequence_realrooted_transform)
  "rr_i2_derivative_lag_sequence_realrooted" " using "
    "certificate" ":=" "transformNeeded" :
  tactic

syntax (name := rr_i2_derivative_lag_sequence_vector)
  "rr_i2_derivative_lag_sequence" " using "
    "certificate" ":=" "vectorNeeded" :
  tactic

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
        degree_two := $hdeg_two:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term,
        certificate := directHalfLine) =>
      `(tactic|
        rr_lw_derivative_lag_sequence_sign_auto using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          degree_two := $hdeg_two,
          recurrence := $hrec,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_i2_derivative_lag_sequence_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term,
        certificate := directHalfLine) =>
      `(tactic|
        rr_lw_derivative_lag_sequence_realrooted_sign_auto using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          degree_two := $hdeg_two,
          recurrence := $hrec,
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
        rr_prec_wagner_derivative_gap_lag_sequence using
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
        rr_prec_wagner_derivative_gap_lag_sequence_realrooted using
          base := $hbase,
          nonneg_coeffs := $hnonneg,
          degree_two := $hdeg,
          lag_coeff_pos := $ha,
          derivative_coeff_pos := $hc,
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
