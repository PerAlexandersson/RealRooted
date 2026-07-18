import RealRooted.Tactic.AllCombo
import RealRooted.Tactic.AffineDerivative
import RealRooted.Tactic.MaWang
import RealRooted.Tactic.CubicDiscriminant
import RealRooted.Tactic.CommonInterleaver
import RealRooted.Tactic.Derivative
import RealRooted.Tactic.EulerOperator
import RealRooted.Tactic.Favard
import RealRooted.Tactic.GammaRealRoots
import RealRooted.Tactic.IteratedDerivativeShift
import RealRooted.Tactic.FiniteSymbolPFFrontend
import RealRooted.Tactic.Linear
import RealRooted.Tactic.InterlacingSequence
import RealRooted.Tactic.LinearPowerFamily
import RealRooted.Tactic.LiuWang
import RealRooted.Tactic.LiuWangRecursion
import RealRooted.Tactic.Matrix
import RealRooted.Tactic.MagnitudeDominated
import RealRooted.Tactic.MultiplierSequence
import RealRooted.Tactic.OperatorPreservesInterlacing
import RealRooted.Tactic.PFPolynomial
import RealRooted.Tactic.PosCombo
import RealRooted.Tactic.RootCount
import RealRooted.Tactic.StaircaseSum
import RealRooted.Tactic.SymmetricDecomposition
import RealRooted.Tactic.VeroneseSection
import RealRooted.Tactic.WeightedSum
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
rr_i2_derivative_lag_sequence_den_coeff using ... certificate := directHalfLine
rr_i2_derivative_lag_sequence_den using ... certificate := wagnerGap
rr_e_positive_t_lag_sequence using ... certificate := currentX
rr_e_positive_t_lag_sequence using ... certificate := currentCX
rr_e_positive_t_lag_sequence using ... certificate := currentOneAddX
rr_e_positive_t_lag_sequence using ... certificate := plateauX
rr_e_positive_t_lag_sequence using ... certificate := xOneSubX
rr_e_positive_t_lag_sequence using ... certificate := xCSubCMulX
rr_e_positive_t_lag_sequence using ... certificate := cMulXCSubCMulX
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

syntax (name := rr_i2_derivative_lag_sequence_den_direct_halfline)
  "rr_i2_derivative_lag_sequence_den_coeff" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "deriv_factor" ":=" term ","
    "lag_factor" ":=" term ","
    "norm_deriv_coeff" ":=" term ","
    "norm_lag_coeff" ":=" term ","
    "den" ":=" term ","
    "raw_deriv_coeff" ":=" term ","
    "raw_lag_coeff" ":=" term ","
    "den_nonzero" ":=" term ","
    "deriv_coeff_eq" ":=" term ","
    "lag_coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term ","
    "certificate" ":=" "directHalfLine" :
  tactic

syntax (name := rr_i2_derivative_lag_sequence_den_realrooted_direct_halfline)
  "rr_i2_derivative_lag_sequence_den_coeff_realrooted" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "deriv_factor" ":=" term ","
    "lag_factor" ":=" term ","
    "norm_deriv_coeff" ":=" term ","
    "norm_lag_coeff" ":=" term ","
    "den" ":=" term ","
    "raw_deriv_coeff" ":=" term ","
    "raw_lag_coeff" ":=" term ","
    "den_nonzero" ":=" term ","
    "deriv_coeff_eq" ":=" term ","
    "lag_coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term ","
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

macro_rules
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
      rr_i2_derivative_lag_sequence_den_coeff using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
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
          degree_two := $hdeg_two,
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
        degree_two := $hdeg_two:term,
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
          degree_two := $hdeg_two,
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
        rr_prec_wagner_derivative_gap_lag_sequence_den using
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
        rr_prec_wagner_derivative_gap_lag_sequence_den_realrooted using
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
