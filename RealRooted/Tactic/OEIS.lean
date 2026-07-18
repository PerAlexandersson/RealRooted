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
import RealRooted.Tactic.Product
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
rr_e_positive_t_lag_sequence using ... certificate := tR
rr_e_positive_t_lag_sequence using ... certificate := cTR
rr_e_positive_t_lag_sequence using ... certificate := cTRAuto
rr_g_negative_lag_sequence using ... certificate := negativeSquare
rr_g_negative_lag_sequence using ... certificate := negativeMonicQuadratic
rr_g_negative_lag_sequence using ... certificate := negativeQuadratic
rr_g_negative_lag_sequence using ... certificate := globalNonpos
rr_g_negative_lag_sequence_den_coeff using ... certificate := negativeSquare
rr_g_negative_lag_sequence_den_coeff using ... certificate := negativeQuadratic
rr_product_exit_sequence using ... certificate := identity
rr_product_exit_sequence using ... certificate := rootZero
rr_product_exit_sequence using ... certificate := periodTwo
rr_product_factor_sequence using ... certificate := suppliedFactor
rr_product_factor_sequence using ... certificate := affine
rr_product_factor_sequence using ... certificate := affineAuto
rr_product_factor_sequence using ... certificate := constFirstAffine
rr_product_factor_sequence using ... certificate := constFirstAffineAuto
rr_product_factor_sequence using ... certificate := xAddC
rr_product_factor_sequence using ... certificate := cAddX
rr_product_factor_sequence using ... certificate := rootZeroPow
rr_product_factor_sequence using ... certificate := xAddCPow
rr_product_factor_sequence using ... certificate := cAddXPow
rr_product_factor_sequence using ... certificate := scalar
rr_product_factor_sequence using ... certificate := scalarAuto
rr_product_lift_sequence using ... certificate := suppliedFactor
rr_product_lift_sequence using ... certificate := rootZero
rr_product_lift_sequence using ... certificate := rootZeroPow
rr_product_lift_sequence using ... certificate := xAddC
rr_product_lift_sequence using ... certificate := rowXAddCPow
rr_product_lift_sequence using ... certificate := scalar
rr_product_lift_sequence using ... certificate := scalarAuto
rr_product_lift_sequence using ... certificate := affine
rr_product_lift_sequence using ... certificate := affineAuto
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

syntax (name := rr_g_negative_lag_sequence_den_global_nonpos)
  "rr_g_negative_lag_sequence_den" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "lag" ":=" term ","
    "den_nonzero" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term ","
    "certificate" ":=" "globalNonpos" :
  tactic

syntax (name := rr_g_negative_lag_sequence_den_realrooted_global_nonpos)
  "rr_g_negative_lag_sequence_den_realrooted" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "lag" ":=" term ","
    "den_nonzero" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term ","
    "certificate" ":=" "globalNonpos" :
  tactic

syntax (name := rr_g_neg_lag_den_sq)
  "rr_g_negative_lag_sequence_den_coeff" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "square_factor" ":=" term ","
    "coeff" ":=" term ","
    "raw_coeff" ":=" term ","
    "den" ":=" term ","
    "den_nonzero" ":=" term ","
    "coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term ","
    "certificate" ":=" "negativeSquare" :
  tactic

syntax (name := rr_g_neg_lag_den_sq_rr)
  "rr_g_negative_lag_sequence_den_coeff_realrooted" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "square_factor" ":=" term ","
    "coeff" ":=" term ","
    "raw_coeff" ":=" term ","
    "den" ":=" term ","
    "den_nonzero" ":=" term ","
    "coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term ","
    "certificate" ":=" "negativeSquare" :
  tactic

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
    "den_nonzero" ":=" term ","
    "leading_coeff_eq" ":=" term ","
    "linear_coeff_eq" ":=" term ","
    "constant_coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term ","
    "certificate" ":=" "negativeQuadratic" :
  tactic

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
    "den_nonzero" ":=" term ","
    "leading_coeff_eq" ":=" term ","
    "linear_coeff_eq" ":=" term ","
    "constant_coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term ","
    "certificate" ":=" "negativeQuadratic" :
  tactic

syntax (name := rr_product_exit_sequence_identity)
  "rr_product_exit_sequence" " using "
    "base" ":=" term ","
    "recurrence" ":=" term ","
    "certificate" ":=" "identity" :
  tactic

syntax (name := rr_product_exit_sequence_root_zero)
  "rr_product_exit_sequence" " using "
    "base" ":=" term ","
    "recurrence" ":=" term ","
    "certificate" ":=" "rootZero" :
  tactic

syntax (name := rr_product_exit_sequence_period_two)
  "rr_product_exit_sequence" " using "
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "recurrence" ":=" term ","
    "certificate" ":=" "periodTwo" :
  tactic

syntax (name := rr_product_factor_sequence_supplied_factor)
  "rr_product_factor_sequence" " using "
    "base" ":=" term ","
    "factor_realrooted" ":=" term ","
    "recurrence" ":=" term ","
    "certificate" ":=" "suppliedFactor" :
  tactic

syntax (name := rr_product_factor_sequence_affine)
  "rr_product_factor_sequence" " using "
    "base" ":=" term ","
    "slope_ne" ":=" term ","
    "recurrence" ":=" term ","
    "certificate" ":=" "affine" :
  tactic

syntax (name := rr_product_factor_sequence_affine_auto)
  "rr_product_factor_sequence" " using "
    "base" ":=" term ","
    "recurrence" ":=" term ","
    "certificate" ":=" "affineAuto" :
  tactic

syntax (name := rr_product_factor_sequence_const_first_affine)
  "rr_product_factor_sequence" " using "
    "base" ":=" term ","
    "slope_ne" ":=" term ","
    "recurrence" ":=" term ","
    "certificate" ":=" "constFirstAffine" :
  tactic

syntax (name := rr_product_factor_sequence_const_first_affine_auto)
  "rr_product_factor_sequence" " using "
    "base" ":=" term ","
    "recurrence" ":=" term ","
    "certificate" ":=" "constFirstAffineAuto" :
  tactic

syntax (name := rr_product_factor_sequence_x_add_c)
  "rr_product_factor_sequence" " using "
    "base" ":=" term ","
    "recurrence" ":=" term ","
    "certificate" ":=" "xAddC" :
  tactic

syntax (name := rr_product_factor_sequence_c_add_x)
  "rr_product_factor_sequence" " using "
    "base" ":=" term ","
    "recurrence" ":=" term ","
    "certificate" ":=" "cAddX" :
  tactic

syntax (name := rr_product_factor_sequence_root_zero_pow)
  "rr_product_factor_sequence" " using "
    "base" ":=" term ","
    "recurrence" ":=" term ","
    "certificate" ":=" "rootZeroPow" :
  tactic

syntax (name := rr_product_factor_sequence_x_add_c_pow)
  "rr_product_factor_sequence" " using "
    "base" ":=" term ","
    "recurrence" ":=" term ","
    "certificate" ":=" "xAddCPow" :
  tactic

syntax (name := rr_product_factor_sequence_c_add_x_pow)
  "rr_product_factor_sequence" " using "
    "base" ":=" term ","
    "recurrence" ":=" term ","
    "certificate" ":=" "cAddXPow" :
  tactic

syntax (name := rr_product_factor_sequence_scalar)
  "rr_product_factor_sequence" " using "
    "base" ":=" term ","
    "scalar_ne" ":=" term ","
    "recurrence" ":=" term ","
    "certificate" ":=" "scalar" :
  tactic

syntax (name := rr_product_factor_sequence_scalar_auto)
  "rr_product_factor_sequence" " using "
    "base" ":=" term ","
    "recurrence" ":=" term ","
    "certificate" ":=" "scalarAuto" :
  tactic

syntax (name := rr_product_lift_sequence_supplied_factor)
  "rr_product_lift_sequence" " using "
    "quotient_realrooted" ":=" term ","
    "factor_realrooted" ":=" term ","
    "factorization" ":=" term ","
    "certificate" ":=" "suppliedFactor" :
  tactic

syntax (name := rr_product_lift_sequence_root_zero)
  "rr_product_lift_sequence" " using "
    "quotient_realrooted" ":=" term ","
    "factorization" ":=" term ","
    "certificate" ":=" "rootZero" :
  tactic

syntax (name := rr_product_lift_sequence_root_zero_pow)
  "rr_product_lift_sequence" " using "
    "quotient_realrooted" ":=" term ","
    "factorization" ":=" term ","
    "certificate" ":=" "rootZeroPow" :
  tactic

syntax (name := rr_product_lift_sequence_x_add_c)
  "rr_product_lift_sequence" " using "
    "quotient_realrooted" ":=" term ","
    "factorization" ":=" term ","
    "certificate" ":=" "xAddC" :
  tactic

syntax (name := rr_product_lift_sequence_row_x_add_c_pow)
  "rr_product_lift_sequence" " using "
    "quotient_realrooted" ":=" term ","
    "factorization" ":=" term ","
    "certificate" ":=" "rowXAddCPow" :
  tactic

syntax (name := rr_product_lift_sequence_scalar)
  "rr_product_lift_sequence" " using "
    "quotient_realrooted" ":=" term ","
    "scalar_ne" ":=" term ","
    "factorization" ":=" term ","
    "certificate" ":=" "scalar" :
  tactic

syntax (name := rr_product_lift_sequence_scalar_auto)
  "rr_product_lift_sequence" " using "
    "quotient_realrooted" ":=" term ","
    "factorization" ":=" term ","
    "certificate" ":=" "scalarAuto" :
  tactic

syntax (name := rr_product_lift_sequence_affine)
  "rr_product_lift_sequence" " using "
    "quotient_realrooted" ":=" term ","
    "slope_ne" ":=" term ","
    "factorization" ":=" term ","
    "certificate" ":=" "affine" :
  tactic

syntax (name := rr_product_lift_sequence_affine_auto)
  "rr_product_lift_sequence" " using "
    "quotient_realrooted" ":=" term ","
    "factorization" ":=" term ","
    "certificate" ":=" "affineAuto" :
  tactic

macro_rules
  | `(tactic|
      rr_product_factor_sequence using
        base := $hbase:term,
        factor_realrooted := $hfactor:term,
        recurrence := $hrec:term,
        certificate := suppliedFactor) =>
      `(tactic|
        rr_product_factor_sequence using
          base := $hbase,
          factor_realrooted := $hfactor,
          recurrence := $hrec)
  | `(tactic|
      rr_product_factor_sequence using
        base := $hbase:term,
        slope_ne := $hs:term,
        recurrence := $hrec:term,
        certificate := affine) =>
      `(tactic|
        rr_product_affine_sequence using
          base := $hbase,
          slope_ne := $hs,
          recurrence := $hrec)
  | `(tactic|
      rr_product_factor_sequence using
        base := $hbase:term,
        recurrence := $hrec:term,
        certificate := affineAuto) =>
      `(tactic|
        rr_product_affine_sequence_auto using
          base := $hbase,
          recurrence := $hrec)
  | `(tactic|
      rr_product_factor_sequence using
        base := $hbase:term,
        slope_ne := $hs:term,
        recurrence := $hrec:term,
        certificate := constFirstAffine) =>
      `(tactic|
        rr_product_const_first_sequence using
          base := $hbase,
          slope_ne := $hs,
          recurrence := $hrec)
  | `(tactic|
      rr_product_factor_sequence using
        base := $hbase:term,
        recurrence := $hrec:term,
        certificate := constFirstAffineAuto) =>
      `(tactic|
        rr_product_const_first_sequence_auto using
          base := $hbase,
          recurrence := $hrec)
  | `(tactic|
      rr_product_factor_sequence using
        base := $hbase:term,
        recurrence := $hrec:term,
        certificate := xAddC) =>
      `(tactic|
        rr_product_X_sequence using
          base := $hbase,
          recurrence := $hrec)
  | `(tactic|
      rr_product_factor_sequence using
        base := $hbase:term,
        recurrence := $hrec:term,
        certificate := cAddX) =>
      `(tactic|
        rr_product_C_add_X_sequence using
          base := $hbase,
          recurrence := $hrec)
  | `(tactic|
      rr_product_factor_sequence using
        base := $hbase:term,
        recurrence := $hrec:term,
        certificate := rootZeroPow) =>
      `(tactic|
        rr_product_X_pow_sequence using
          base := $hbase,
          recurrence := $hrec)
  | `(tactic|
      rr_product_factor_sequence using
        base := $hbase:term,
        recurrence := $hrec:term,
        certificate := xAddCPow) =>
      `(tactic|
        rr_product_X_add_C_pow_sequence using
          base := $hbase,
          recurrence := $hrec)
  | `(tactic|
      rr_product_factor_sequence using
        base := $hbase:term,
        recurrence := $hrec:term,
        certificate := cAddXPow) =>
      `(tactic|
        rr_product_C_add_X_pow_sequence using
          base := $hbase,
          recurrence := $hrec)
  | `(tactic|
      rr_product_factor_sequence using
        base := $hbase:term,
        scalar_ne := $hs:term,
        recurrence := $hrec:term,
        certificate := scalar) =>
      `(tactic|
        rr_product_scalar_sequence using
          base := $hbase,
          scalar_ne := $hs,
          recurrence := $hrec)
  | `(tactic|
      rr_product_factor_sequence using
        base := $hbase:term,
        recurrence := $hrec:term,
        certificate := scalarAuto) =>
      `(tactic|
        rr_product_scalar_sequence_auto using
          base := $hbase,
          recurrence := $hrec)
  | `(tactic|
      rr_product_lift_sequence using
        quotient_realrooted := $hquot:term,
        factor_realrooted := $hfactor:term,
        factorization := $hrow:term,
        certificate := suppliedFactor) =>
      `(tactic|
        rr_product_lift_sequence using
          quotient_realrooted := $hquot,
          factor_realrooted := $hfactor,
          factorization := $hrow)
  | `(tactic|
      rr_product_lift_sequence using
        quotient_realrooted := $hquot:term,
        factorization := $hrow:term,
        certificate := rootZero) =>
      `(tactic|
        rr_product_lift_X_sequence using
          quotient_realrooted := $hquot,
          factorization := $hrow)
  | `(tactic|
      rr_product_lift_sequence using
        quotient_realrooted := $hquot:term,
        factorization := $hrow:term,
        certificate := rootZeroPow) =>
      `(tactic|
        rr_product_lift_X_pow_sequence using
          quotient_realrooted := $hquot,
          factorization := $hrow)
  | `(tactic|
      rr_product_lift_sequence using
        quotient_realrooted := $hquot:term,
        factorization := $hrow:term,
        certificate := xAddC) =>
      `(tactic|
        rr_product_lift_X_add_C_sequence using
          quotient_realrooted := $hquot,
          factorization := $hrow)
  | `(tactic|
      rr_product_lift_sequence using
        quotient_realrooted := $hquot:term,
        factorization := $hrow:term,
        certificate := rowXAddCPow) =>
      `(tactic|
        rr_product_lift_X_add_C_row_pow_sequence using
          quotient_realrooted := $hquot,
          factorization := $hrow)
  | `(tactic|
      rr_product_lift_sequence using
        quotient_realrooted := $hquot:term,
        scalar_ne := $hscalar:term,
        factorization := $hrow:term,
        certificate := scalar) =>
      `(tactic|
        rr_product_lift_C_sequence using
          quotient_realrooted := $hquot,
          scalar_ne := $hscalar,
          factorization := $hrow)
  | `(tactic|
      rr_product_lift_sequence using
        quotient_realrooted := $hquot:term,
        factorization := $hrow:term,
        certificate := scalarAuto) =>
      `(tactic|
        rr_product_lift_C_sequence_auto using
          quotient_realrooted := $hquot,
          factorization := $hrow)
  | `(tactic|
      rr_product_lift_sequence using
        quotient_realrooted := $hquot:term,
        slope_ne := $hslope:term,
        factorization := $hrow:term,
        certificate := affine) =>
      `(tactic|
        rr_product_lift_affine_sequence using
          quotient_realrooted := $hquot,
          slope_ne := $hslope,
          factorization := $hrow)
  | `(tactic|
      rr_product_lift_sequence using
        quotient_realrooted := $hquot:term,
        factorization := $hrow:term,
        certificate := affineAuto) =>
      `(tactic|
        rr_product_lift_affine_sequence_auto using
          quotient_realrooted := $hquot,
          factorization := $hrow)
  | `(tactic|
      rr_product_exit_sequence using
        base := $hbase:term,
        recurrence := $hrec:term,
        certificate := identity) =>
      `(tactic|
        rr_product_identity_sequence using
          base := $hbase,
          recurrence := $hrec)
  | `(tactic|
      rr_product_exit_sequence using
        base := $hbase:term,
        recurrence := $hrec:term,
        certificate := rootZero) =>
      `(tactic|
        rr_product_root_zero_sequence using
          base := $hbase,
          recurrence := $hrec)
  | `(tactic|
      rr_product_exit_sequence using
        base_zero := $hbase_zero:term,
        base_one := $hbase_one:term,
        recurrence := $hrec:term,
        certificate := periodTwo) =>
      `(tactic|
        rr_product_period_two_sequence using
          base_zero := $hbase_zero,
          base_one := $hbase_one,
          recurrence := $hrec)
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
