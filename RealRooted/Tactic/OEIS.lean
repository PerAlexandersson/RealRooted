import RealRooted.Tactic.AllCombo
import RealRooted.Tactic.AffineDerivative
import RealRooted.Tactic.MaWang
import RealRooted.Tactic.CubicDiscriminant
import RealRooted.Tactic.CommonInterleaver
import RealRooted.Tactic.Derivative
import RealRooted.Tactic.EulerOperator
import RealRooted.Tactic.Favard
import RealRooted.Tactic.GammaRealRoots
import RealRooted.Tactic.Hadamard
import RealRooted.Tactic.HermiteBiehler
import RealRooted.Tactic.HermitePoulain
import RealRooted.Tactic.IteratedDerivativeShift
import RealRooted.Tactic.FiniteSymbolPFFrontend
import RealRooted.Tactic.J1Chebyshev
import RealRooted.Tactic.J1Gap3Reciprocal
import RealRooted.Tactic.Kurtz
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
import RealRooted.Tactic.PFBidiagonal
import RealRooted.Tactic.PFBidiagonalFrontend
import RealRooted.Tactic.Product
import RealRooted.Tactic.PosCombo
import RealRooted.Tactic.Narayana
import RealRooted.Tactic.RootCount
import RealRooted.Tactic.SecondDerivative
import RealRooted.Tactic.StaircaseSum
import RealRooted.Tactic.SymmetricDecomposition
import RealRooted.Tactic.VeroneseSection
import RealRooted.Tactic.WeightedSum
import RealRooted.Tactic.Wagner
import RealRooted.Tactic.WagnerX

/-!
# OEIS tactic wrapper stub

Planned user-facing dispatch:

```lean
rr_oeis ma_wang
rr_oeis favard
rr_oeis liu_wang
rr_oeis matrix
rr_wagner_common_left_add_sequence using ...
rr_wagner_common_right_add_sequence using ...
rr_wagner_mulX_iff_sequence using ...
rr_hadamard_pf using ...
rr_hadamard_sequence_pf using ...
rr_hadamard_sequence_prec0 using ...
rr_schur_szego_sequence using ...
rr_hermite_biehler_odd_even_hurwitz using ...
rr_hermite_biehler_odd_even_hurwitz_stable_sequence using ...
rr_hermite_poulain using ...
rr_hermite_poulain_sequence using ...
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
rr_h_second_derivative_sequence using route := pf_bidiagonal, ...
rr_j1_factorable_sequence_realrooted using ... certificate := finiteLinearProduct
rr_j1_gap3_reciprocal_sequence_realrooted using ... certificate := modelRealRooted
rr_j1_gap3_reciprocal_sequence_realrooted using ... certificate := modelPF
rr_kurtz using ...
rr_kurtz_sequence using ...
rr_mw_plus_derivative_sequence using ...
rr_mw_plus_derivative_sequence_expanded_auto using ...
rr_narayana_polynomial_splits using ...
rr_narayana_polynomial_sequence_splits using ...
rr_product_exit_sequence using ... certificate := identity
rr_product_exit_sequence using ... certificate := rootZero
rr_product_exit_sequence using ... certificate := auto
rr_product_exit_sequence using ... certificate := periodTwo
rr_product_factor_sequence using ... certificate := suppliedFactor
rr_product_factor_sequence using ... certificate := auto
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
rr_product_factor_sequence using ... certificate := scalarPow
rr_product_factor_sequence using ... certificate := scalarPowAuto
rr_product_factor_sequence using ... certificate := affinePow
rr_product_factor_sequence using ... certificate := affinePowAuto
rr_product_factor_sequence using ... certificate := constFirstAffinePow
rr_product_factor_sequence using ... certificate := constFirstAffinePowAuto
rr_product_formula_sequence using ... certificate := finiteLinearProduct
rr_product_formula_sequence using ... certificate := scalarFiniteLinearProduct
rr_product_parity_sequence using ... certificate := scalarThenFactor
rr_product_parity_sequence using ... certificate := scalarThenFactorAuto
rr_product_parity_sequence using ... certificate := scalarThenXAddC
rr_product_parity_sequence using ... certificate := scalarThenXAddCAuto
rr_product_parity_sequence using ... certificate := scalarThenCAddX
rr_product_parity_sequence using ... certificate := scalarThenCAddXAuto
rr_product_parity_sequence using ... certificate := scalarThenRootZeroPow
rr_product_parity_sequence using ... certificate := scalarThenRootZeroPowAuto
rr_product_parity_sequence using ... certificate := scalarThenXAddCPow
rr_product_parity_sequence using ... certificate := scalarThenXAddCPowAuto
rr_product_parity_sequence using ... certificate := scalarThenCAddXPow
rr_product_parity_sequence using ... certificate := scalarThenCAddXPowAuto
rr_product_parity_lift_sequence using ... certificate := scalarXOdd
rr_endpoint_pair_sequence using ... certificate := sumThenX
rr_endpoint_pair_sequence_realrooted using ... certificate := sumThenX
rr_endpoint_pair_sequence using ... certificate := xThenSum
rr_endpoint_pair_sequence_realrooted using ... certificate := xThenSum
rr_endpoint_pair_lift_sequence using ... certificate := sumThenX
rr_endpoint_pair_lift_sequence using ... certificate := xThenSum
rr_endpoint_pair_lift_sequence using ... certificate := xThenSumSwapped
rr_product_lift_sequence using ... certificate := suppliedFactor
rr_product_lift_sequence using ... certificate := auto
rr_product_lift_sequence using ... certificate := rootZero
rr_product_lift_sequence using ... certificate := rootZeroPow
rr_product_lift_sequence using ... certificate := xAddC
rr_product_lift_sequence using ... certificate := cAddX
rr_product_lift_sequence using ... certificate := fixedXAddCPow
rr_product_lift_sequence using ... certificate := rowXAddCPow
rr_product_lift_sequence using ... certificate := cAddXPow
rr_product_lift_sequence using ... certificate := scalar
rr_product_lift_sequence using ... certificate := scalarAuto
rr_product_lift_sequence using ... certificate := scalarPow
rr_product_lift_sequence using ... certificate := scalarPowAuto
rr_product_lift_sequence using ... certificate := affine
rr_product_lift_sequence using ... certificate := affineAuto
rr_product_lift_sequence using ... certificate := constFirstAffine
rr_product_lift_sequence using ... certificate := constFirstAffineAuto
rr_product_lift_sequence using ... certificate := affinePow
rr_product_lift_sequence using ... certificate := affinePowAuto
rr_product_lift_sequence using ... certificate := constFirstAffinePow
rr_product_lift_sequence using ... certificate := constFirstAffinePowAuto
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
    ("den_nonzero" ":=" term ",")?
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
    ("den_nonzero" ":=" term ",")?
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
    ("den_nonzero" ":=" term ",")?
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
    ("den_nonzero" ":=" term ",")?
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
    ("den_nonzero" ":=" term ",")?
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
    ("den_nonzero" ":=" term ",")?
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
    ("den_nonzero" ":=" term ",")?
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
    ("den_nonzero" ":=" term ",")?
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
    ("cutoff" ":=" term ",")?
    "recurrence" ":=" term ","
    "certificate" ":=" "identity" :
  tactic

syntax (name := rr_product_exit_sequence_root_zero)
  "rr_product_exit_sequence" " using "
    "base" ":=" term ","
    ("cutoff" ":=" term ",")?
    "recurrence" ":=" term ","
    "certificate" ":=" "rootZero" :
  tactic

syntax (name := rr_product_exit_sequence_auto)
  "rr_product_exit_sequence" " using "
    "base" ":=" term ","
    ("cutoff" ":=" term ",")?
    "recurrence" ":=" term ","
    "certificate" ":=" "auto" :
  tactic

syntax (name := rr_product_exit_sequence_period_two)
  "rr_product_exit_sequence" " using "
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "recurrence" ":=" term ","
    "certificate" ":=" "periodTwo" :
  tactic

syntax (name := rr_product_exit_sequence_period_two_cutoff)
  "rr_product_exit_sequence" " using "
    "base" ":=" term ","
    "cutoff" ":=" term ","
    "recurrence" ":=" term ","
    "certificate" ":=" "periodTwo" :
  tactic

syntax (name := rr_product_factor_sequence_supplied_factor)
  "rr_product_factor_sequence" " using "
    "base" ":=" term ","
    "factor_realrooted" ":=" term ","
    ("cutoff" ":=" term ",")?
    "recurrence" ":=" term ","
    "certificate" ":=" "suppliedFactor" :
  tactic

syntax (name := rr_product_factor_sequence_auto)
  "rr_product_factor_sequence" " using "
    "base" ":=" term ","
    ("cutoff" ":=" term ",")?
    "recurrence" ":=" term ","
    "certificate" ":=" "auto" :
  tactic

syntax (name := rr_product_factor_sequence_affine)
  "rr_product_factor_sequence" " using "
    "base" ":=" term ","
    "slope_ne" ":=" term ","
    ("cutoff" ":=" term ",")?
    "recurrence" ":=" term ","
    "certificate" ":=" "affine" :
  tactic

syntax (name := rr_product_factor_sequence_affine_auto)
  "rr_product_factor_sequence" " using "
    "base" ":=" term ","
    ("cutoff" ":=" term ",")?
    "recurrence" ":=" term ","
    "certificate" ":=" "affineAuto" :
  tactic

syntax (name := rr_product_factor_sequence_const_first_affine)
  "rr_product_factor_sequence" " using "
    "base" ":=" term ","
    "slope_ne" ":=" term ","
    ("cutoff" ":=" term ",")?
    "recurrence" ":=" term ","
    "certificate" ":=" "constFirstAffine" :
  tactic

syntax (name := rr_product_factor_sequence_const_first_affine_auto)
  "rr_product_factor_sequence" " using "
    "base" ":=" term ","
    ("cutoff" ":=" term ",")?
    "recurrence" ":=" term ","
    "certificate" ":=" "constFirstAffineAuto" :
  tactic

syntax (name := rr_product_factor_sequence_x_add_c)
  "rr_product_factor_sequence" " using "
    "base" ":=" term ","
    ("cutoff" ":=" term ",")?
    "recurrence" ":=" term ","
    "certificate" ":=" "xAddC" :
  tactic

syntax (name := rr_product_factor_sequence_c_add_x)
  "rr_product_factor_sequence" " using "
    "base" ":=" term ","
    ("cutoff" ":=" term ",")?
    "recurrence" ":=" term ","
    "certificate" ":=" "cAddX" :
  tactic

syntax (name := rr_product_factor_sequence_root_zero_pow)
  "rr_product_factor_sequence" " using "
    "base" ":=" term ","
    ("cutoff" ":=" term ",")?
    "recurrence" ":=" term ","
    "certificate" ":=" "rootZeroPow" :
  tactic

syntax (name := rr_product_factor_sequence_x_add_c_pow)
  "rr_product_factor_sequence" " using "
    "base" ":=" term ","
    ("cutoff" ":=" term ",")?
    "recurrence" ":=" term ","
    "certificate" ":=" "xAddCPow" :
  tactic

syntax (name := rr_product_factor_sequence_c_add_x_pow)
  "rr_product_factor_sequence" " using "
    "base" ":=" term ","
    ("cutoff" ":=" term ",")?
    "recurrence" ":=" term ","
    "certificate" ":=" "cAddXPow" :
  tactic

syntax (name := rr_product_factor_sequence_scalar)
  "rr_product_factor_sequence" " using "
    "base" ":=" term ","
    "scalar_ne" ":=" term ","
    ("cutoff" ":=" term ",")?
    "recurrence" ":=" term ","
    "certificate" ":=" "scalar" :
  tactic

syntax (name := rr_product_factor_sequence_scalar_auto)
  "rr_product_factor_sequence" " using "
    "base" ":=" term ","
    ("cutoff" ":=" term ",")?
    "recurrence" ":=" term ","
    "certificate" ":=" "scalarAuto" :
  tactic

syntax (name := rr_product_factor_sequence_scalar_pow)
  "rr_product_factor_sequence" " using "
    "base" ":=" term ","
    "scalar_ne" ":=" term ","
    ("cutoff" ":=" term ",")?
    "recurrence" ":=" term ","
    "certificate" ":=" "scalarPow" :
  tactic

syntax (name := rr_product_factor_sequence_scalar_pow_auto)
  "rr_product_factor_sequence" " using "
    "base" ":=" term ","
    ("cutoff" ":=" term ",")?
    "recurrence" ":=" term ","
    "certificate" ":=" "scalarPowAuto" :
  tactic

syntax (name := rr_product_factor_sequence_affine_pow)
  "rr_product_factor_sequence" " using "
    "base" ":=" term ","
    "slope_ne" ":=" term ","
    ("cutoff" ":=" term ",")?
    "recurrence" ":=" term ","
    "certificate" ":=" "affinePow" :
  tactic

syntax (name := rr_product_factor_sequence_affine_pow_auto)
  "rr_product_factor_sequence" " using "
    "base" ":=" term ","
    ("cutoff" ":=" term ",")?
    "recurrence" ":=" term ","
    "certificate" ":=" "affinePowAuto" :
  tactic

syntax (name := rr_product_factor_sequence_const_first_affine_pow)
  "rr_product_factor_sequence" " using "
    "base" ":=" term ","
    "slope_ne" ":=" term ","
    ("cutoff" ":=" term ",")?
    "recurrence" ":=" term ","
    "certificate" ":=" "constFirstAffinePow" :
  tactic

syntax (name := rr_product_factor_sequence_const_first_affine_pow_auto)
  "rr_product_factor_sequence" " using "
    "base" ":=" term ","
    ("cutoff" ":=" term ",")?
    "recurrence" ":=" term ","
    "certificate" ":=" "constFirstAffinePowAuto" :
  tactic

syntax (name := rr_product_formula_sequence_finite_linear_product)
  "rr_product_formula_sequence" " using "
    "formula" ":=" term ","
    "certificate" ":=" "finiteLinearProduct" :
  tactic

syntax (name := rr_product_formula_sequence_scalar_finite_linear_product)
  "rr_product_formula_sequence" " using "
    "scalar_ne_zero" ":=" term ","
    "root_grid" ":=" term ","
    "certificate" ":=" "scalarFiniteLinearProduct" :
  tactic

syntax (name := rr_j1_factorable_sequence_realrooted_finite_linear_product)
  "rr_j1_factorable_sequence_realrooted" " using "
    "scalar_ne_zero" ":=" term ","
    "root_grid" ":=" term ","
    "certificate" ":=" "finiteLinearProduct" :
  tactic

syntax (name := rr_j1_gap3_reciprocal_sequence_realrooted_model_realrooted)
  "rr_j1_gap3_reciprocal_sequence_realrooted" " using "
    "model_realrooted" ":=" term ","
    "degree" ":=" term ","
    "reciprocal" ":=" term ","
    "certificate" ":=" "modelRealRooted" :
  tactic

syntax (name := rr_j1_gap3_reciprocal_sequence_realrooted_model_pf)
  "rr_j1_gap3_reciprocal_sequence_realrooted" " using "
    "model_pf" ":=" term ","
    "model_ne" ":=" term ","
    "degree" ":=" term ","
    "reciprocal" ":=" term ","
    "certificate" ":=" "modelPF" :
  tactic

syntax (name := rr_product_parity_sequence_scalar_then_factor)
  "rr_product_parity_sequence" " using "
    "base" ":=" term ","
    "scalar_ne" ":=" term ","
    "factor_realrooted" ":=" term ","
    ("cutoff" ":=" term ",")?
    "scalar_step" ":=" term ","
    "factor_step" ":=" term ","
    "certificate" ":=" "scalarThenFactor" :
  tactic

syntax (name := rr_product_parity_sequence_scalar_then_factor_auto)
  "rr_product_parity_sequence" " using "
    "base" ":=" term ","
    "factor_realrooted" ":=" term ","
    ("cutoff" ":=" term ",")?
    "scalar_step" ":=" term ","
    "factor_step" ":=" term ","
    "certificate" ":=" "scalarThenFactorAuto" :
  tactic

syntax (name := rr_product_parity_sequence_scalar_then_x_add_c)
  "rr_product_parity_sequence" " using "
    "base" ":=" term ","
    "scalar_ne" ":=" term ","
    ("cutoff" ":=" term ",")?
    "scalar_step" ":=" term ","
    "linear_step" ":=" term ","
    "certificate" ":=" "scalarThenXAddC" :
  tactic

syntax (name := rr_product_parity_sequence_scalar_then_x_add_c_auto)
  "rr_product_parity_sequence" " using "
    "base" ":=" term ","
    ("cutoff" ":=" term ",")?
    "scalar_step" ":=" term ","
    "linear_step" ":=" term ","
    "certificate" ":=" "scalarThenXAddCAuto" :
  tactic

syntax (name := rr_product_parity_sequence_scalar_then_c_add_x)
  "rr_product_parity_sequence" " using "
    "base" ":=" term ","
    "scalar_ne" ":=" term ","
    ("cutoff" ":=" term ",")?
    "scalar_step" ":=" term ","
    "linear_step" ":=" term ","
    "certificate" ":=" "scalarThenCAddX" :
  tactic

syntax (name := rr_product_parity_sequence_scalar_then_c_add_x_auto)
  "rr_product_parity_sequence" " using "
    "base" ":=" term ","
    ("cutoff" ":=" term ",")?
    "scalar_step" ":=" term ","
    "linear_step" ":=" term ","
    "certificate" ":=" "scalarThenCAddXAuto" :
  tactic

syntax (name := rr_product_parity_sequence_scalar_then_root_zero_pow)
  "rr_product_parity_sequence" " using "
    "base" ":=" term ","
    "scalar_ne" ":=" term ","
    ("cutoff" ":=" term ",")?
    "scalar_step" ":=" term ","
    "factor_step" ":=" term ","
    "certificate" ":=" "scalarThenRootZeroPow" :
  tactic

syntax (name := rr_product_parity_sequence_scalar_then_root_zero_pow_auto)
  "rr_product_parity_sequence" " using "
    "base" ":=" term ","
    ("cutoff" ":=" term ",")?
    "scalar_step" ":=" term ","
    "factor_step" ":=" term ","
    "certificate" ":=" "scalarThenRootZeroPowAuto" :
  tactic

syntax (name := rr_product_parity_sequence_scalar_then_x_add_c_pow)
  "rr_product_parity_sequence" " using "
    "base" ":=" term ","
    "scalar_ne" ":=" term ","
    ("cutoff" ":=" term ",")?
    "scalar_step" ":=" term ","
    "factor_step" ":=" term ","
    "certificate" ":=" "scalarThenXAddCPow" :
  tactic

syntax (name := rr_product_parity_sequence_scalar_then_x_add_c_pow_auto)
  "rr_product_parity_sequence" " using "
    "base" ":=" term ","
    ("cutoff" ":=" term ",")?
    "scalar_step" ":=" term ","
    "factor_step" ":=" term ","
    "certificate" ":=" "scalarThenXAddCPowAuto" :
  tactic

syntax (name := rr_product_parity_sequence_scalar_then_c_add_x_pow)
  "rr_product_parity_sequence" " using "
    "base" ":=" term ","
    "scalar_ne" ":=" term ","
    ("cutoff" ":=" term ",")?
    "scalar_step" ":=" term ","
    "factor_step" ":=" term ","
    "certificate" ":=" "scalarThenCAddXPow" :
  tactic

syntax (name := rr_product_parity_sequence_scalar_then_c_add_x_pow_auto)
  "rr_product_parity_sequence" " using "
    "base" ":=" term ","
    ("cutoff" ":=" term ",")?
    "scalar_step" ":=" term ","
    "factor_step" ":=" term ","
    "certificate" ":=" "scalarThenCAddXPowAuto" :
  tactic

syntax (name := rr_product_parity_lift_sequence_scalar_x_odd)
  "rr_product_parity_lift_sequence" " using "
    "even_realrooted" ":=" term ","
    "scalar_ne" ":=" term ","
    "even_factorization" ":=" term ","
    "odd_factorization" ":=" term ","
    "certificate" ":=" "scalarXOdd" :
  tactic

syntax (name := rr_endpoint_pair_sequence_sum_then_x)
  "rr_endpoint_pair_sequence" " using "
    "base" ":=" term ","
    "left_nonneg" ":=" term ","
    "right_nonneg" ":=" term ","
    "sum_step" ":=" term ","
    "x_step" ":=" term ","
    "coprime" ":=" term ","
    "certificate" ":=" "sumThenX" :
  tactic

syntax (name := rr_endpoint_pair_sequence_realrooted_sum_then_x)
  "rr_endpoint_pair_sequence_realrooted" " using "
    "base" ":=" term ","
    "left_nonneg" ":=" term ","
    "right_nonneg" ":=" term ","
    "sum_step" ":=" term ","
    "x_step" ":=" term ","
    "coprime" ":=" term ","
    "certificate" ":=" "sumThenX" :
  tactic

syntax (name := rr_endpoint_pair_sequence_x_then_sum)
  "rr_endpoint_pair_sequence" " using "
    "base" ":=" term ","
    "left_nonneg" ":=" term ","
    "right_nonneg" ":=" term ","
    "x_step" ":=" term ","
    "sum_step" ":=" term ","
    "coprime" ":=" term ","
    "certificate" ":=" "xThenSum" :
  tactic

syntax (name := rr_endpoint_pair_sequence_realrooted_x_then_sum)
  "rr_endpoint_pair_sequence_realrooted" " using "
    "base" ":=" term ","
    "left_nonneg" ":=" term ","
    "right_nonneg" ":=" term ","
    "x_step" ":=" term ","
    "sum_step" ":=" term ","
    "coprime" ":=" term ","
    "certificate" ":=" "xThenSum" :
  tactic

syntax (name := rr_endpoint_pair_lift_sequence_sum_then_x)
  "rr_endpoint_pair_lift_sequence" " using "
    "base" ":=" term ","
    "left_nonneg" ":=" term ","
    "right_nonneg" ":=" term ","
    "sum_step" ":=" term ","
    "x_step" ":=" term ","
    "coprime" ":=" term ","
    "even_factorization" ":=" term ","
    "odd_factorization" ":=" term ","
    "certificate" ":=" "sumThenX" :
  tactic

syntax (name := rr_endpoint_pair_lift_sequence_x_then_sum)
  "rr_endpoint_pair_lift_sequence" " using "
    "base" ":=" term ","
    "left_nonneg" ":=" term ","
    "right_nonneg" ":=" term ","
    "x_step" ":=" term ","
    "sum_step" ":=" term ","
    "coprime" ":=" term ","
    "even_factorization" ":=" term ","
    "odd_factorization" ":=" term ","
    "certificate" ":=" "xThenSum" :
  tactic

syntax (name := rr_endpoint_pair_lift_sequence_x_then_sum_swapped)
  "rr_endpoint_pair_lift_sequence" " using "
    "base" ":=" term ","
    "left_nonneg" ":=" term ","
    "right_nonneg" ":=" term ","
    "x_step" ":=" term ","
    "sum_step" ":=" term ","
    "coprime" ":=" term ","
    "even_factorization" ":=" term ","
    "odd_factorization" ":=" term ","
    "certificate" ":=" "xThenSumSwapped" :
  tactic

syntax (name := rr_product_lift_sequence_supplied_factor)
  "rr_product_lift_sequence" " using "
    "quotient_realrooted" ":=" term ","
    "factor_realrooted" ":=" term ","
    "factorization" ":=" term ","
    "certificate" ":=" "suppliedFactor" :
  tactic

syntax (name := rr_product_lift_sequence_supplied_factor_cutoff)
  "rr_product_lift_sequence" " using "
    "base" ":=" term ","
    "quotient_realrooted" ":=" term ","
    "factor_realrooted" ":=" term ","
    "cutoff" ":=" term ","
    "factorization" ":=" term ","
    "certificate" ":=" "suppliedFactor" :
  tactic

syntax (name := rr_product_lift_sequence_auto)
  "rr_product_lift_sequence" " using "
    "quotient_realrooted" ":=" term ","
    "factorization" ":=" term ","
    "certificate" ":=" "auto" :
  tactic

syntax (name := rr_product_lift_sequence_auto_cutoff)
  "rr_product_lift_sequence" " using "
    "base" ":=" term ","
    "quotient_realrooted" ":=" term ","
    "cutoff" ":=" term ","
    "factorization" ":=" term ","
    "certificate" ":=" "auto" :
  tactic

syntax (name := rr_product_lift_sequence_root_zero)
  "rr_product_lift_sequence" " using "
    "quotient_realrooted" ":=" term ","
    "factorization" ":=" term ","
    "certificate" ":=" "rootZero" :
  tactic

syntax (name := rr_product_lift_sequence_root_zero_cutoff)
  "rr_product_lift_sequence" " using "
    "base" ":=" term ","
    "quotient_realrooted" ":=" term ","
    "cutoff" ":=" term ","
    "factorization" ":=" term ","
    "certificate" ":=" "rootZero" :
  tactic

syntax (name := rr_product_lift_sequence_root_zero_pow)
  "rr_product_lift_sequence" " using "
    "quotient_realrooted" ":=" term ","
    "factorization" ":=" term ","
    "certificate" ":=" "rootZeroPow" :
  tactic

syntax (name := rr_product_lift_sequence_root_zero_pow_cutoff)
  "rr_product_lift_sequence" " using "
    "base" ":=" term ","
    "quotient_realrooted" ":=" term ","
    "cutoff" ":=" term ","
    "factorization" ":=" term ","
    "certificate" ":=" "rootZeroPow" :
  tactic

syntax (name := rr_product_lift_sequence_x_add_c)
  "rr_product_lift_sequence" " using "
    "quotient_realrooted" ":=" term ","
    "factorization" ":=" term ","
    "certificate" ":=" "xAddC" :
  tactic

syntax (name := rr_product_lift_sequence_x_add_c_cutoff)
  "rr_product_lift_sequence" " using "
    "base" ":=" term ","
    "quotient_realrooted" ":=" term ","
    "cutoff" ":=" term ","
    "factorization" ":=" term ","
    "certificate" ":=" "xAddC" :
  tactic

syntax (name := rr_product_lift_sequence_c_add_x)
  "rr_product_lift_sequence" " using "
    "quotient_realrooted" ":=" term ","
    "factorization" ":=" term ","
    "certificate" ":=" "cAddX" :
  tactic

syntax (name := rr_product_lift_sequence_c_add_x_cutoff)
  "rr_product_lift_sequence" " using "
    "base" ":=" term ","
    "quotient_realrooted" ":=" term ","
    "cutoff" ":=" term ","
    "factorization" ":=" term ","
    "certificate" ":=" "cAddX" :
  tactic

syntax (name := rr_product_lift_sequence_fixed_x_add_c_pow)
  "rr_product_lift_sequence" " using "
    "quotient_realrooted" ":=" term ","
    "factorization" ":=" term ","
    "certificate" ":=" "fixedXAddCPow" :
  tactic

syntax (name := rr_product_lift_sequence_fixed_x_add_c_pow_cutoff)
  "rr_product_lift_sequence" " using "
    "base" ":=" term ","
    "quotient_realrooted" ":=" term ","
    "cutoff" ":=" term ","
    "factorization" ":=" term ","
    "certificate" ":=" "fixedXAddCPow" :
  tactic

syntax (name := rr_product_lift_sequence_row_x_add_c_pow)
  "rr_product_lift_sequence" " using "
    "quotient_realrooted" ":=" term ","
    "factorization" ":=" term ","
    "certificate" ":=" "rowXAddCPow" :
  tactic

syntax (name := rr_product_lift_sequence_row_x_add_c_pow_cutoff)
  "rr_product_lift_sequence" " using "
    "base" ":=" term ","
    "quotient_realrooted" ":=" term ","
    "cutoff" ":=" term ","
    "factorization" ":=" term ","
    "certificate" ":=" "rowXAddCPow" :
  tactic

syntax (name := rr_product_lift_sequence_c_add_x_pow)
  "rr_product_lift_sequence" " using "
    "quotient_realrooted" ":=" term ","
    "factorization" ":=" term ","
    "certificate" ":=" "cAddXPow" :
  tactic

syntax (name := rr_product_lift_sequence_c_add_x_pow_cutoff)
  "rr_product_lift_sequence" " using "
    "base" ":=" term ","
    "quotient_realrooted" ":=" term ","
    "cutoff" ":=" term ","
    "factorization" ":=" term ","
    "certificate" ":=" "cAddXPow" :
  tactic

syntax (name := rr_product_lift_sequence_scalar)
  "rr_product_lift_sequence" " using "
    "quotient_realrooted" ":=" term ","
    "scalar_ne" ":=" term ","
    "factorization" ":=" term ","
    "certificate" ":=" "scalar" :
  tactic

syntax (name := rr_product_lift_sequence_scalar_cutoff)
  "rr_product_lift_sequence" " using "
    "base" ":=" term ","
    "quotient_realrooted" ":=" term ","
    "scalar_ne" ":=" term ","
    "cutoff" ":=" term ","
    "factorization" ":=" term ","
    "certificate" ":=" "scalar" :
  tactic

syntax (name := rr_product_lift_sequence_scalar_auto)
  "rr_product_lift_sequence" " using "
    "quotient_realrooted" ":=" term ","
    "factorization" ":=" term ","
    "certificate" ":=" "scalarAuto" :
  tactic

syntax (name := rr_product_lift_sequence_scalar_auto_cutoff)
  "rr_product_lift_sequence" " using "
    "base" ":=" term ","
    "quotient_realrooted" ":=" term ","
    "cutoff" ":=" term ","
    "factorization" ":=" term ","
    "certificate" ":=" "scalarAuto" :
  tactic

syntax (name := rr_product_lift_sequence_scalar_pow)
  "rr_product_lift_sequence" " using "
    "quotient_realrooted" ":=" term ","
    "scalar_ne" ":=" term ","
    "factorization" ":=" term ","
    "certificate" ":=" "scalarPow" :
  tactic

syntax (name := rr_product_lift_sequence_scalar_pow_cutoff)
  "rr_product_lift_sequence" " using "
    "base" ":=" term ","
    "quotient_realrooted" ":=" term ","
    "scalar_ne" ":=" term ","
    "cutoff" ":=" term ","
    "factorization" ":=" term ","
    "certificate" ":=" "scalarPow" :
  tactic

syntax (name := rr_product_lift_sequence_scalar_pow_auto)
  "rr_product_lift_sequence" " using "
    "quotient_realrooted" ":=" term ","
    "factorization" ":=" term ","
    "certificate" ":=" "scalarPowAuto" :
  tactic

syntax (name := rr_product_lift_sequence_scalar_pow_auto_cutoff)
  "rr_product_lift_sequence" " using "
    "base" ":=" term ","
    "quotient_realrooted" ":=" term ","
    "cutoff" ":=" term ","
    "factorization" ":=" term ","
    "certificate" ":=" "scalarPowAuto" :
  tactic

syntax (name := rr_product_lift_sequence_affine)
  "rr_product_lift_sequence" " using "
    "quotient_realrooted" ":=" term ","
    "slope_ne" ":=" term ","
    "factorization" ":=" term ","
    "certificate" ":=" "affine" :
  tactic

syntax (name := rr_product_lift_sequence_affine_cutoff)
  "rr_product_lift_sequence" " using "
    "base" ":=" term ","
    "quotient_realrooted" ":=" term ","
    "slope_ne" ":=" term ","
    "cutoff" ":=" term ","
    "factorization" ":=" term ","
    "certificate" ":=" "affine" :
  tactic

syntax (name := rr_product_lift_sequence_affine_auto)
  "rr_product_lift_sequence" " using "
    "quotient_realrooted" ":=" term ","
    "factorization" ":=" term ","
    "certificate" ":=" "affineAuto" :
  tactic

syntax (name := rr_product_lift_sequence_affine_auto_cutoff)
  "rr_product_lift_sequence" " using "
    "base" ":=" term ","
    "quotient_realrooted" ":=" term ","
    "cutoff" ":=" term ","
    "factorization" ":=" term ","
    "certificate" ":=" "affineAuto" :
  tactic

syntax (name := rr_product_lift_sequence_const_first_affine)
  "rr_product_lift_sequence" " using "
    "quotient_realrooted" ":=" term ","
    "slope_ne" ":=" term ","
    "factorization" ":=" term ","
    "certificate" ":=" "constFirstAffine" :
  tactic

syntax (name := rr_product_lift_sequence_const_first_affine_cutoff)
  "rr_product_lift_sequence" " using "
    "base" ":=" term ","
    "quotient_realrooted" ":=" term ","
    "slope_ne" ":=" term ","
    "cutoff" ":=" term ","
    "factorization" ":=" term ","
    "certificate" ":=" "constFirstAffine" :
  tactic

syntax (name := rr_product_lift_sequence_const_first_affine_auto)
  "rr_product_lift_sequence" " using "
    "quotient_realrooted" ":=" term ","
    "factorization" ":=" term ","
    "certificate" ":=" "constFirstAffineAuto" :
  tactic

syntax (name := rr_product_lift_sequence_const_first_affine_auto_cutoff)
  "rr_product_lift_sequence" " using "
    "base" ":=" term ","
    "quotient_realrooted" ":=" term ","
    "cutoff" ":=" term ","
    "factorization" ":=" term ","
    "certificate" ":=" "constFirstAffineAuto" :
  tactic

syntax (name := rr_product_lift_sequence_affine_pow)
  "rr_product_lift_sequence" " using "
    "quotient_realrooted" ":=" term ","
    "slope_ne" ":=" term ","
    "factorization" ":=" term ","
    "certificate" ":=" "affinePow" :
  tactic

syntax (name := rr_product_lift_sequence_affine_pow_cutoff)
  "rr_product_lift_sequence" " using "
    "base" ":=" term ","
    "quotient_realrooted" ":=" term ","
    "slope_ne" ":=" term ","
    "cutoff" ":=" term ","
    "factorization" ":=" term ","
    "certificate" ":=" "affinePow" :
  tactic

syntax (name := rr_product_lift_sequence_affine_pow_auto)
  "rr_product_lift_sequence" " using "
    "quotient_realrooted" ":=" term ","
    "factorization" ":=" term ","
    "certificate" ":=" "affinePowAuto" :
  tactic

syntax (name := rr_product_lift_sequence_affine_pow_auto_cutoff)
  "rr_product_lift_sequence" " using "
    "base" ":=" term ","
    "quotient_realrooted" ":=" term ","
    "cutoff" ":=" term ","
    "factorization" ":=" term ","
    "certificate" ":=" "affinePowAuto" :
  tactic

syntax (name := rr_product_lift_sequence_const_first_affine_pow)
  "rr_product_lift_sequence" " using "
    "quotient_realrooted" ":=" term ","
    "slope_ne" ":=" term ","
    "factorization" ":=" term ","
    "certificate" ":=" "constFirstAffinePow" :
  tactic

syntax (name := rr_product_lift_sequence_const_first_affine_pow_cutoff)
  "rr_product_lift_sequence" " using "
    "base" ":=" term ","
    "quotient_realrooted" ":=" term ","
    "slope_ne" ":=" term ","
    "cutoff" ":=" term ","
    "factorization" ":=" term ","
    "certificate" ":=" "constFirstAffinePow" :
  tactic

syntax (name := rr_product_lift_sequence_const_first_affine_pow_auto)
  "rr_product_lift_sequence" " using "
    "quotient_realrooted" ":=" term ","
    "factorization" ":=" term ","
    "certificate" ":=" "constFirstAffinePowAuto" :
  tactic

syntax (name := rr_product_lift_sequence_const_first_affine_pow_auto_cutoff)
  "rr_product_lift_sequence" " using "
    "base" ":=" term ","
    "quotient_realrooted" ":=" term ","
    "cutoff" ":=" term ","
    "factorization" ":=" term ","
    "certificate" ":=" "constFirstAffinePowAuto" :
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
        factor_realrooted := $hfactor:term,
        cutoff := $N:term,
        recurrence := $hrec:term,
        certificate := suppliedFactor) =>
      `(tactic|
        rr_product_factor_sequence using
          base := $hbase,
          factor_realrooted := $hfactor,
          cutoff := $N,
          recurrence := $hrec)
  | `(tactic|
      rr_product_factor_sequence using
        base := $hbase:term,
        recurrence := $hrec:term,
        certificate := auto) =>
      `(tactic|
        first
          | rr_product_checked_scalar_sequence_auto using
              base := $hbase,
              recurrence := $hrec
          | rr_product_checked_affine_sequence_auto using
              base := $hbase,
              recurrence := $hrec
          | rr_product_checked_affine_pow_sequence_auto using
              base := $hbase,
              recurrence := $hrec
          | rr_product_X_sequence using
              base := $hbase,
              recurrence := $hrec
          | rr_product_C_add_X_sequence using
              base := $hbase,
              recurrence := $hrec
          | rr_product_X_pow_sequence using
              base := $hbase,
              recurrence := $hrec
          | rr_product_X_add_C_pow_sequence using
              base := $hbase,
              recurrence := $hrec
          | rr_product_C_add_X_pow_sequence using
              base := $hbase,
              recurrence := $hrec)
  | `(tactic|
      rr_product_factor_sequence using
        base := $hbase:term,
        cutoff := $N:term,
        recurrence := $hrec:term,
        certificate := auto) =>
      `(tactic|
        first
          | rr_product_checked_scalar_sequence_auto using
              base := $hbase,
              cutoff := $N,
              recurrence := $hrec
          | rr_product_checked_affine_sequence_auto using
              base := $hbase,
              cutoff := $N,
              recurrence := $hrec
          | rr_product_checked_affine_pow_sequence_auto using
              base := $hbase,
              cutoff := $N,
              recurrence := $hrec
          | rr_product_X_sequence using
              base := $hbase,
              cutoff := $N,
              recurrence := $hrec
          | rr_product_C_add_X_sequence using
              base := $hbase,
              cutoff := $N,
              recurrence := $hrec
          | rr_product_X_pow_sequence using
              base := $hbase,
              cutoff := $N,
              recurrence := $hrec
          | rr_product_X_add_C_pow_sequence using
              base := $hbase,
              cutoff := $N,
              recurrence := $hrec
          | rr_product_C_add_X_pow_sequence using
              base := $hbase,
              cutoff := $N,
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
        slope_ne := $hs:term,
        cutoff := $N:term,
        recurrence := $hrec:term,
        certificate := affine) =>
      `(tactic|
        rr_product_affine_sequence using
          base := $hbase,
          slope_ne := $hs,
          cutoff := $N,
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
        cutoff := $N:term,
        recurrence := $hrec:term,
        certificate := affineAuto) =>
      `(tactic|
        rr_product_affine_sequence_auto using
          base := $hbase,
          cutoff := $N,
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
        slope_ne := $hs:term,
        cutoff := $N:term,
        recurrence := $hrec:term,
        certificate := constFirstAffine) =>
      `(tactic|
        rr_product_const_first_sequence using
          base := $hbase,
          slope_ne := $hs,
          cutoff := $N,
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
        cutoff := $N:term,
        recurrence := $hrec:term,
        certificate := constFirstAffineAuto) =>
      `(tactic|
        rr_product_const_first_sequence_auto using
          base := $hbase,
          cutoff := $N,
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
        cutoff := $N:term,
        recurrence := $hrec:term,
        certificate := xAddC) =>
      `(tactic|
        rr_product_X_sequence using
          base := $hbase,
          cutoff := $N,
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
        cutoff := $N:term,
        recurrence := $hrec:term,
        certificate := cAddX) =>
      `(tactic|
        rr_product_C_add_X_sequence using
          base := $hbase,
          cutoff := $N,
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
        cutoff := $N:term,
        recurrence := $hrec:term,
        certificate := rootZeroPow) =>
      `(tactic|
        rr_product_X_pow_sequence using
          base := $hbase,
          cutoff := $N,
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
        cutoff := $N:term,
        recurrence := $hrec:term,
        certificate := xAddCPow) =>
      `(tactic|
        rr_product_X_add_C_pow_sequence using
          base := $hbase,
          cutoff := $N,
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
        cutoff := $N:term,
        recurrence := $hrec:term,
        certificate := cAddXPow) =>
      `(tactic|
        rr_product_C_add_X_pow_sequence using
          base := $hbase,
          cutoff := $N,
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
        scalar_ne := $hs:term,
        cutoff := $N:term,
        recurrence := $hrec:term,
        certificate := scalar) =>
      `(tactic|
        rr_product_scalar_sequence using
          base := $hbase,
          scalar_ne := $hs,
          cutoff := $N,
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
      rr_product_factor_sequence using
        base := $hbase:term,
        cutoff := $N:term,
        recurrence := $hrec:term,
        certificate := scalarAuto) =>
      `(tactic|
        rr_product_scalar_sequence_auto using
          base := $hbase,
          cutoff := $N,
          recurrence := $hrec)
  | `(tactic|
      rr_product_factor_sequence using
        base := $hbase:term,
        scalar_ne := $hs:term,
        recurrence := $hrec:term,
        certificate := scalarPow) =>
      `(tactic|
        rr_product_C_pow_sequence using
          base := $hbase,
          scalar_ne := $hs,
          recurrence := $hrec)
  | `(tactic|
      rr_product_factor_sequence using
        base := $hbase:term,
        scalar_ne := $hs:term,
        cutoff := $N:term,
        recurrence := $hrec:term,
        certificate := scalarPow) =>
      `(tactic|
        rr_product_C_pow_sequence using
          base := $hbase,
          scalar_ne := $hs,
          cutoff := $N,
          recurrence := $hrec)
  | `(tactic|
      rr_product_factor_sequence using
        base := $hbase:term,
        recurrence := $hrec:term,
        certificate := scalarPowAuto) =>
      `(tactic|
        rr_product_C_pow_sequence_auto using
          base := $hbase,
          recurrence := $hrec)
  | `(tactic|
      rr_product_factor_sequence using
        base := $hbase:term,
        cutoff := $N:term,
        recurrence := $hrec:term,
        certificate := scalarPowAuto) =>
      `(tactic|
        rr_product_C_pow_sequence_auto using
          base := $hbase,
          cutoff := $N,
          recurrence := $hrec)
  | `(tactic|
      rr_product_factor_sequence using
        base := $hbase:term,
        slope_ne := $hs:term,
        recurrence := $hrec:term,
        certificate := affinePow) =>
      `(tactic|
        rr_product_affine_pow_sequence using
          base := $hbase,
          slope_ne := $hs,
          recurrence := $hrec)
  | `(tactic|
      rr_product_factor_sequence using
        base := $hbase:term,
        slope_ne := $hs:term,
        cutoff := $N:term,
        recurrence := $hrec:term,
        certificate := affinePow) =>
      `(tactic|
        rr_product_affine_pow_sequence using
          base := $hbase,
          slope_ne := $hs,
          cutoff := $N,
          recurrence := $hrec)
  | `(tactic|
      rr_product_factor_sequence using
        base := $hbase:term,
        recurrence := $hrec:term,
        certificate := affinePowAuto) =>
      `(tactic|
        rr_product_affine_pow_sequence_auto using
          base := $hbase,
          recurrence := $hrec)
  | `(tactic|
      rr_product_factor_sequence using
        base := $hbase:term,
        cutoff := $N:term,
        recurrence := $hrec:term,
        certificate := affinePowAuto) =>
      `(tactic|
        rr_product_affine_pow_sequence_auto using
          base := $hbase,
          cutoff := $N,
          recurrence := $hrec)
  | `(tactic|
      rr_product_factor_sequence using
        base := $hbase:term,
        slope_ne := $hs:term,
        recurrence := $hrec:term,
        certificate := constFirstAffinePow) =>
      `(tactic|
        rr_product_const_first_affine_pow_sequence using
          base := $hbase,
          slope_ne := $hs,
          recurrence := $hrec)
  | `(tactic|
      rr_product_factor_sequence using
        base := $hbase:term,
        slope_ne := $hs:term,
        cutoff := $N:term,
        recurrence := $hrec:term,
        certificate := constFirstAffinePow) =>
      `(tactic|
        rr_product_const_first_affine_pow_sequence using
          base := $hbase,
          slope_ne := $hs,
          cutoff := $N,
          recurrence := $hrec)
  | `(tactic|
      rr_product_factor_sequence using
        base := $hbase:term,
        recurrence := $hrec:term,
        certificate := constFirstAffinePowAuto) =>
      `(tactic|
        rr_product_const_first_affine_pow_sequence_auto using
          base := $hbase,
          recurrence := $hrec)
  | `(tactic|
      rr_product_factor_sequence using
        base := $hbase:term,
        cutoff := $N:term,
        recurrence := $hrec:term,
        certificate := constFirstAffinePowAuto) =>
      `(tactic|
        rr_product_const_first_affine_pow_sequence_auto using
          base := $hbase,
          cutoff := $N,
          recurrence := $hrec)
  | `(tactic|
      rr_product_formula_sequence using
        formula := $hroot:term,
        certificate := finiteLinearProduct) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.finiteLinearProductSequence_realRooted $hroot))
  | `(tactic|
      rr_product_formula_sequence using
        scalar_ne_zero := $hc:term,
        root_grid := $hroot:term,
        certificate := scalarFiniteLinearProduct) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.finiteLinearProductScalarSequence_realRooted $hc $hroot))
  | `(tactic|
      rr_j1_factorable_sequence_realrooted using
        scalar_ne_zero := $hc:term,
        root_grid := $hroot:term,
        certificate := finiteLinearProduct) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.j1FactorableLag3Sequence_realRooted $hc $hroot))
  | `(tactic|
      rr_j1_gap3_reciprocal_sequence_realrooted using
        model_realrooted := $hmodel:term,
        degree := $hdegree:term,
        reciprocal := $hreciprocal:term,
        certificate := modelRealRooted) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_j1_gap3_reciprocal_sequence
            $hmodel $hdegree $hreciprocal))
  | `(tactic|
      rr_j1_gap3_reciprocal_sequence_realrooted using
        model_pf := $hmodel:term,
        model_ne := $hmodel_ne:term,
        degree := $hdegree:term,
        reciprocal := $hreciprocal:term,
        certificate := modelPF) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_j1_gap3_reciprocal_pf_sequence
            $hmodel $hmodel_ne $hdegree $hreciprocal))
  | `(tactic|
      rr_product_parity_sequence using
        base := $hbase:term,
        scalar_ne := $ha:term,
        factor_realrooted := $hfactor:term,
        cutoff := $N:term,
        scalar_step := $hscalar:term,
        factor_step := $hstep:term,
        certificate := scalarThenFactor) =>
      `(tactic|
        rr_product_scalar_factor_sequence using
          base := $hbase,
          scalar_ne := $ha,
          factor_realrooted := $hfactor,
          cutoff := $N,
          scalar_step := $hscalar,
          factor_step := $hstep)
  | `(tactic|
      rr_product_parity_sequence using
        base := $hbase:term,
        scalar_ne := $ha:term,
        factor_realrooted := $hfactor:term,
        scalar_step := $hscalar:term,
        factor_step := $hstep:term,
        certificate := scalarThenFactor) =>
      `(tactic|
        rr_product_scalar_factor_sequence using
          base := $hbase,
          scalar_ne := $ha,
          factor_realrooted := $hfactor,
          scalar_step := $hscalar,
          factor_step := $hstep)
  | `(tactic|
      rr_product_parity_sequence using
        base := $hbase:term,
        factor_realrooted := $hfactor:term,
        cutoff := $N:term,
        scalar_step := $hscalar:term,
        factor_step := $hstep:term,
        certificate := scalarThenFactorAuto) =>
      `(tactic|
        rr_product_scalar_factor_sequence_auto using
          base := $hbase,
          factor_realrooted := $hfactor,
          cutoff := $N,
          scalar_step := $hscalar,
          factor_step := $hstep)
  | `(tactic|
      rr_product_parity_sequence using
        base := $hbase:term,
        factor_realrooted := $hfactor:term,
        scalar_step := $hscalar:term,
        factor_step := $hstep:term,
        certificate := scalarThenFactorAuto) =>
      `(tactic|
        rr_product_scalar_factor_sequence_auto using
          base := $hbase,
          factor_realrooted := $hfactor,
          scalar_step := $hscalar,
          factor_step := $hstep)
  | `(tactic|
      rr_product_parity_sequence using
        base := $hbase:term,
        scalar_ne := $ha:term,
        cutoff := $N:term,
        scalar_step := $hscalar:term,
        linear_step := $hlinear:term,
        certificate := scalarThenXAddC) =>
      `(tactic|
        rr_product_scalar_linear_sequence using
          base := $hbase,
          scalar_ne := $ha,
          cutoff := $N,
          scalar_step := $hscalar,
          linear_step := $hlinear)
  | `(tactic|
      rr_product_parity_sequence using
        base := $hbase:term,
        scalar_ne := $ha:term,
        scalar_step := $hscalar:term,
        linear_step := $hlinear:term,
        certificate := scalarThenXAddC) =>
      `(tactic|
        rr_product_scalar_linear_sequence using
          base := $hbase,
          scalar_ne := $ha,
          scalar_step := $hscalar,
          linear_step := $hlinear)
  | `(tactic|
      rr_product_parity_sequence using
        base := $hbase:term,
        cutoff := $N:term,
        scalar_step := $hscalar:term,
        linear_step := $hlinear:term,
        certificate := scalarThenXAddCAuto) =>
      `(tactic|
        rr_product_scalar_linear_sequence_auto using
          base := $hbase,
          cutoff := $N,
          scalar_step := $hscalar,
          linear_step := $hlinear)
  | `(tactic|
      rr_product_parity_sequence using
        base := $hbase:term,
        scalar_step := $hscalar:term,
        linear_step := $hlinear:term,
        certificate := scalarThenXAddCAuto) =>
      `(tactic|
        rr_product_scalar_linear_sequence_auto using
          base := $hbase,
          scalar_step := $hscalar,
          linear_step := $hlinear)
  | `(tactic|
      rr_product_parity_sequence using
        base := $hbase:term,
        scalar_ne := $ha:term,
        cutoff := $N:term,
        scalar_step := $hscalar:term,
        linear_step := $hlinear:term,
        certificate := scalarThenCAddX) =>
      `(tactic|
        rr_product_scalar_C_add_X_sequence using
          base := $hbase,
          scalar_ne := $ha,
          cutoff := $N,
          scalar_step := $hscalar,
          linear_step := $hlinear)
  | `(tactic|
      rr_product_parity_sequence using
        base := $hbase:term,
        scalar_ne := $ha:term,
        scalar_step := $hscalar:term,
        linear_step := $hlinear:term,
        certificate := scalarThenCAddX) =>
      `(tactic|
        rr_product_scalar_C_add_X_sequence using
          base := $hbase,
          scalar_ne := $ha,
          scalar_step := $hscalar,
          linear_step := $hlinear)
  | `(tactic|
      rr_product_parity_sequence using
        base := $hbase:term,
        cutoff := $N:term,
        scalar_step := $hscalar:term,
        linear_step := $hlinear:term,
        certificate := scalarThenCAddXAuto) =>
      `(tactic|
        rr_product_scalar_C_add_X_sequence_auto using
          base := $hbase,
          cutoff := $N,
          scalar_step := $hscalar,
          linear_step := $hlinear)
  | `(tactic|
      rr_product_parity_sequence using
        base := $hbase:term,
        scalar_step := $hscalar:term,
        linear_step := $hlinear:term,
        certificate := scalarThenCAddXAuto) =>
      `(tactic|
        rr_product_scalar_C_add_X_sequence_auto using
          base := $hbase,
          scalar_step := $hscalar,
          linear_step := $hlinear)
  | `(tactic|
      rr_product_parity_sequence using
        base := $hbase:term,
        scalar_ne := $ha:term,
        cutoff := $N:term,
        scalar_step := $hscalar:term,
        factor_step := $hstep:term,
        certificate := scalarThenRootZeroPow) =>
      `(tactic|
        rr_product_scalar_X_pow_sequence using
          base := $hbase,
          scalar_ne := $ha,
          cutoff := $N,
          scalar_step := $hscalar,
          factor_step := $hstep)
  | `(tactic|
      rr_product_parity_sequence using
        base := $hbase:term,
        scalar_ne := $ha:term,
        scalar_step := $hscalar:term,
        factor_step := $hstep:term,
        certificate := scalarThenRootZeroPow) =>
      `(tactic|
        rr_product_scalar_X_pow_sequence using
          base := $hbase,
          scalar_ne := $ha,
          scalar_step := $hscalar,
          factor_step := $hstep)
  | `(tactic|
      rr_product_parity_sequence using
        base := $hbase:term,
        cutoff := $N:term,
        scalar_step := $hscalar:term,
        factor_step := $hstep:term,
        certificate := scalarThenRootZeroPowAuto) =>
      `(tactic|
        rr_product_scalar_X_pow_sequence_auto using
          base := $hbase,
          cutoff := $N,
          scalar_step := $hscalar,
          factor_step := $hstep)
  | `(tactic|
      rr_product_parity_sequence using
        base := $hbase:term,
        scalar_step := $hscalar:term,
        factor_step := $hstep:term,
        certificate := scalarThenRootZeroPowAuto) =>
      `(tactic|
        rr_product_scalar_X_pow_sequence_auto using
          base := $hbase,
          scalar_step := $hscalar,
          factor_step := $hstep)
  | `(tactic|
      rr_product_parity_sequence using
        base := $hbase:term,
        scalar_ne := $ha:term,
        cutoff := $N:term,
        scalar_step := $hscalar:term,
        factor_step := $hstep:term,
        certificate := scalarThenXAddCPow) =>
      `(tactic|
        rr_product_scalar_X_add_C_pow_sequence using
          base := $hbase,
          scalar_ne := $ha,
          cutoff := $N,
          scalar_step := $hscalar,
          factor_step := $hstep)
  | `(tactic|
      rr_product_parity_sequence using
        base := $hbase:term,
        scalar_ne := $ha:term,
        scalar_step := $hscalar:term,
        factor_step := $hstep:term,
        certificate := scalarThenXAddCPow) =>
      `(tactic|
        rr_product_scalar_X_add_C_pow_sequence using
          base := $hbase,
          scalar_ne := $ha,
          scalar_step := $hscalar,
          factor_step := $hstep)
  | `(tactic|
      rr_product_parity_sequence using
        base := $hbase:term,
        cutoff := $N:term,
        scalar_step := $hscalar:term,
        factor_step := $hstep:term,
        certificate := scalarThenXAddCPowAuto) =>
      `(tactic|
        rr_product_scalar_X_add_C_pow_sequence_auto using
          base := $hbase,
          cutoff := $N,
          scalar_step := $hscalar,
          factor_step := $hstep)
  | `(tactic|
      rr_product_parity_sequence using
        base := $hbase:term,
        scalar_step := $hscalar:term,
        factor_step := $hstep:term,
        certificate := scalarThenXAddCPowAuto) =>
      `(tactic|
        rr_product_scalar_X_add_C_pow_sequence_auto using
          base := $hbase,
          scalar_step := $hscalar,
          factor_step := $hstep)
  | `(tactic|
      rr_product_parity_sequence using
        base := $hbase:term,
        scalar_ne := $ha:term,
        cutoff := $N:term,
        scalar_step := $hscalar:term,
        factor_step := $hstep:term,
        certificate := scalarThenCAddXPow) =>
      `(tactic|
        rr_product_scalar_C_add_X_pow_sequence using
          base := $hbase,
          scalar_ne := $ha,
          cutoff := $N,
          scalar_step := $hscalar,
          factor_step := $hstep)
  | `(tactic|
      rr_product_parity_sequence using
        base := $hbase:term,
        scalar_ne := $ha:term,
        scalar_step := $hscalar:term,
        factor_step := $hstep:term,
        certificate := scalarThenCAddXPow) =>
      `(tactic|
        rr_product_scalar_C_add_X_pow_sequence using
          base := $hbase,
          scalar_ne := $ha,
          scalar_step := $hscalar,
          factor_step := $hstep)
  | `(tactic|
      rr_product_parity_sequence using
        base := $hbase:term,
        cutoff := $N:term,
        scalar_step := $hscalar:term,
        factor_step := $hstep:term,
        certificate := scalarThenCAddXPowAuto) =>
      `(tactic|
        rr_product_scalar_C_add_X_pow_sequence_auto using
          base := $hbase,
          cutoff := $N,
          scalar_step := $hscalar,
          factor_step := $hstep)
  | `(tactic|
      rr_product_parity_sequence using
        base := $hbase:term,
        scalar_step := $hscalar:term,
        factor_step := $hstep:term,
        certificate := scalarThenCAddXPowAuto) =>
      `(tactic|
        rr_product_scalar_C_add_X_pow_sequence_auto using
          base := $hbase,
          scalar_step := $hscalar,
          factor_step := $hstep)
  | `(tactic|
      rr_product_parity_lift_sequence using
        even_realrooted := $hquot:term,
        scalar_ne := $ha:term,
        even_factorization := $heven:term,
        odd_factorization := $hodd:term,
        certificate := scalarXOdd) =>
      `(tactic|
        rr_even_product_odd_X_scalar_sequence using
          even_realrooted := $hquot,
          scalar_ne := $ha,
          even_factorization := $heven,
          odd_factorization := $hodd)
  | `(tactic|
      rr_endpoint_pair_sequence using
        base := $hbase:term,
        left_nonneg := $hleft_nonneg:term,
        right_nonneg := $hright_nonneg:term,
        sum_step := $hsum_step:term,
        x_step := $hx_step:term,
        coprime := $hcop:term,
        certificate := sumThenX) =>
      `(tactic|
        rr_endpoint_sum_then_X_pair_sequence using
          base := $hbase,
          left_nonneg := $hleft_nonneg,
          right_nonneg := $hright_nonneg,
          sum_step := $hsum_step,
          x_step := $hx_step,
          coprime := $hcop)
  | `(tactic|
      rr_endpoint_pair_sequence_realrooted using
        base := $hbase:term,
        left_nonneg := $hleft_nonneg:term,
        right_nonneg := $hright_nonneg:term,
        sum_step := $hsum_step:term,
        x_step := $hx_step:term,
        coprime := $hcop:term,
        certificate := sumThenX) =>
      `(tactic|
        rr_endpoint_sum_then_X_pair_sequence_realrooted using
          base := $hbase,
          left_nonneg := $hleft_nonneg,
          right_nonneg := $hright_nonneg,
          sum_step := $hsum_step,
          x_step := $hx_step,
          coprime := $hcop)
  | `(tactic|
      rr_endpoint_pair_sequence using
        base := $hbase:term,
        left_nonneg := $hleft_nonneg:term,
        right_nonneg := $hright_nonneg:term,
        x_step := $hx_step:term,
        sum_step := $hsum_step:term,
        coprime := $hcop:term,
        certificate := xThenSum) =>
      `(tactic|
        rr_endpoint_X_then_sum_pair_sequence using
          base := $hbase,
          left_nonneg := $hleft_nonneg,
          right_nonneg := $hright_nonneg,
          x_step := $hx_step,
          sum_step := $hsum_step,
          coprime := $hcop)
  | `(tactic|
      rr_endpoint_pair_sequence_realrooted using
        base := $hbase:term,
        left_nonneg := $hleft_nonneg:term,
        right_nonneg := $hright_nonneg:term,
        x_step := $hx_step:term,
        sum_step := $hsum_step:term,
        coprime := $hcop:term,
        certificate := xThenSum) =>
      `(tactic|
        rr_endpoint_X_then_sum_pair_sequence_realrooted using
          base := $hbase,
          left_nonneg := $hleft_nonneg,
          right_nonneg := $hright_nonneg,
          x_step := $hx_step,
          sum_step := $hsum_step,
          coprime := $hcop)
  | `(tactic|
      rr_endpoint_pair_lift_sequence using
        base := $hbase:term,
        left_nonneg := $hleft_nonneg:term,
        right_nonneg := $hright_nonneg:term,
        sum_step := $hsum_step:term,
        x_step := $hx_step:term,
        coprime := $hcop:term,
        even_factorization := $heven:term,
        odd_factorization := $hodd:term,
        certificate := sumThenX) =>
      `(tactic|
        rr_endpoint_sum_then_X_pair_lift_sequence using
          base := $hbase,
          left_nonneg := $hleft_nonneg,
          right_nonneg := $hright_nonneg,
          sum_step := $hsum_step,
          x_step := $hx_step,
          coprime := $hcop,
          even_factorization := $heven,
          odd_factorization := $hodd)
  | `(tactic|
      rr_endpoint_pair_lift_sequence using
        base := $hbase:term,
        left_nonneg := $hleft_nonneg:term,
        right_nonneg := $hright_nonneg:term,
        x_step := $hx_step:term,
        sum_step := $hsum_step:term,
        coprime := $hcop:term,
        even_factorization := $heven:term,
        odd_factorization := $hodd:term,
        certificate := xThenSum) =>
      `(tactic|
        rr_endpoint_X_then_sum_pair_lift_sequence using
          base := $hbase,
          left_nonneg := $hleft_nonneg,
          right_nonneg := $hright_nonneg,
          x_step := $hx_step,
          sum_step := $hsum_step,
          coprime := $hcop,
          even_factorization := $heven,
          odd_factorization := $hodd)
  | `(tactic|
      rr_endpoint_pair_lift_sequence using
        base := $hbase:term,
        left_nonneg := $hleft_nonneg:term,
        right_nonneg := $hright_nonneg:term,
        x_step := $hx_step:term,
        sum_step := $hsum_step:term,
        coprime := $hcop:term,
        even_factorization := $heven:term,
        odd_factorization := $hodd:term,
        certificate := xThenSumSwapped) =>
      `(tactic|
        rr_endpoint_X_then_sum_pair_lift_swapped_sequence using
          base := $hbase,
          left_nonneg := $hleft_nonneg,
          right_nonneg := $hright_nonneg,
          x_step := $hx_step,
          sum_step := $hsum_step,
          coprime := $hcop,
          even_factorization := $heven,
          odd_factorization := $hodd)
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
        base := $hbase:term,
        quotient_realrooted := $hquot:term,
        factor_realrooted := $hfactor:term,
        cutoff := $N:term,
        factorization := $hrow:term,
        certificate := suppliedFactor) =>
      `(tactic|
        rr_product_lift_sequence using
          base := $hbase,
          quotient_realrooted := $hquot,
          factor_realrooted := $hfactor,
          cutoff := $N,
          factorization := $hrow)
  | `(tactic|
      rr_product_lift_sequence using
        quotient_realrooted := $hquot:term,
        factorization := $hrow:term,
        certificate := auto) =>
      `(tactic|
        rr_product_lift_sequence_auto using
          quotient_realrooted := $hquot,
          factorization := $hrow)
  | `(tactic|
      rr_product_lift_sequence using
        base := $hbase:term,
        quotient_realrooted := $hquot:term,
        cutoff := $N:term,
        factorization := $hrow:term,
        certificate := auto) =>
      `(tactic|
        rr_product_lift_sequence_auto using
          base := $hbase,
          quotient_realrooted := $hquot,
          cutoff := $N,
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
        base := $hbase:term,
        quotient_realrooted := $hquot:term,
        cutoff := $N:term,
        factorization := $hrow:term,
        certificate := rootZero) =>
      `(tactic|
        rr_product_lift_X_sequence using
          base := $hbase,
          quotient_realrooted := $hquot,
          cutoff := $N,
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
        base := $hbase:term,
        quotient_realrooted := $hquot:term,
        cutoff := $N:term,
        factorization := $hrow:term,
        certificate := rootZeroPow) =>
      `(tactic|
        rr_product_lift_X_pow_sequence using
          base := $hbase,
          quotient_realrooted := $hquot,
          cutoff := $N,
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
        base := $hbase:term,
        quotient_realrooted := $hquot:term,
        cutoff := $N:term,
        factorization := $hrow:term,
        certificate := xAddC) =>
      `(tactic|
        rr_product_lift_X_add_C_sequence using
          base := $hbase,
          quotient_realrooted := $hquot,
          cutoff := $N,
          factorization := $hrow)
  | `(tactic|
      rr_product_lift_sequence using
        quotient_realrooted := $hquot:term,
        factorization := $hrow:term,
        certificate := cAddX) =>
      `(tactic|
        rr_product_lift_C_add_X_sequence using
          quotient_realrooted := $hquot,
          factorization := $hrow)
  | `(tactic|
      rr_product_lift_sequence using
        base := $hbase:term,
        quotient_realrooted := $hquot:term,
        cutoff := $N:term,
        factorization := $hrow:term,
        certificate := cAddX) =>
      `(tactic|
        rr_product_lift_C_add_X_sequence using
          base := $hbase,
          quotient_realrooted := $hquot,
          cutoff := $N,
          factorization := $hrow)
  | `(tactic|
      rr_product_lift_sequence using
        quotient_realrooted := $hquot:term,
        factorization := $hrow:term,
        certificate := fixedXAddCPow) =>
      `(tactic|
        rr_product_lift_X_add_C_pow_sequence using
          quotient_realrooted := $hquot,
          factorization := $hrow)
  | `(tactic|
      rr_product_lift_sequence using
        base := $hbase:term,
        quotient_realrooted := $hquot:term,
        cutoff := $N:term,
        factorization := $hrow:term,
        certificate := fixedXAddCPow) =>
      `(tactic|
        rr_product_lift_X_add_C_pow_sequence using
          base := $hbase,
          quotient_realrooted := $hquot,
          cutoff := $N,
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
        base := $hbase:term,
        quotient_realrooted := $hquot:term,
        cutoff := $N:term,
        factorization := $hrow:term,
        certificate := rowXAddCPow) =>
      `(tactic|
        rr_product_lift_X_add_C_row_pow_sequence using
          base := $hbase,
          quotient_realrooted := $hquot,
          cutoff := $N,
          factorization := $hrow)
  | `(tactic|
      rr_product_lift_sequence using
        quotient_realrooted := $hquot:term,
        factorization := $hrow:term,
        certificate := cAddXPow) =>
      `(tactic|
        rr_product_lift_C_add_X_pow_sequence using
          quotient_realrooted := $hquot,
          factorization := $hrow)
  | `(tactic|
      rr_product_lift_sequence using
        base := $hbase:term,
        quotient_realrooted := $hquot:term,
        cutoff := $N:term,
        factorization := $hrow:term,
        certificate := cAddXPow) =>
      `(tactic|
        rr_product_lift_C_add_X_pow_sequence using
          base := $hbase,
          quotient_realrooted := $hquot,
          cutoff := $N,
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
        base := $hbase:term,
        quotient_realrooted := $hquot:term,
        scalar_ne := $hscalar:term,
        cutoff := $N:term,
        factorization := $hrow:term,
        certificate := scalar) =>
      `(tactic|
        rr_product_lift_C_sequence using
          base := $hbase,
          quotient_realrooted := $hquot,
          scalar_ne := $hscalar,
          cutoff := $N,
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
        base := $hbase:term,
        quotient_realrooted := $hquot:term,
        cutoff := $N:term,
        factorization := $hrow:term,
        certificate := scalarAuto) =>
      `(tactic|
        rr_product_lift_C_sequence_auto using
          base := $hbase,
          quotient_realrooted := $hquot,
          cutoff := $N,
          factorization := $hrow)
  | `(tactic|
      rr_product_lift_sequence using
        quotient_realrooted := $hquot:term,
        scalar_ne := $hscalar:term,
        factorization := $hrow:term,
        certificate := scalarPow) =>
      `(tactic|
        rr_product_lift_C_pow_sequence using
          quotient_realrooted := $hquot,
          scalar_ne := $hscalar,
          factorization := $hrow)
  | `(tactic|
      rr_product_lift_sequence using
        base := $hbase:term,
        quotient_realrooted := $hquot:term,
        scalar_ne := $hscalar:term,
        cutoff := $N:term,
        factorization := $hrow:term,
        certificate := scalarPow) =>
      `(tactic|
        rr_product_lift_C_pow_sequence using
          base := $hbase,
          quotient_realrooted := $hquot,
          scalar_ne := $hscalar,
          cutoff := $N,
          factorization := $hrow)
  | `(tactic|
      rr_product_lift_sequence using
        quotient_realrooted := $hquot:term,
        factorization := $hrow:term,
        certificate := scalarPowAuto) =>
      `(tactic|
        rr_product_lift_C_pow_sequence_auto using
          quotient_realrooted := $hquot,
          factorization := $hrow)
  | `(tactic|
      rr_product_lift_sequence using
        base := $hbase:term,
        quotient_realrooted := $hquot:term,
        cutoff := $N:term,
        factorization := $hrow:term,
        certificate := scalarPowAuto) =>
      `(tactic|
        rr_product_lift_C_pow_sequence_auto using
          base := $hbase,
          quotient_realrooted := $hquot,
          cutoff := $N,
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
        base := $hbase:term,
        quotient_realrooted := $hquot:term,
        slope_ne := $hslope:term,
        cutoff := $N:term,
        factorization := $hrow:term,
        certificate := affine) =>
      `(tactic|
        rr_product_lift_affine_sequence using
          base := $hbase,
          quotient_realrooted := $hquot,
          slope_ne := $hslope,
          cutoff := $N,
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
      rr_product_lift_sequence using
        base := $hbase:term,
        quotient_realrooted := $hquot:term,
        cutoff := $N:term,
        factorization := $hrow:term,
        certificate := affineAuto) =>
      `(tactic|
        rr_product_lift_affine_sequence_auto using
          base := $hbase,
          quotient_realrooted := $hquot,
          cutoff := $N,
          factorization := $hrow)
  | `(tactic|
      rr_product_lift_sequence using
        quotient_realrooted := $hquot:term,
        slope_ne := $hslope:term,
        factorization := $hrow:term,
        certificate := constFirstAffine) =>
      `(tactic|
        rr_product_lift_const_first_sequence using
          quotient_realrooted := $hquot,
          slope_ne := $hslope,
          factorization := $hrow)
  | `(tactic|
      rr_product_lift_sequence using
        base := $hbase:term,
        quotient_realrooted := $hquot:term,
        slope_ne := $hslope:term,
        cutoff := $N:term,
        factorization := $hrow:term,
        certificate := constFirstAffine) =>
      `(tactic|
        rr_product_lift_const_first_sequence using
          base := $hbase,
          quotient_realrooted := $hquot,
          slope_ne := $hslope,
          cutoff := $N,
          factorization := $hrow)
  | `(tactic|
      rr_product_lift_sequence using
        quotient_realrooted := $hquot:term,
        factorization := $hrow:term,
        certificate := constFirstAffineAuto) =>
      `(tactic|
        rr_product_lift_const_first_sequence_auto using
          quotient_realrooted := $hquot,
          factorization := $hrow)
  | `(tactic|
      rr_product_lift_sequence using
        base := $hbase:term,
        quotient_realrooted := $hquot:term,
        cutoff := $N:term,
        factorization := $hrow:term,
        certificate := constFirstAffineAuto) =>
      `(tactic|
        rr_product_lift_const_first_sequence_auto using
          base := $hbase,
          quotient_realrooted := $hquot,
          cutoff := $N,
          factorization := $hrow)
  | `(tactic|
      rr_product_lift_sequence using
        quotient_realrooted := $hquot:term,
        slope_ne := $hslope:term,
        factorization := $hrow:term,
        certificate := affinePow) =>
      `(tactic|
        rr_product_lift_affine_pow_sequence using
          quotient_realrooted := $hquot,
          slope_ne := $hslope,
          factorization := $hrow)
  | `(tactic|
      rr_product_lift_sequence using
        base := $hbase:term,
        quotient_realrooted := $hquot:term,
        slope_ne := $hslope:term,
        cutoff := $N:term,
        factorization := $hrow:term,
        certificate := affinePow) =>
      `(tactic|
        rr_product_lift_affine_pow_sequence using
          base := $hbase,
          quotient_realrooted := $hquot,
          slope_ne := $hslope,
          cutoff := $N,
          factorization := $hrow)
  | `(tactic|
      rr_product_lift_sequence using
        quotient_realrooted := $hquot:term,
        factorization := $hrow:term,
        certificate := affinePowAuto) =>
      `(tactic|
        rr_product_lift_affine_pow_sequence_auto using
          quotient_realrooted := $hquot,
          factorization := $hrow)
  | `(tactic|
      rr_product_lift_sequence using
        base := $hbase:term,
        quotient_realrooted := $hquot:term,
        cutoff := $N:term,
        factorization := $hrow:term,
        certificate := affinePowAuto) =>
      `(tactic|
        rr_product_lift_affine_pow_sequence_auto using
          base := $hbase,
          quotient_realrooted := $hquot,
          cutoff := $N,
          factorization := $hrow)
  | `(tactic|
      rr_product_lift_sequence using
        quotient_realrooted := $hquot:term,
        slope_ne := $hslope:term,
        factorization := $hrow:term,
        certificate := constFirstAffinePow) =>
      `(tactic|
        rr_product_lift_const_first_affine_pow_sequence using
          quotient_realrooted := $hquot,
          slope_ne := $hslope,
          factorization := $hrow)
  | `(tactic|
      rr_product_lift_sequence using
        base := $hbase:term,
        quotient_realrooted := $hquot:term,
        slope_ne := $hslope:term,
        cutoff := $N:term,
        factorization := $hrow:term,
        certificate := constFirstAffinePow) =>
      `(tactic|
        rr_product_lift_const_first_affine_pow_sequence using
          base := $hbase,
          quotient_realrooted := $hquot,
          slope_ne := $hslope,
          cutoff := $N,
          factorization := $hrow)
  | `(tactic|
      rr_product_lift_sequence using
        quotient_realrooted := $hquot:term,
        factorization := $hrow:term,
        certificate := constFirstAffinePowAuto) =>
      `(tactic|
        rr_product_lift_const_first_affine_pow_sequence_auto using
          quotient_realrooted := $hquot,
          factorization := $hrow)
  | `(tactic|
      rr_product_lift_sequence using
        base := $hbase:term,
        quotient_realrooted := $hquot:term,
        cutoff := $N:term,
        factorization := $hrow:term,
        certificate := constFirstAffinePowAuto) =>
      `(tactic|
        rr_product_lift_const_first_affine_pow_sequence_auto using
          base := $hbase,
          quotient_realrooted := $hquot,
          cutoff := $N,
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
        cutoff := $N:term,
        recurrence := $hrec:term,
        certificate := identity) =>
      `(tactic|
        rr_product_identity_sequence using
          base := $hbase,
          cutoff := $N,
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
        base := $hbase:term,
        cutoff := $N:term,
        recurrence := $hrec:term,
        certificate := rootZero) =>
      `(tactic|
        rr_product_root_zero_sequence using
          base := $hbase,
          cutoff := $N,
          recurrence := $hrec)
  | `(tactic|
      rr_product_exit_sequence using
        base := $hbase:term,
        recurrence := $hrec:term,
        certificate := auto) =>
      `(tactic|
        first
          | rr_product_identity_sequence using
              base := $hbase,
              recurrence := $hrec
          | rr_product_root_zero_sequence using
              base := $hbase,
              recurrence := $hrec)
  | `(tactic|
      rr_product_exit_sequence using
        base := $hbase:term,
        cutoff := $N:term,
        recurrence := $hrec:term,
        certificate := auto) =>
      `(tactic|
        first
          | rr_product_identity_sequence using
              base := $hbase,
              cutoff := $N,
              recurrence := $hrec
          | rr_product_root_zero_sequence using
              base := $hbase,
              cutoff := $N,
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
      rr_product_exit_sequence using
        base := $hbase:term,
        cutoff := $N:term,
        recurrence := $hrec:term,
        certificate := periodTwo) =>
      `(tactic|
        rr_product_period_two_sequence using
          base := $hbase,
          cutoff := $N,
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
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term,
        certificate := globalNonpos) =>
      `(tactic|
        rr_g_negative_lag_sequence_den using
          base := $hbase,
          pos_lc := $hpos,
          lag := $B,
          den_nonzero := rr_scalar_active_den_all_term,
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
          den_nonzero := rr_scalar_active_den_all_term,
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
          den_nonzero := rr_scalar_active_den_all_term,
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
          den_nonzero := rr_scalar_active_den_all_term,
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
          den_nonzero := rr_scalar_active_den_all_term,
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
          den_nonzero := rr_scalar_active_den_all_term,
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
          degree_two := $hdeg_two,
          deriv_factor := $V,
          lag_factor := $W,
          norm_deriv_coeff := $cV,
          norm_lag_coeff := $cW,
          den := $d,
          raw_deriv_coeff := $b,
          raw_lag_coeff := $e,
          den_nonzero := rr_scalar_active_den_all_term,
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
          degree_two := $hdeg_two,
          deriv_factor := $V,
          lag_factor := $W,
          norm_deriv_coeff := $cV,
          norm_lag_coeff := $cW,
          den := $d,
          raw_deriv_coeff := $b,
          raw_lag_coeff := $e,
          den_nonzero := rr_scalar_active_den_all_term,
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
