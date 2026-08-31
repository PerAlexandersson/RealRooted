import RealRooted.Tactic.AllCombo
import RealRooted.Tactic.AffineDerivative
import RealRooted.Tactic.MaWang
import RealRooted.Tactic.CubicDiscriminant
import RealRooted.Tactic.CoefficientShape
import RealRooted.Tactic.CommonInterleaver
import RealRooted.Tactic.Derivative
import RealRooted.Tactic.EulerOperator
import RealRooted.Tactic.Favard
import RealRooted.Tactic.GammaRealRoots
import RealRooted.Tactic.Hadamard
import RealRooted.Tactic.HermiteBiehler
import RealRooted.Tactic.HermitePoulain
import RealRooted.Tactic.IteratedDerivativeShift
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
import RealRooted.Tactic.Product
import RealRooted.Tactic.PosCombo
import RealRooted.Tactic.Narayana
import RealRooted.Tactic.RootBounds
import RealRooted.Tactic.RootCount
import RealRooted.Tactic.SecondDerivative
import RealRooted.Tactic.StaircaseSum
import RealRooted.Tactic.SymmetricDecomposition
import RealRooted.Tactic.VeroneseSection
import RealRooted.Tactic.WeightedSum
import RealRooted.Tactic.Wagner
import RealRooted.Tactic.WagnerX
import RealRooted.Tactic.OEIS.Basic
import RealRooted.Tactic.OEIS.DerivativeLag
import RealRooted.Tactic.OEIS.PositiveLag
import RealRooted.Tactic.OEIS.NegativeLag

/-!
# OEIS tactic wrapper stub

Planned user-facing dispatch:

```lean
rr_oeis ma_wang
rr_oeis favard
rr_oeis liu_wang
rr_oeis matrix
rr_favard using ...
rr_favard_const_unit using ...
rr_favard_const_row_sign_unit using ...
rr_favard_affine_param_den_auto using ...
rr_favard_affine_param_den_raw_auto using ...
rr_prec_C_mul_left_sequence using ...
rr_prec_C_mul_right_sequence using ...
rr_prec_C_mul_both_sequence using ...
rr_C_mul_realrooted_sequence using ...
rr_X_mul_realrooted_sequence using ...
rr_coeff_shape using ...
rr_fPolynomial_sequence_realrooted using ...
rr_of_fPolynomial_sequence_realrooted using ...
rr_fPolynomial_sequence_prec using ...
rr_of_fPolynomial_sequence_prec using ...
rr_fPolynomial_sequence_pos_combo using ...
rr_gamma_transform_sequence_realrooted_nonneg using ...
rr_gamma_transform_sequence_roots_nonpos_nonneg using ...
rr_gamma_transform_sequence_realrooted_nonpos using ...
rr_gamma_transform_sequence_backward using ...
rr_gamma_transform_sequence_backward_minimal using ...
rr_gamma_sequence_realrooted_iff using ...
rr_veronese_section_sequence_nonneg using ...
rr_veronese_section_sequence_pf_coeff using ...
rr_veronese_section_sequence_splits_pf using ...
rr_veronese_section_sequence_splits_nonneg using ...
rr_veronese_section_sequence_prec0 using ...
rr_veronese_section_sequence_prec using ...
rr_veronese_pair_sequence_prec0 using ...
rr_veronese_pair_sequence_prec using ...
rr_veronese_pair_fin_sequence_prec0 using ...
rr_veronese_pair_fin_sequence_prec using ...
rr_compatible_sequence_comm using ...
rr_compatible_sequence_comp_X_add_C using ...
rr_compatible_sequence_reflect using ...
rr_compatible_sequence_reflect_iff using ...
rr_compatible_sequence_derivative using ...
rr_compatible_sequence_left_realrooted using ...
rr_compatible_sequence_right_realrooted using ...
rr_compatible_sequence_right_degree_le_succ using ...
rr_compatible_sequence_degree_close using ...
rr_compatible_sequence_to_pos_combo using ...
rr_compatible_sequence_of_pos_combo using ...
rr_compatible_sequence_of_pos_combo_same_degree using ...
rr_compatible_sequence_of_pos_combo_succ_degree using ...
rr_compatible_sequence_of_common_left using ...
rr_compatible_sequence_of_common_right using ...
rr_pos_combo_sequence_comp_X_add_C using ...
rr_pairwise_compatible_sequence_of_common_left using ...
rr_pairwise_compatible_sequence_of_pairwise_common_left using ...
rr_pairwise_compatible_sequence_of_common_right using ...
rr_pairwise_compatible_sequence_of_pairwise_common_right using ...
rr_common_interleaver_sequence_of_pairwise using ...
rr_common_left_interleaver_sequence_of_pairwise using ...
rr_common_interleaver_sum_sequence_realrooted using ...
rr_common_left_interleaver_sum_sequence_realrooted using ...
rr_prec_affine_derivative_sequence using ...
rr_prec_affine_derivative_sequence_realrooted using ...
rr_prec_affine_derivative_nonneg_sequence using ...
rr_prec_affine_derivative_nonneg_sequence_realrooted using ...
rr_affine_deriv_coeff_sequence using ...
rr_affine_deriv_natDegree_sequence using ...
rr_affine_deriv_leadingCoeff_sequence using ...
rr_affine_deriv_ne_zero_sequence using ...
rr_all_combo_sequence_derivative using ...
rr_all_combo_sequence_to_pos_combo_sameDegree using ...
rr_derivative_sequence_prec using ...
rr_nonneg_coeffs_sequence_derivative using ...
rr_operator_all_combo_sequence using ...
rr_operator_prec0_sequence_up_to_order using ...
rr_pf_sequence_mul using ...
rr_pf_sequence_zero_or_splits using ...
rr_pos_combo_sequence_of_prec using ...
rr_pos_combo_sequence_add_realrooted using ...
rr_weighted_sum_sequence_left_prec using ...
rr_weighted_sum_sequence_right_prec using ...
rr_sum_sequence_left_prec using ...
rr_sum_sequence_right_prec using ...
rr_staircaseSum_sequence_prec using ...
rr_staircaseSum_sequence_realrooted using ...
rr_natDegree_add_C_mul_lt_sequence using ...
rr_leadingCoeff_add_C_mul_lt_sequence using ...
rr_exists_root_lt_succDegree_add_right_small_sequence using ...
rr_degreeIncreasing_local_lower_count_sequence using ...
rr_positiveParameter_local_lower_count_sequence using ...
rr_rightFamily_card_roots_gt_eq_local_lower_sequence using ...
rr_card_filter_gt_endpoint_eq_local_lower_sequence using ...
rr_closedSegment_not_isRoot_same_sign_sequence using ...
rr_rightFamily_eval_ne_zero_same_sign_sequence using ...
rr_exists_nonRoot_threshold_count_eq_sequence using ...
rr_exists_nonRoot_threshold_count_gt_eq_sequence using ...
rr_rootCount_diff_le_one_nonRoot_sequence using ...
rr_rootCount_abs_diff_le_one_nonRoot_sequence using ...
rr_rootCount_diff_le_one_nonRoot_isRoot_sequence using ...
rr_rootCountAbove_diff_le_one_nonRoot_sequence using ...
rr_rootCountAbove_diff_le_one_nonRoot_isRoot_sequence using ...
rr_rootCount_max_abs_diff_le_one_sequence using ...
rr_card_roots_filter_le_eq_no_isRoot_Ioc_sequence using ...
rr_card_roots_filter_gt_eq_no_isRoot_Ioc_sequence using ...
rr_card_roots_filter_Ioc_zero_no_isRoot_Ioc_sequence using ...
rr_card_roots_filter_all_eq_no_isRoot_Ioc_sequence using ...
rr_card_roots_filter_le_mono_sequence using ...
rr_card_roots_filter_gt_antitone_sequence using ...
rr_card_roots_filter_le_and_gt_mono_sequence using ...
rr_card_roots_filter_le_eq_no_isRoot_Icc_sequence using ...
rr_card_roots_filter_gt_eq_no_isRoot_Icc_sequence using ...
rr_card_roots_filter_Ioc_zero_no_isRoot_Icc_sequence using ...
rr_card_roots_filter_all_eq_no_isRoot_Icc_sequence using ...
rr_card_roots_filter_le_sub_eq_no_isRoot_Ioc_sequence using ...
rr_card_roots_filter_gt_sub_eq_no_isRoot_Ioc_sequence using ...
rr_card_roots_filter_le_bound_no_isRoot_Ioc_sequence using ...
rr_card_roots_filter_gt_bound_no_isRoot_Ioc_sequence using ...
rr_card_roots_filter_le_and_gt_bound_no_isRoot_Ioc_sequence using ...
rr_card_roots_filter_le_sub_eq_no_isRoot_Icc_sequence using ...
rr_card_roots_filter_gt_sub_eq_no_isRoot_Icc_sequence using ...
rr_card_roots_filter_le_bound_no_isRoot_Icc_sequence using ...
rr_card_roots_filter_gt_bound_no_isRoot_Icc_sequence using ...
rr_card_roots_filter_le_and_gt_bound_no_isRoot_Icc_sequence using ...
rr_left_card_roots_succDegree_sequence using ...
rr_right_card_roots_succDegree_sequence using ...
rr_left_ne_zero_card_roots_succDegree_sequence using ...
rr_right_ne_zero_card_roots_succDegree_sequence using ...
rr_rightFamily_sameDegree_gt_count_eq_sequence using ...
rr_rightFamily_zero_one_gt_count_eq_sequence using ...
rr_sameDegree_gt_count_eq_no_rightFamily_sequence using ...
rr_sameDegree_rootCountAbove_no_rightFamily_sequence using ...
rr_sameDegree_rootCountAbove_no_pos_crossing_sequence using ...
rr_sameDegree_rootCountAbove_pos_crossing_sequence using ...
rr_posCombo_sameDegree_rootCount_degree_le_two_sequence using ...
rr_posCombo_sameDegree_rootCountAbove_degree_le_two_sequence using ...
rr_sameDegree_rootCrossing_degree_le_one_sequence using ...
rr_posCombo_sameDegree_rootCrossing_degree_le_two_sequence using ...
rr_compatible_succDegree_rootCountAbove_le_two_sequence using ...
rr_posCombo_sameDegree_rootCount_degree_le_three using ...
rr_posCombo_sameDegree_rootCount_degree_le_three_sequence using ...
rr_posCombo_sameDegree_rootCountAbove_degree_le_three using ...
rr_posCombo_sameDegree_rootCountAbove_degree_le_three_sequence using ...
rr_posCombo_sameDegree_rootCrossing_degree_le_three using ...
rr_posCombo_sameDegree_rootCrossing_degree_le_three_sequence using ...
rr_posCombo_sameDegree_rootCount_cubicInterior_sequence using ...
rr_posCombo_sameDegree_rootCountAbove_cubicInterior_sequence using ...
rr_posCombo_sameDegree_rootCrossing_cubicInterior_sequence using ...
rr_theta_sequence_pf using ...
rr_thetaPlusOne_sequence_pf using ...
rr_iterateThetaPlusOne_sequence_pf using ...
rr_thetaPlusOne_sequence_prec0 using ...
rr_iterateThetaPlusOne_sequence_prec0 using ...
rr_TDeriv_sequence_splits using ...
rr_TDeriv_sequence_prec using ...
rr_iterateTDeriv_sequence_splits using ...
rr_iterateTDeriv_sequence_prec_succ using ...
rr_wagner_common_left_add_sequence using ...
rr_wagner_common_right_add_sequence using ...
rr_wagner_mulX_iff_sequence using ...
rr_hadamard_pf using ...
rr_hadamard_nonneg_realrooted using ...
rr_hadamard_nonneg_coeffs using ...
rr_hadamard_sequence_pf using ...
rr_hadamard_sequence_nonneg_realrooted using ...
rr_hadamard_sequence_nonneg_coeffs using ...
rr_hadamard_sequence_prec0 using ...
rr_schur_szego_sequence using ...
rr_schur_szego_sequence_splits using ...
rr_schur_szego_pf_factor_degree_le_two using ...
rr_schur_szego_pf_factor_degree_le_three_cubic using ...
rr_schur_szego_pf_factor_degree_le_three_num_left_degree using ...
rr_hermite_biehler_odd_even_hurwitz using ...
rr_hermite_biehler_odd_even_hurwitz_stable_sequence using ...
rr_hermite_poulain using ...
rr_hermite_poulain_sequence using ...
rr_jensen_sequence_nonneg using ...
rr_jensen_sequence_pf_of_finite_multiplier using ...
rr_jensen_sequence_pf_of_finite_pf_multiplier using ...
rr_finite_multiplier_sequence_mono using ...
rr_finite_multiplier_sequence_mul using ...
rr_finite_pf_multiplier_sequence_of_finite_multiplier using ...
rr_i2_derivative_lag_sequence using ... certificate := directHalfLine
rr_i2_derivative_lag_sequence using ... certificate := wagnerGap
rr_i2_derivative_lag_sequence_den_coeff using ... certificate := directHalfLine
rr_i2_derivative_lag_sequence_den using ... certificate := wagnerGap
rr_magnitude_dominated_sequence using ...
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
rr_j1_factorable_sequence_realrooted using ... certificate := finiteLinearProduct
rr_j1_gap3_reciprocal_sequence_realrooted using ... certificate := modelRealRooted
rr_j1_gap3_reciprocal_sequence_realrooted using ... certificate := modelPF
rr_kurtz using ...
rr_kurtz_sequence using ...
rr_mw_plus_derivative_sequence using ...
rr_mw_plus_derivative_sequence_expanded_auto using ...
rr_narayana_polynomial_splits using ...
rr_narayana_polynomial_sequence_splits using ...
rr_root_nonpos_sequence using ...
rr_root_le_neg_shift_sequence using ...
rr_derivative_root_nonpos_sequence using ...
rr_sign_at_roots_sequence using ...
rr_sign_at_roots_sequence_with_factor using ...
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

end Tactic
end RealRooted
