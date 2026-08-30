import RealRooted.ProductSequence
import RealRooted.Tactic.Finish

/-!
# Product-factor tactic frontend

Syntax and elaboration for applying the theorem backend in
`RealRooted.ProductSequence`.
-/

open Polynomial
open scoped BigOperators

namespace RealRooted

namespace Tactic

open Lean
open Lean.Elab.Tactic
open Lean.Meta

syntax (name := rr_product_C_named)
  "rr_product_C" " using "
    "scalar_ne" ":=" term :
  tactic

syntax (name := rr_product_C_auto) "rr_product_C_auto" : tactic

syntax (name := rr_product_C_pow_named)
  "rr_product_C_pow" " using "
    "scalar_ne" ":=" term ","
    "exponent" ":=" term :
  tactic

syntax (name := rr_product_C_pow_auto_named)
  "rr_product_C_pow_auto" " using "
    "exponent" ":=" term :
  tactic

syntax (name := rr_product_X_named) "rr_product_X" : tactic

syntax (name := rr_product_X_pow_named)
  "rr_product_X_pow" " using "
    "exponent" ":=" term :
  tactic

syntax (name := rr_product_X_add_C_named)
  "rr_product_X_add_C" " using "
    "constant" ":=" term :
  tactic

syntax (name := rr_product_X_add_C_pow_named)
  "rr_product_X_add_C_pow" " using "
    "constant" ":=" term ","
    "exponent" ":=" term :
  tactic

syntax (name := rr_product_C_add_X_named)
  "rr_product_C_add_X" " using "
    "constant" ":=" term :
  tactic

syntax (name := rr_product_C_add_X_pow_named)
  "rr_product_C_add_X_pow" " using "
    "constant" ":=" term ","
    "exponent" ":=" term :
  tactic

syntax (name := rr_product_affine_named)
  "rr_product_affine" " using "
    "slope_ne" ":=" term :
  tactic

syntax (name := rr_product_affine_auto) "rr_product_affine_auto" : tactic

syntax (name := rr_product_affine_pow_named)
  "rr_product_affine_pow" " using "
    "slope_ne" ":=" term ","
    "exponent" ":=" term :
  tactic

syntax (name := rr_product_affine_pow_auto_named)
  "rr_product_affine_pow_auto" " using "
    "exponent" ":=" term :
  tactic

syntax (name := rr_product_const_first_affine_named)
  "rr_product_const_first_affine" " using "
    "slope_ne" ":=" term :
  tactic

syntax (name := rr_product_const_first_affine_auto)
  "rr_product_const_first_affine_auto" :
  tactic

syntax (name := rr_product_const_first_affine_pow_named)
  "rr_product_const_first_affine_pow" " using "
    "slope_ne" ":=" term ","
    "exponent" ":=" term :
  tactic

syntax (name := rr_product_const_first_affine_pow_auto_named)
  "rr_product_const_first_affine_pow_auto" " using "
    "exponent" ":=" term :
  tactic

syntax (name := rr_product_factor)
  "rr_product_factor" " using " term ", " term : tactic

syntax (name := rr_product_factor_named)
  "rr_product_factor" " using "
    "realrooted" ":=" term ","
    "slope_ne" ":=" term :
  tactic

syntax (name := rr_product_factor_auto)
  "rr_product_factor_auto" " using " term : tactic

syntax (name := rr_product_factor_auto_named)
  "rr_product_factor_auto" " using "
    "realrooted" ":=" term :
  tactic

syntax (name := rr_product_factor_const_first)
  "rr_product_factor_const_first" " using " term ", " term : tactic

syntax (name := rr_product_factor_const_first_named)
  "rr_product_factor_const_first" " using "
    "realrooted" ":=" term ","
    "slope_ne" ":=" term :
  tactic

syntax (name := rr_product_factor_const_first_auto)
  "rr_product_factor_const_first_auto" " using " term : tactic

syntax (name := rr_product_factor_const_first_auto_named)
  "rr_product_factor_const_first_auto" " using "
    "realrooted" ":=" term :
  tactic

syntax (name := rr_product_factor_X)
  "rr_product_factor_X" " using " term : tactic

syntax (name := rr_product_factor_X_named)
  "rr_product_factor_X" " using "
    "realrooted" ":=" term :
  tactic

syntax (name := rr_product_factor_C_add_X)
  "rr_product_factor_C_add_X" " using " term : tactic

syntax (name := rr_product_factor_C_add_X_named)
  "rr_product_factor_C_add_X" " using "
    "realrooted" ":=" term :
  tactic

syntax (name := rr_product_factor_sequence_named)
  "rr_product_factor_sequence" " using "
    "base" ":=" term ","
    "factor_realrooted" ":=" term ","
    ("cutoff" ":=" term ",")?
    "recurrence" ":=" term :
  tactic

syntax (name := rr_product_factor_sequence)
  "rr_product_factor_sequence" " using " term ", " term ", " term :
  tactic

syntax (name := rr_product_factor_sequence_inferred_of_recurrence)
  "rr_product_factor_sequence" " using "
    "recurrence" ":=" term :
  tactic

syntax (name := rr_product_factor_sequence_from_inferred_of_recurrence)
  "rr_product_factor_sequence" " using "
    "cutoff" ":=" term ","
    "recurrence" ":=" term :
  tactic

syntax (name := rr_lag_product_factor_sequence_named)
  "rr_lag_product_factor_sequence" " using "
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "factor_realrooted" ":=" term ","
    "recurrence" ":=" term :
  tactic

syntax (name := rr_lag_product_factor_sequence)
  "rr_lag_product_factor_sequence" " using "
    term ", " term ", " term ", " term :
  tactic

syntax (name := rr_lag_product_factor_sequence_inferred_of_recurrence)
  "rr_lag_product_factor_sequence" " using "
    "recurrence" ":=" term :
  tactic

syntax (name := rr_affine_product_sequence_named)
  "rr_affine_product_sequence" " using " "formula" ":=" term :
  tactic

syntax (name := rr_finite_linear_product_scalar_sequence_named)
  "rr_finite_linear_product_scalar_sequence" " using "
    "scalar_ne" ":=" term ","
    "factorization" ":=" term :
  tactic

syntax (name := rr_j1_factorable_lag3_sequence_realrooted_named)
  "rr_j1_factorable_lag3_sequence_realrooted" " using "
    "scalar_ne_zero" ":=" term ","
    "root_grid" ":=" term :
  tactic

syntax (name := rr_product_identity_sequence_named)
  "rr_product_identity_sequence" " using "
    "base" ":=" term ","
    ("cutoff" ":=" term ",")?
    "recurrence" ":=" term :
  tactic

syntax (name := rr_product_identity_sequence)
  "rr_product_identity_sequence" " using " term ", " term :
  tactic

syntax (name := rr_product_root_zero_sequence_named)
  "rr_product_root_zero_sequence" " using "
    "base" ":=" term ","
    ("cutoff" ":=" term ",")?
    "recurrence" ":=" term :
  tactic

syntax (name := rr_product_root_zero_sequence)
  "rr_product_root_zero_sequence" " using " term ", " term :
  tactic

syntax (name := rr_product_period_two_sequence_named)
  "rr_product_period_two_sequence" " using "
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "recurrence" ":=" term :
  tactic

syntax (name := rr_product_period_two_sequence_cutoff_named)
  "rr_product_period_two_sequence" " using "
    "base" ":=" term ","
    "cutoff" ":=" term ","
    "recurrence" ":=" term :
  tactic

syntax (name := rr_product_period_two_sequence)
  "rr_product_period_two_sequence" " using " term ", " term ", " term :
  tactic

syntax (name := rr_product_lift_sequence_named)
  "rr_product_lift_sequence" " using "
    "quotient_realrooted" ":=" term ","
    "factor_realrooted" ":=" term ","
    "factorization" ":=" term :
  tactic

syntax (name := rr_product_lift_sequence_cutoff_named)
  "rr_product_lift_sequence" " using "
    "base" ":=" term ","
    "quotient_realrooted" ":=" term ","
    "factor_realrooted" ":=" term ","
    "cutoff" ":=" term ","
    "factorization" ":=" term :
  tactic

syntax (name := rr_product_lift_sequence)
  "rr_product_lift_sequence" " using " term ", " term ", " term :
  tactic

syntax (name := rr_product_tail_sequence_named)
  "rr_product_tail_sequence" " using "
    "base" ":=" term ","
    "quotient_realrooted" ":=" term ","
    "factor_realrooted" ":=" term ","
    "factorization" ":=" term :
  tactic

syntax (name := rr_product_tail_sequence)
  "rr_product_tail_sequence" " using " term ", " term ", " term ", " term :
  tactic

syntax (name := rr_model_sequence_named)
  "rr_model_sequence" " using "
    "model_realrooted" ":=" term ","
    "identification" ":=" term :
  tactic

syntax (name := rr_scalar_monomial_lift_sequence_named)
  "rr_scalar_monomial_lift_sequence" " using "
    "model_realrooted" ":=" term ","
    "scalar_ne" ":=" term ","
    "factorization" ":=" term :
  tactic

syntax (name := rr_scalar_monomial_tail_sequence_named)
  "rr_scalar_monomial_tail_sequence" " using "
    "base" ":=" term ","
    "model_realrooted" ":=" term ","
    "scalar_ne" ":=" term ","
    "factorization" ":=" term :
  tactic

syntax (name := rr_even_odd_scalar_monomial_lift_sequence_named)
  "rr_even_odd_scalar_monomial_lift_sequence" " using "
    "even_model_realrooted" ":=" term ","
    "odd_model_realrooted" ":=" term ","
    "even_scalar_ne" ":=" term ","
    "odd_scalar_ne" ":=" term ","
    "even_factorization" ":=" term ","
    "odd_factorization" ":=" term :
  tactic

syntax (name := rr_product_lift_sequence_auto_named)
  "rr_product_lift_sequence_auto" " using "
    "quotient_realrooted" ":=" term ","
    "factorization" ":=" term :
  tactic

syntax (name := rr_product_lift_sequence_auto_cutoff_named)
  "rr_product_lift_sequence_auto" " using "
    "base" ":=" term ","
    "quotient_realrooted" ":=" term ","
    "cutoff" ":=" term ","
    "factorization" ":=" term :
  tactic

syntax (name := rr_product_lift_X_sequence_named)
  "rr_product_lift_X_sequence" " using "
    "quotient_realrooted" ":=" term ","
    "factorization" ":=" term :
  tactic

syntax (name := rr_product_lift_X_sequence_cutoff_named)
  "rr_product_lift_X_sequence" " using "
    "base" ":=" term ","
    "quotient_realrooted" ":=" term ","
    "cutoff" ":=" term ","
    "factorization" ":=" term :
  tactic

syntax (name := rr_product_lift_X_add_C_sequence_named)
  "rr_product_lift_X_add_C_sequence" " using "
    "quotient_realrooted" ":=" term ","
    "factorization" ":=" term :
  tactic

syntax (name := rr_product_lift_X_add_C_sequence_cutoff_named)
  "rr_product_lift_X_add_C_sequence" " using "
    "base" ":=" term ","
    "quotient_realrooted" ":=" term ","
    "cutoff" ":=" term ","
    "factorization" ":=" term :
  tactic

syntax (name := rr_product_lift_C_add_X_sequence_named)
  "rr_product_lift_C_add_X_sequence" " using "
    "quotient_realrooted" ":=" term ","
    "factorization" ":=" term :
  tactic

syntax (name := rr_product_lift_C_add_X_sequence_cutoff_named)
  "rr_product_lift_C_add_X_sequence" " using "
    "base" ":=" term ","
    "quotient_realrooted" ":=" term ","
    "cutoff" ":=" term ","
    "factorization" ":=" term :
  tactic

syntax (name := rr_product_lift_C_sequence_named)
  "rr_product_lift_C_sequence" " using "
    "quotient_realrooted" ":=" term ","
    "scalar_ne" ":=" term ","
    "factorization" ":=" term :
  tactic

syntax (name := rr_product_lift_C_sequence_cutoff_named)
  "rr_product_lift_C_sequence" " using "
    "base" ":=" term ","
    "quotient_realrooted" ":=" term ","
    "scalar_ne" ":=" term ","
    "cutoff" ":=" term ","
    "factorization" ":=" term :
  tactic

syntax (name := rr_product_lift_C_sequence_auto_named)
  "rr_product_lift_C_sequence_auto" " using "
    "quotient_realrooted" ":=" term ","
    "factorization" ":=" term :
  tactic

syntax (name := rr_product_lift_C_sequence_auto_cutoff_named)
  "rr_product_lift_C_sequence_auto" " using "
    "base" ":=" term ","
    "quotient_realrooted" ":=" term ","
    "cutoff" ":=" term ","
    "factorization" ":=" term :
  tactic

syntax (name := rr_even_product_odd_X_scalar_sequence_named)
  "rr_even_product_odd_X_scalar_sequence" " using "
    "even_realrooted" ":=" term ","
    "scalar_ne" ":=" term ","
    "even_factorization" ":=" term ","
    "odd_factorization" ":=" term :
  tactic

syntax (name := rr_product_lift_affine_sequence_named)
  "rr_product_lift_affine_sequence" " using "
    "quotient_realrooted" ":=" term ","
    "slope_ne" ":=" term ","
    "factorization" ":=" term :
  tactic

syntax (name := rr_product_lift_affine_sequence_cutoff_named)
  "rr_product_lift_affine_sequence" " using "
    "base" ":=" term ","
    "quotient_realrooted" ":=" term ","
    "slope_ne" ":=" term ","
    "cutoff" ":=" term ","
    "factorization" ":=" term :
  tactic

syntax (name := rr_product_lift_affine_sequence_auto_named)
  "rr_product_lift_affine_sequence_auto" " using "
    "quotient_realrooted" ":=" term ","
    "factorization" ":=" term :
  tactic

syntax (name := rr_product_lift_affine_sequence_auto_cutoff_named)
  "rr_product_lift_affine_sequence_auto" " using "
    "base" ":=" term ","
    "quotient_realrooted" ":=" term ","
    "cutoff" ":=" term ","
    "factorization" ":=" term :
  tactic

syntax (name := rr_product_lift_const_first_sequence_named)
  "rr_product_lift_const_first_sequence" " using "
    "quotient_realrooted" ":=" term ","
    "slope_ne" ":=" term ","
    "factorization" ":=" term :
  tactic

syntax (name := rr_product_lift_const_first_sequence_cutoff_named)
  "rr_product_lift_const_first_sequence" " using "
    "base" ":=" term ","
    "quotient_realrooted" ":=" term ","
    "slope_ne" ":=" term ","
    "cutoff" ":=" term ","
    "factorization" ":=" term :
  tactic

syntax (name := rr_product_lift_const_first_sequence_auto_named)
  "rr_product_lift_const_first_sequence_auto" " using "
    "quotient_realrooted" ":=" term ","
    "factorization" ":=" term :
  tactic

syntax (name := rr_product_lift_const_first_sequence_auto_cutoff_named)
  "rr_product_lift_const_first_sequence_auto" " using "
    "base" ":=" term ","
    "quotient_realrooted" ":=" term ","
    "cutoff" ":=" term ","
    "factorization" ":=" term :
  tactic

syntax (name := rr_product_lift_C_pow_sequence_named)
  "rr_product_lift_C_pow_sequence" " using "
    "quotient_realrooted" ":=" term ","
    "scalar_ne" ":=" term ","
    "factorization" ":=" term :
  tactic

syntax (name := rr_product_lift_C_pow_sequence_cutoff_named)
  "rr_product_lift_C_pow_sequence" " using "
    "base" ":=" term ","
    "quotient_realrooted" ":=" term ","
    "scalar_ne" ":=" term ","
    "cutoff" ":=" term ","
    "factorization" ":=" term :
  tactic

syntax (name := rr_product_lift_C_pow_sequence_auto_named)
  "rr_product_lift_C_pow_sequence_auto" " using "
    "quotient_realrooted" ":=" term ","
    "factorization" ":=" term :
  tactic

syntax (name := rr_product_lift_C_pow_sequence_auto_cutoff_named)
  "rr_product_lift_C_pow_sequence_auto" " using "
    "base" ":=" term ","
    "quotient_realrooted" ":=" term ","
    "cutoff" ":=" term ","
    "factorization" ":=" term :
  tactic

syntax (name := rr_product_lift_checked_scalar_sequence_auto_named)
  "rr_product_lift_checked_scalar_sequence_auto" " using "
    "quotient_realrooted" ":=" term ","
    "factorization" ":=" term :
  tactic

syntax (name := rr_product_lift_checked_scalar_sequence_auto_cutoff_named)
  "rr_product_lift_checked_scalar_sequence_auto" " using "
    "base" ":=" term ","
    "quotient_realrooted" ":=" term ","
    "cutoff" ":=" term ","
    "factorization" ":=" term :
  tactic

syntax (name := rr_product_lift_X_pow_sequence_named)
  "rr_product_lift_X_pow_sequence" " using "
    "quotient_realrooted" ":=" term ","
    "factorization" ":=" term :
  tactic

syntax (name := rr_product_lift_X_pow_sequence_cutoff_named)
  "rr_product_lift_X_pow_sequence" " using "
    "base" ":=" term ","
    "quotient_realrooted" ":=" term ","
    "cutoff" ":=" term ","
    "factorization" ":=" term :
  tactic

syntax (name := rr_product_lift_X_add_C_pow_sequence_named)
  "rr_product_lift_X_add_C_pow_sequence" " using "
    "quotient_realrooted" ":=" term ","
    "factorization" ":=" term :
  tactic

syntax (name := rr_product_lift_X_add_C_pow_sequence_cutoff_named)
  "rr_product_lift_X_add_C_pow_sequence" " using "
    "base" ":=" term ","
    "quotient_realrooted" ":=" term ","
    "cutoff" ":=" term ","
    "factorization" ":=" term :
  tactic

syntax (name := rr_product_lift_X_add_C_row_pow_sequence_named)
  "rr_product_lift_X_add_C_row_pow_sequence" " using "
    "quotient_realrooted" ":=" term ","
    "factorization" ":=" term :
  tactic

syntax (name := rr_product_lift_X_add_C_row_pow_sequence_cutoff_named)
  "rr_product_lift_X_add_C_row_pow_sequence" " using "
    "base" ":=" term ","
    "quotient_realrooted" ":=" term ","
    "cutoff" ":=" term ","
    "factorization" ":=" term :
  tactic

syntax (name := rr_product_lift_C_add_X_pow_sequence_named)
  "rr_product_lift_C_add_X_pow_sequence" " using "
    "quotient_realrooted" ":=" term ","
    "factorization" ":=" term :
  tactic

syntax (name := rr_product_lift_C_add_X_pow_sequence_cutoff_named)
  "rr_product_lift_C_add_X_pow_sequence" " using "
    "base" ":=" term ","
    "quotient_realrooted" ":=" term ","
    "cutoff" ":=" term ","
    "factorization" ":=" term :
  tactic

syntax (name := rr_product_lift_affine_pow_sequence_named)
  "rr_product_lift_affine_pow_sequence" " using "
    "quotient_realrooted" ":=" term ","
    "slope_ne" ":=" term ","
    "factorization" ":=" term :
  tactic

syntax (name := rr_product_lift_affine_pow_sequence_cutoff_named)
  "rr_product_lift_affine_pow_sequence" " using "
    "base" ":=" term ","
    "quotient_realrooted" ":=" term ","
    "slope_ne" ":=" term ","
    "cutoff" ":=" term ","
    "factorization" ":=" term :
  tactic

syntax (name := rr_product_lift_affine_pow_sequence_auto_named)
  "rr_product_lift_affine_pow_sequence_auto" " using "
    "quotient_realrooted" ":=" term ","
    "factorization" ":=" term :
  tactic

syntax (name := rr_product_lift_affine_pow_sequence_auto_cutoff_named)
  "rr_product_lift_affine_pow_sequence_auto" " using "
    "base" ":=" term ","
    "quotient_realrooted" ":=" term ","
    "cutoff" ":=" term ","
    "factorization" ":=" term :
  tactic

syntax (name := rr_product_lift_const_first_affine_pow_sequence_named)
  "rr_product_lift_const_first_affine_pow_sequence" " using "
    "quotient_realrooted" ":=" term ","
    "slope_ne" ":=" term ","
    "factorization" ":=" term :
  tactic

syntax (name := rr_product_lift_const_first_affine_pow_sequence_cutoff_named)
  "rr_product_lift_const_first_affine_pow_sequence" " using "
    "base" ":=" term ","
    "quotient_realrooted" ":=" term ","
    "slope_ne" ":=" term ","
    "cutoff" ":=" term ","
    "factorization" ":=" term :
  tactic

syntax (name := rr_product_lift_const_first_affine_pow_sequence_auto_named)
  "rr_product_lift_const_first_affine_pow_sequence_auto" " using "
    "quotient_realrooted" ":=" term ","
    "factorization" ":=" term :
  tactic

syntax (name := rr_product_lift_const_first_affine_pow_sequence_auto_cutoff_named)
  "rr_product_lift_const_first_affine_pow_sequence_auto" " using "
    "base" ":=" term ","
    "quotient_realrooted" ":=" term ","
    "cutoff" ":=" term ","
    "factorization" ":=" term :
  tactic

syntax (name := rr_product_lift_checked_affine_sequence_auto_named)
  "rr_product_lift_checked_affine_sequence_auto" " using "
    "quotient_realrooted" ":=" term ","
    "factorization" ":=" term :
  tactic

syntax (name := rr_product_lift_checked_affine_sequence_auto_cutoff_named)
  "rr_product_lift_checked_affine_sequence_auto" " using "
    "base" ":=" term ","
    "quotient_realrooted" ":=" term ","
    "cutoff" ":=" term ","
    "factorization" ":=" term :
  tactic

syntax (name := rr_product_lift_checked_affine_pow_sequence_auto_named)
  "rr_product_lift_checked_affine_pow_sequence_auto" " using "
    "quotient_realrooted" ":=" term ","
    "factorization" ":=" term :
  tactic

syntax (name := rr_product_lift_checked_affine_pow_sequence_auto_cutoff_named)
  "rr_product_lift_checked_affine_pow_sequence_auto" " using "
    "base" ":=" term ","
    "quotient_realrooted" ":=" term ","
    "cutoff" ":=" term ","
    "factorization" ":=" term :
  tactic

syntax (name := rr_endpoint_sum_then_X_pair_sequence_named)
  "rr_endpoint_sum_then_X_pair_sequence" " using "
    "base" ":=" term ","
    "left_nonneg" ":=" term ","
    "right_nonneg" ":=" term ","
    "sum_step" ":=" term ","
    "x_step" ":=" term ","
    "coprime" ":=" term :
  tactic

syntax (name := rr_endpoint_sum_then_X_pair_sequence_realrooted_named)
  "rr_endpoint_sum_then_X_pair_sequence_realrooted" " using "
    "base" ":=" term ","
    "left_nonneg" ":=" term ","
    "right_nonneg" ":=" term ","
    "sum_step" ":=" term ","
    "x_step" ":=" term ","
    "coprime" ":=" term :
  tactic

syntax (name := rr_endpoint_X_then_sum_pair_sequence_named)
  "rr_endpoint_X_then_sum_pair_sequence" " using "
    "base" ":=" term ","
    "left_nonneg" ":=" term ","
    "right_nonneg" ":=" term ","
    "x_step" ":=" term ","
    "sum_step" ":=" term ","
    "coprime" ":=" term :
  tactic

syntax (name := rr_endpoint_X_then_sum_pair_sequence_realrooted_named)
  "rr_endpoint_X_then_sum_pair_sequence_realrooted" " using "
    "base" ":=" term ","
    "left_nonneg" ":=" term ","
    "right_nonneg" ":=" term ","
    "x_step" ":=" term ","
    "sum_step" ":=" term ","
    "coprime" ":=" term :
  tactic

syntax (name := rr_endpoint_sum_then_X_pair_lift_sequence_named)
  "rr_endpoint_sum_then_X_pair_lift_sequence" " using "
    "base" ":=" term ","
    "left_nonneg" ":=" term ","
    "right_nonneg" ":=" term ","
    "sum_step" ":=" term ","
    "x_step" ":=" term ","
    "coprime" ":=" term ","
    "even_factorization" ":=" term ","
    "odd_factorization" ":=" term :
  tactic

syntax (name := rr_endpoint_X_then_sum_pair_lift_sequence_named)
  "rr_endpoint_X_then_sum_pair_lift_sequence" " using "
    "base" ":=" term ","
    "left_nonneg" ":=" term ","
    "right_nonneg" ":=" term ","
    "x_step" ":=" term ","
    "sum_step" ":=" term ","
    "coprime" ":=" term ","
    "even_factorization" ":=" term ","
    "odd_factorization" ":=" term :
  tactic

syntax (name := rr_endpoint_X_then_sum_pair_lift_swapped_sequence_named)
  "rr_endpoint_X_then_sum_pair_lift_swapped_sequence" " using "
    "base" ":=" term ","
    "left_nonneg" ":=" term ","
    "right_nonneg" ":=" term ","
    "x_step" ":=" term ","
    "sum_step" ":=" term ","
    "coprime" ":=" term ","
    "even_factorization" ":=" term ","
    "odd_factorization" ":=" term :
  tactic

syntax (name := rr_product_affine_sequence_named)
  "rr_product_affine_sequence" " using "
    "base" ":=" term ","
    "slope_ne" ":=" term ","
    ("cutoff" ":=" term ",")?
    "recurrence" ":=" term :
  tactic

syntax (name := rr_product_affine_sequence_auto_named)
  "rr_product_affine_sequence_auto" " using "
    "base" ":=" term ","
    ("cutoff" ":=" term ",")?
    "recurrence" ":=" term :
  tactic

syntax (name := rr_product_const_first_sequence_named)
  "rr_product_const_first_sequence" " using "
    "base" ":=" term ","
    "slope_ne" ":=" term ","
    ("cutoff" ":=" term ",")?
    "recurrence" ":=" term :
  tactic

syntax (name := rr_product_const_first_sequence_auto_named)
  "rr_product_const_first_sequence_auto" " using "
    "base" ":=" term ","
    ("cutoff" ":=" term ",")?
    "recurrence" ":=" term :
  tactic

syntax (name := rr_product_checked_affine_sequence_auto_named)
  "rr_product_checked_affine_sequence_auto" " using "
    "base" ":=" term ","
    ("cutoff" ":=" term ",")?
    "recurrence" ":=" term :
  tactic

syntax (name := rr_product_X_sequence_named)
  "rr_product_X_sequence" " using "
    "base" ":=" term ","
    ("cutoff" ":=" term ",")?
    "recurrence" ":=" term :
  tactic

syntax (name := rr_product_C_add_X_sequence_named)
  "rr_product_C_add_X_sequence" " using "
    "base" ":=" term ","
    ("cutoff" ":=" term ",")?
    "recurrence" ":=" term :
  tactic

syntax (name := rr_product_C_pow_sequence_named)
  "rr_product_C_pow_sequence" " using "
    "base" ":=" term ","
    "scalar_ne" ":=" term ","
    ("cutoff" ":=" term ",")?
    "recurrence" ":=" term :
  tactic

syntax (name := rr_product_C_pow_sequence_auto_named)
  "rr_product_C_pow_sequence_auto" " using "
    "base" ":=" term ","
    ("cutoff" ":=" term ",")?
    "recurrence" ":=" term :
  tactic

syntax (name := rr_product_X_pow_sequence_named)
  "rr_product_X_pow_sequence" " using "
    "base" ":=" term ","
    ("cutoff" ":=" term ",")?
    "recurrence" ":=" term :
  tactic

syntax (name := rr_product_X_add_C_pow_sequence_named)
  "rr_product_X_add_C_pow_sequence" " using "
    "base" ":=" term ","
    ("cutoff" ":=" term ",")?
    "recurrence" ":=" term :
  tactic

syntax (name := rr_product_C_add_X_pow_sequence_named)
  "rr_product_C_add_X_pow_sequence" " using "
    "base" ":=" term ","
    ("cutoff" ":=" term ",")?
    "recurrence" ":=" term :
  tactic

syntax (name := rr_product_affine_pow_sequence_named)
  "rr_product_affine_pow_sequence" " using "
    "base" ":=" term ","
    "slope_ne" ":=" term ","
    ("cutoff" ":=" term ",")?
    "recurrence" ":=" term :
  tactic

syntax (name := rr_product_affine_pow_sequence_auto_named)
  "rr_product_affine_pow_sequence_auto" " using "
    "base" ":=" term ","
    ("cutoff" ":=" term ",")?
    "recurrence" ":=" term :
  tactic

syntax (name := rr_product_const_first_affine_pow_sequence_named)
  "rr_product_const_first_affine_pow_sequence" " using "
    "base" ":=" term ","
    "slope_ne" ":=" term ","
    ("cutoff" ":=" term ",")?
    "recurrence" ":=" term :
  tactic

syntax (name := rr_product_const_first_affine_pow_sequence_auto_named)
  "rr_product_const_first_affine_pow_sequence_auto" " using "
    "base" ":=" term ","
    ("cutoff" ":=" term ",")?
    "recurrence" ":=" term :
  tactic

syntax (name := rr_product_checked_affine_pow_sequence_auto_named)
  "rr_product_checked_affine_pow_sequence_auto" " using "
    "base" ":=" term ","
    ("cutoff" ":=" term ",")?
    "recurrence" ":=" term :
  tactic

syntax (name := rr_product_checked_scalar_sequence_auto_named)
  "rr_product_checked_scalar_sequence_auto" " using "
    "base" ":=" term ","
    ("cutoff" ":=" term ",")?
    "recurrence" ":=" term :
  tactic

syntax (name := rr_product_scalar_sequence_named)
  "rr_product_scalar_sequence" " using "
    "base" ":=" term ","
    "scalar_ne" ":=" term ","
    ("cutoff" ":=" term ",")?
    "recurrence" ":=" term :
  tactic

syntax (name := rr_product_scalar_sequence_auto_named)
  "rr_product_scalar_sequence_auto" " using "
    "base" ":=" term ","
    ("cutoff" ":=" term ",")?
    "recurrence" ":=" term :
  tactic

syntax (name := rr_product_scalar_linear_sequence_named)
  "rr_product_scalar_linear_sequence" " using "
    "base" ":=" term ","
    "scalar_ne" ":=" term ","
    ("cutoff" ":=" term ",")?
    "scalar_step" ":=" term ","
    "linear_step" ":=" term :
  tactic

syntax (name := rr_product_scalar_linear_sequence_auto_named)
  "rr_product_scalar_linear_sequence_auto" " using "
    "base" ":=" term ","
    ("cutoff" ":=" term ",")?
    "scalar_step" ":=" term ","
    "linear_step" ":=" term :
  tactic

syntax (name := rr_product_scalar_C_add_X_sequence_named)
  "rr_product_scalar_C_add_X_sequence" " using "
    "base" ":=" term ","
    "scalar_ne" ":=" term ","
    ("cutoff" ":=" term ",")?
    "scalar_step" ":=" term ","
    "linear_step" ":=" term :
  tactic

syntax (name := rr_product_scalar_C_add_X_sequence_auto_named)
  "rr_product_scalar_C_add_X_sequence_auto" " using "
    "base" ":=" term ","
    ("cutoff" ":=" term ",")?
    "scalar_step" ":=" term ","
    "linear_step" ":=" term :
  tactic

syntax (name := rr_product_scalar_factor_sequence_named)
  "rr_product_scalar_factor_sequence" " using "
    "base" ":=" term ","
    "scalar_ne" ":=" term ","
    "factor_realrooted" ":=" term ","
    ("cutoff" ":=" term ",")?
    "scalar_step" ":=" term ","
    "factor_step" ":=" term :
  tactic

syntax (name := rr_product_scalar_factor_sequence_auto_named)
  "rr_product_scalar_factor_sequence_auto" " using "
    "base" ":=" term ","
    "factor_realrooted" ":=" term ","
    ("cutoff" ":=" term ",")?
    "scalar_step" ":=" term ","
    "factor_step" ":=" term :
  tactic

syntax (name := rr_product_scalar_X_pow_sequence_named)
  "rr_product_scalar_X_pow_sequence" " using "
    "base" ":=" term ","
    "scalar_ne" ":=" term ","
    ("cutoff" ":=" term ",")?
    "scalar_step" ":=" term ","
    "factor_step" ":=" term :
  tactic

syntax (name := rr_product_scalar_X_pow_sequence_auto_named)
  "rr_product_scalar_X_pow_sequence_auto" " using "
    "base" ":=" term ","
    ("cutoff" ":=" term ",")?
    "scalar_step" ":=" term ","
    "factor_step" ":=" term :
  tactic

syntax (name := rr_product_scalar_X_add_C_pow_sequence_named)
  "rr_product_scalar_X_add_C_pow_sequence" " using "
    "base" ":=" term ","
    "scalar_ne" ":=" term ","
    ("cutoff" ":=" term ",")?
    "scalar_step" ":=" term ","
    "factor_step" ":=" term :
  tactic

syntax (name := rr_product_scalar_X_add_C_pow_sequence_auto_named)
  "rr_product_scalar_X_add_C_pow_sequence_auto" " using "
    "base" ":=" term ","
    ("cutoff" ":=" term ",")?
    "scalar_step" ":=" term ","
    "factor_step" ":=" term :
  tactic

syntax (name := rr_product_scalar_C_add_X_pow_sequence_named)
  "rr_product_scalar_C_add_X_pow_sequence" " using "
    "base" ":=" term ","
    "scalar_ne" ":=" term ","
    ("cutoff" ":=" term ",")?
    "scalar_step" ":=" term ","
    "factor_step" ":=" term :
  tactic

syntax (name := rr_product_scalar_C_add_X_pow_sequence_auto_named)
  "rr_product_scalar_C_add_X_pow_sequence_auto" " using "
    "base" ":=" term ","
    ("cutoff" ":=" term ",")?
    "scalar_step" ":=" term ","
    "factor_step" ":=" term :
  tactic

syntax (name := rr_product_nonzero) "rr_product_nonzero" : tactic

syntax (name := rr_product_normalize)
  "rr_product_normalize" " using " term :
  tactic

syntax (name := rr_product_nonzero_term) "rr_product_nonzero_term" : term

syntax (name := rr_product_nonzero_seq) "rr_product_nonzero_seq" : term

syntax (name := rr_product_nonzero_seq_from) "rr_product_nonzero_seq_from" : term

syntax (name := rr_product_two_variants)
  "rr_product_two_variants" term ", " term :
  tactic

syntax (name := rr_product_two_sequence_variants)
  "rr_product_two_sequence_variants" term ", " term :
  tactic

syntax (name := rr_product_four_sequence_variants)
  "rr_product_four_sequence_variants" term ", " term ", " term ", " term :
  tactic

private inductive AffinePowOrientation where
  | mulXFirst
  | constFirst

private inductive ScalarFactorKind where
  | scalar
  | scalarPow

private def appFnName? (e : Expr) : Option Name :=
  e.consumeMData.getAppFn.constName?

private partial def containsAppFn (needle : Name) (e : Expr) : Bool :=
  let e := e.consumeMData
  appFnName? e == some needle ||
    e.getAppArgs.any (containsAppFn needle) ||
    match e with
    | .forallE _ domain body _ => containsAppFn needle domain || containsAppFn needle body
    | .lam _ domain body _ => containsAppFn needle domain || containsAppFn needle body
    | .letE _ type value body _ =>
        containsAppFn needle type || containsAppFn needle value || containsAppFn needle body
    | .proj _ _ body => containsAppFn needle body
    | _ => false

private def isPolynomialX (e : Expr) : Bool :=
  appFnName? e == some ``Polynomial.X

private def containsPolynomialX (e : Expr) : Bool :=
  containsAppFn ``Polynomial.X e

private def isScalarPolynomialExpr (e : Expr) : Bool :=
  containsAppFn ``Polynomial.C e && !containsPolynomialX e

private def scalarFactorKind? (e : Expr) : Option ScalarFactorKind :=
  let e := e.consumeMData
  if appFnName? e == some ``HPow.hPow then
    let args := e.getAppArgs
    if args.size > 5 && isScalarPolynomialExpr args[4]! then
      some .scalarPow
    else
      none
  else if isScalarPolynomialExpr e then
    some .scalar
  else
    none

private partial def topMulFactors (e : Expr) : List Expr :=
  let e := e.consumeMData
  if appFnName? e == some ``HMul.hMul then
    let args := e.getAppArgs
    if args.size > 5 then
      topMulFactors args[4]! ++ topMulFactors args[5]!
    else
      [e]
  else
    [e]

private def scalarKindOfTopProduct? (rhs : Expr) : Option ScalarFactorKind :=
  match topMulFactors rhs with
  | lhsFactor :: rhsFactor :: [] =>
      match scalarFactorKind? lhsFactor, scalarFactorKind? rhsFactor with
      | some kind, none => some kind
      | none, some kind => some kind
      | _, _ => none
  | _ => none

private partial def findScalarTopProductKind? (e : Expr) :
    Option ScalarFactorKind := Id.run do
  let e := e.consumeMData
  if appFnName? e == some ``Eq then
    let args := e.getAppArgs
    if args.size > 0 then
      if let some kind := scalarKindOfTopProduct? args[args.size - 1]! then
        return some kind
  match e with
  | .forallE _ _ body _ => findScalarTopProductKind? body
  | .lam _ _ body _ => findScalarTopProductKind? body
  | .letE _ _ value body _ =>
      if let some kind := findScalarTopProductKind? value then
        return some kind
      findScalarTopProductKind? body
  | .proj _ _ body => findScalarTopProductKind? body
  | _ => none

private def isPolynomialCMulX (e : Expr) : Bool :=
  let e := e.consumeMData
  appFnName? e == some ``HMul.hMul &&
    let args := e.getAppArgs
    args.size > 5 &&
      containsAppFn ``Polynomial.C args[4]! &&
      isPolynomialX args[5]!

private def affineOrientationOfBase? (e : Expr) : Option AffinePowOrientation :=
  let e := e.consumeMData
  if appFnName? e == some ``HAdd.hAdd then
    let args := e.getAppArgs
    if args.size > 5 then
      if isPolynomialCMulX args[4]! then
        some .mulXFirst
      else if isPolynomialCMulX args[5]! then
        some .constFirst
      else
        none
    else
      none
  else
    none

private partial def findAffinePowOrientation? (e : Expr) :
    Option AffinePowOrientation := Id.run do
  let e := e.consumeMData
  if appFnName? e == some ``HPow.hPow then
    let args := e.getAppArgs
    if args.size > 5 then
      if let some orientation := affineOrientationOfBase? args[4]! then
        return some orientation
  for arg in e.getAppArgs do
    if let some orientation := findAffinePowOrientation? arg then
      return some orientation
  match e with
  | .forallE _ domain body _ =>
      if let some orientation := findAffinePowOrientation? domain then
        return some orientation
      findAffinePowOrientation? body
  | .lam _ domain body _ =>
      if let some orientation := findAffinePowOrientation? domain then
        return some orientation
      findAffinePowOrientation? body
  | .letE _ type value body _ =>
      if let some orientation := findAffinePowOrientation? type then
        return some orientation
      if let some orientation := findAffinePowOrientation? value then
        return some orientation
      findAffinePowOrientation? body
  | .proj _ _ body => findAffinePowOrientation? body
  | _ => none

private partial def findAffineLinearOrientation? (e : Expr) :
    Option AffinePowOrientation := Id.run do
  let e := e.consumeMData
  if appFnName? e == some ``HPow.hPow then
    return none
  if let some orientation := affineOrientationOfBase? e then
    return some orientation
  for arg in e.getAppArgs do
    if let some orientation := findAffineLinearOrientation? arg then
      return some orientation
  match e with
  | .forallE _ domain body _ =>
      if let some orientation := findAffineLinearOrientation? domain then
        return some orientation
      findAffineLinearOrientation? body
  | .lam _ domain body _ =>
      if let some orientation := findAffineLinearOrientation? domain then
        return some orientation
      findAffineLinearOrientation? body
  | .letE _ type value body _ =>
      if let some orientation := findAffineLinearOrientation? type then
        return some orientation
      if let some orientation := findAffineLinearOrientation? value then
        return some orientation
      findAffineLinearOrientation? body
  | .proj _ _ body => findAffineLinearOrientation? body
  | _ => none

private def affineLinearOrientationOfEvidence (label : String) (evidence : Syntax) :
    TacticM AffinePowOrientation := withMainContext do
  let evidenceExpr ← Lean.Elab.Tactic.elabTerm evidence none
  let evidenceType ← instantiateMVars (← inferType evidenceExpr)
  match findAffineLinearOrientation? evidenceType with
  | some orientation => pure orientation
  | none =>
      throwError
        "rr_product checked affine auto: no affine factor found in {label}"

private def affinePowOrientationOfEvidence (label : String) (evidence : Syntax) :
    TacticM AffinePowOrientation := withMainContext do
  let evidenceExpr ← Lean.Elab.Tactic.elabTerm evidence none
  let evidenceType ← instantiateMVars (← inferType evidenceExpr)
  match findAffinePowOrientation? evidenceType with
  | some orientation => pure orientation
  | none =>
      throwError
        "rr_product checked affine-power auto: no affine-power factor found in {label}"

private def scalarKindOfEvidence (label : String) (evidence : Syntax) :
    TacticM ScalarFactorKind := withMainContext do
  let evidenceExpr ← Lean.Elab.Tactic.elabTerm evidence none
  let evidenceType ← instantiateMVars (← inferType evidenceExpr)
  match findScalarTopProductKind? evidenceType with
  | some kind => pure kind
  | none =>
      throwError "rr_product checked scalar auto: no scalar factor found in {label}"

elab "rr_product_lift_checked_affine_sequence_auto" " using "
    "quotient_realrooted" ":=" hquot:term ","
    "factorization" ":=" hrow:term : tactic => do
  match ← affineLinearOrientationOfEvidence "factorization" hrow with
  | .mulXFirst =>
      evalTactic
        (← `(tactic|
          rr_product_lift_affine_sequence_auto using
            quotient_realrooted := $hquot,
            factorization := $hrow))
  | .constFirst =>
      evalTactic
        (← `(tactic|
          rr_product_lift_const_first_sequence_auto using
            quotient_realrooted := $hquot,
            factorization := $hrow))

elab "rr_product_lift_checked_affine_sequence_auto" " using "
    "base" ":=" hbase:term ","
    "quotient_realrooted" ":=" hquot:term ","
    "cutoff" ":=" N:term ","
    "factorization" ":=" hrow:term : tactic => do
  match ← affineLinearOrientationOfEvidence "factorization" hrow with
  | .mulXFirst =>
      evalTactic
        (← `(tactic|
          rr_product_lift_affine_sequence_auto using
            base := $hbase,
            quotient_realrooted := $hquot,
            cutoff := $N,
            factorization := $hrow))
  | .constFirst =>
      evalTactic
        (← `(tactic|
          rr_product_lift_const_first_sequence_auto using
            base := $hbase,
            quotient_realrooted := $hquot,
            cutoff := $N,
            factorization := $hrow))

elab "rr_product_lift_checked_affine_pow_sequence_auto" " using "
    "quotient_realrooted" ":=" hquot:term ","
    "factorization" ":=" hrow:term : tactic => do
  match ← affinePowOrientationOfEvidence "factorization" hrow with
  | .mulXFirst =>
      evalTactic
        (← `(tactic|
          rr_product_lift_affine_pow_sequence_auto using
            quotient_realrooted := $hquot,
            factorization := $hrow))
  | .constFirst =>
      evalTactic
        (← `(tactic|
          rr_product_lift_const_first_affine_pow_sequence_auto using
            quotient_realrooted := $hquot,
            factorization := $hrow))

elab "rr_product_lift_checked_affine_pow_sequence_auto" " using "
    "base" ":=" hbase:term ","
    "quotient_realrooted" ":=" hquot:term ","
    "cutoff" ":=" N:term ","
    "factorization" ":=" hrow:term : tactic => do
  match ← affinePowOrientationOfEvidence "factorization" hrow with
  | .mulXFirst =>
      evalTactic
        (← `(tactic|
          rr_product_lift_affine_pow_sequence_auto using
            base := $hbase,
            quotient_realrooted := $hquot,
            cutoff := $N,
            factorization := $hrow))
  | .constFirst =>
      evalTactic
        (← `(tactic|
          rr_product_lift_const_first_affine_pow_sequence_auto using
            base := $hbase,
            quotient_realrooted := $hquot,
            cutoff := $N,
            factorization := $hrow))

elab "rr_product_lift_checked_scalar_sequence_auto" " using "
    "quotient_realrooted" ":=" hquot:term ","
    "factorization" ":=" hrow:term : tactic => do
  match ← scalarKindOfEvidence "factorization" hrow with
  | .scalar =>
      evalTactic
        (← `(tactic|
          rr_product_lift_C_sequence_auto using
            quotient_realrooted := $hquot,
            factorization := $hrow))
  | .scalarPow =>
      evalTactic
        (← `(tactic|
          rr_product_lift_C_pow_sequence_auto using
            quotient_realrooted := $hquot,
            factorization := $hrow))

elab "rr_product_lift_checked_scalar_sequence_auto" " using "
    "base" ":=" hbase:term ","
    "quotient_realrooted" ":=" hquot:term ","
    "cutoff" ":=" N:term ","
    "factorization" ":=" hrow:term : tactic => do
  match ← scalarKindOfEvidence "factorization" hrow with
  | .scalar =>
      evalTactic
        (← `(tactic|
          rr_product_lift_C_sequence_auto using
            base := $hbase,
            quotient_realrooted := $hquot,
            cutoff := $N,
            factorization := $hrow))
  | .scalarPow =>
      evalTactic
        (← `(tactic|
          rr_product_lift_C_pow_sequence_auto using
            base := $hbase,
            quotient_realrooted := $hquot,
            cutoff := $N,
            factorization := $hrow))

elab "rr_product_checked_affine_sequence_auto" " using "
    "base" ":=" hbase:term ","
    "recurrence" ":=" hrec:term : tactic => do
  match ← affineLinearOrientationOfEvidence "recurrence" hrec with
  | .mulXFirst =>
      evalTactic
        (← `(tactic|
          rr_product_affine_sequence_auto using
            base := $hbase,
            recurrence := $hrec))
  | .constFirst =>
      evalTactic
        (← `(tactic|
          rr_product_const_first_sequence_auto using
            base := $hbase,
            recurrence := $hrec))

elab "rr_product_checked_affine_sequence_auto" " using "
    "base" ":=" hbase:term ","
    "cutoff" ":=" N:term ","
    "recurrence" ":=" hrec:term : tactic => do
  match ← affineLinearOrientationOfEvidence "recurrence" hrec with
  | .mulXFirst =>
      evalTactic
        (← `(tactic|
          rr_product_affine_sequence_auto using
            base := $hbase,
            cutoff := $N,
            recurrence := $hrec))
  | .constFirst =>
      evalTactic
        (← `(tactic|
          rr_product_const_first_sequence_auto using
            base := $hbase,
            cutoff := $N,
            recurrence := $hrec))

elab "rr_product_checked_scalar_sequence_auto" " using "
    "base" ":=" hbase:term ","
    "recurrence" ":=" hrec:term : tactic => do
  match ← scalarKindOfEvidence "recurrence" hrec with
  | .scalar =>
      evalTactic
        (← `(tactic|
          rr_product_scalar_sequence_auto using
            base := $hbase,
            recurrence := $hrec))
  | .scalarPow =>
      evalTactic
        (← `(tactic|
          rr_product_C_pow_sequence_auto using
            base := $hbase,
            recurrence := $hrec))

elab "rr_product_checked_scalar_sequence_auto" " using "
    "base" ":=" hbase:term ","
    "cutoff" ":=" N:term ","
    "recurrence" ":=" hrec:term : tactic => do
  match ← scalarKindOfEvidence "recurrence" hrec with
  | .scalar =>
      evalTactic
        (← `(tactic|
          rr_product_scalar_sequence_auto using
            base := $hbase,
            cutoff := $N,
            recurrence := $hrec))
  | .scalarPow =>
      evalTactic
        (← `(tactic|
          rr_product_C_pow_sequence_auto using
            base := $hbase,
            cutoff := $N,
            recurrence := $hrec))

elab "rr_product_checked_affine_pow_sequence_auto" " using "
    "base" ":=" hbase:term ","
    "recurrence" ":=" hrec:term : tactic => do
  match ← affinePowOrientationOfEvidence "recurrence" hrec with
  | .mulXFirst =>
      evalTactic
        (← `(tactic|
          rr_product_affine_pow_sequence_auto using
            base := $hbase,
            recurrence := $hrec))
  | .constFirst =>
      evalTactic
        (← `(tactic|
          rr_product_const_first_affine_pow_sequence_auto using
            base := $hbase,
            recurrence := $hrec))

elab "rr_product_checked_affine_pow_sequence_auto" " using "
    "base" ":=" hbase:term ","
    "cutoff" ":=" N:term ","
    "recurrence" ":=" hrec:term : tactic => do
  match ← affinePowOrientationOfEvidence "recurrence" hrec with
  | .mulXFirst =>
      evalTactic
        (← `(tactic|
          rr_product_affine_pow_sequence_auto using
            base := $hbase,
            cutoff := $N,
            recurrence := $hrec))
  | .constFirst =>
      evalTactic
        (← `(tactic|
          rr_product_const_first_affine_pow_sequence_auto using
            base := $hbase,
            cutoff := $N,
            recurrence := $hrec))

macro_rules
  | `(tactic| rr_product_nonzero) =>
      `(tactic| rr_side_ne)
  | `(tactic| rr_product_normalize using $h:term) =>
      `(tactic|
        have hcert := ($h);
        first
          | exact hcert
          | convert hcert using 2 <;> norm_num <;> ring)
  | `(rr_product_nonzero_term) =>
      `(by rr_product_nonzero)
  | `(rr_product_nonzero_seq) =>
      `(fun n => by rr_product_nonzero)
  | `(rr_product_nonzero_seq_from) =>
      `(fun n _ => by rr_product_nonzero)
  | `(tactic| rr_product_two_variants $hleft:term, $hright:term) =>
      `(tactic|
        rr_first_realrooted_or_projection $hleft, $hright)
  | `(tactic| rr_product_two_sequence_variants $hleft:term, $hright:term) =>
      `(tactic|
        rr_first_realrooted_sequence_or_projection $hleft, $hright)
  | `(tactic|
      rr_product_four_sequence_variants
        $hleft:term, $hright:term, $hscalar_right:term, $hfactor_right:term) =>
      `(tactic|
        rr_first_realrooted_sequence_or_projection
          $hleft, $hright, $hscalar_right, $hfactor_right)

macro_rules
  | `(tactic| rr_product_C using scalar_ne := $ha:term) =>
      `(tactic|
        rr_first_realrooted_or_projection (RealRooted.isRealRooted_C $ha))
  | `(tactic| rr_product_C_auto) =>
      `(tactic|
        rr_product_C using scalar_ne := rr_product_nonzero_term)
  | `(tactic|
      rr_product_C_pow using
        scalar_ne := $ha:term,
        exponent := $n:term) =>
      `(tactic|
        rr_first_realrooted_or_projection (RealRooted.isRealRooted_C_pow $ha $n))
  | `(tactic| rr_product_C_pow_auto using exponent := $n:term) =>
      `(tactic|
        rr_product_C_pow using
          scalar_ne := rr_product_nonzero_term,
          exponent := $n)
  | `(tactic| rr_product_X) =>
      `(tactic|
        rr_first_realrooted_or_projection RealRooted.isRealRooted_X)
  | `(tactic| rr_product_X_pow using exponent := $n:term) =>
      `(tactic|
        rr_first_realrooted_or_projection (RealRooted.isRealRooted_X_pow $n))
  | `(tactic| rr_product_X_add_C using constant := $t:term) =>
      `(tactic|
        rr_first_realrooted_or_projection (RealRooted.isRealRooted_X_add_C $t))
  | `(tactic|
      rr_product_X_add_C_pow using
        constant := $t:term,
        exponent := $n:term) =>
      `(tactic|
        rr_first_realrooted_or_projection (RealRooted.isRealRooted_X_add_C_pow $t $n))
  | `(tactic| rr_product_C_add_X using constant := $t:term) =>
      `(tactic|
        rr_first_realrooted_or_projection (RealRooted.isRealRooted_C_add_X $t))
  | `(tactic|
      rr_product_C_add_X_pow using
        constant := $t:term,
        exponent := $n:term) =>
      `(tactic|
        rr_first_realrooted_or_projection (RealRooted.isRealRooted_C_add_X_pow $t $n))
  | `(tactic| rr_product_affine using slope_ne := $hs:term) =>
      `(tactic|
        rr_first_realrooted_or_projection
          (RealRooted.isRealRooted_C_mul_X_add_C $hs))
  | `(tactic| rr_product_affine_auto) =>
      `(tactic|
        rr_product_affine using slope_ne := rr_product_nonzero_term)
  | `(tactic|
      rr_product_affine_pow using
        slope_ne := $hs:term,
        exponent := $n:term) =>
      `(tactic|
        rr_first_realrooted_or_projection
          (RealRooted.isRealRooted_C_mul_X_add_C_pow $hs $n))
  | `(tactic| rr_product_affine_pow_auto using exponent := $n:term) =>
      `(tactic|
        rr_product_affine_pow using
          slope_ne := rr_product_nonzero_term,
          exponent := $n)
  | `(tactic| rr_product_const_first_affine using slope_ne := $hs:term) =>
      `(tactic|
        rr_first_realrooted_or_projection
          (RealRooted.isRealRooted_C_add_C_mul_X $hs))
  | `(tactic| rr_product_const_first_affine_auto) =>
      `(tactic|
        rr_product_const_first_affine using slope_ne := rr_product_nonzero_term)
  | `(tactic|
      rr_product_const_first_affine_pow using
        slope_ne := $hs:term,
        exponent := $n:term) =>
      `(tactic|
        rr_first_realrooted_or_projection
          (RealRooted.isRealRooted_C_add_C_mul_X_pow $hs $n))
  | `(tactic| rr_product_const_first_affine_pow_auto using exponent := $n:term) =>
      `(tactic|
        rr_product_const_first_affine_pow using
          slope_ne := rr_product_nonzero_term,
          exponent := $n)
  | `(tactic| rr_product_factor using $hp:term, $hs:term) =>
      `(tactic|
        rr_product_two_variants
          (RealRooted.isRealRooted_C_mul_X_add_C_mul $hp $hs),
          (RealRooted.isRealRooted_mul_C_mul_X_add_C $hp $hs))
  | `(tactic|
      rr_product_factor using
        realrooted := $hp:term,
        slope_ne := $hs:term) =>
      `(tactic|
        rr_product_factor using $hp, $hs)
  | `(tactic| rr_product_factor_auto using $hp:term) =>
      `(tactic|
        rr_product_factor using $hp, rr_product_nonzero_term)
  | `(tactic|
      rr_product_factor_auto using
        realrooted := $hp:term) =>
      `(tactic|
        rr_product_factor_auto using $hp)
  | `(tactic| rr_product_factor_const_first using $hp:term, $hs:term) =>
      `(tactic|
        rr_product_two_variants
          (RealRooted.isRealRooted_C_add_C_mul_X_mul $hp $hs),
          (RealRooted.isRealRooted_mul_C_add_C_mul_X $hp $hs))
  | `(tactic|
      rr_product_factor_const_first using
        realrooted := $hp:term,
        slope_ne := $hs:term) =>
      `(tactic|
        rr_product_factor_const_first using $hp, $hs)
  | `(tactic| rr_product_factor_const_first_auto using $hp:term) =>
      `(tactic|
        rr_product_factor_const_first using $hp, rr_product_nonzero_term)
  | `(tactic|
      rr_product_factor_const_first_auto using
        realrooted := $hp:term) =>
      `(tactic|
        rr_product_factor_const_first_auto using $hp)
  | `(tactic| rr_product_factor_X using $hp:term) =>
      `(tactic|
        rr_product_two_variants
          (RealRooted.isRealRooted_X_add_C_mul $hp),
          (RealRooted.isRealRooted_mul_X_add_C $hp))
  | `(tactic|
      rr_product_factor_X using
        realrooted := $hp:term) =>
      `(tactic|
        rr_product_factor_X using $hp)
  | `(tactic| rr_product_factor_C_add_X using $hp:term) =>
      `(tactic|
        rr_product_two_variants
          (RealRooted.isRealRooted_C_add_X_mul $hp),
          (RealRooted.isRealRooted_mul_C_add_X $hp))
  | `(tactic|
      rr_product_factor_C_add_X using
        realrooted := $hp:term) =>
      `(tactic|
        rr_product_factor_C_add_X using $hp)
  | `(tactic|
      rr_product_factor_sequence using
        base := $hbase:term,
        factor_realrooted := $hfactor:term,
        recurrence := $hstep:term) =>
      `(tactic|
        rr_product_two_sequence_variants
          (RealRooted.isRealRooted_of_product_factor_sequence
            $hbase $hfactor $hstep),
          (RealRooted.isRealRooted_of_product_factor_right_sequence
            $hbase $hfactor $hstep))
  | `(tactic|
      rr_product_factor_sequence using
        base := $hbase:term,
        factor_realrooted := $hfactor:term,
        cutoff := $N:term,
        recurrence := $hstep:term) =>
      `(tactic|
        rr_product_two_sequence_variants
          (RealRooted.isRealRooted_of_product_factor_sequence_from
            $N $hbase $hfactor $hstep),
          (RealRooted.isRealRooted_of_product_factor_right_sequence_from
            $N $hbase $hfactor $hstep))
  | `(tactic|
      rr_product_factor_sequence using
        $hbase:term, $hfactor:term, $hstep:term) =>
      `(tactic|
        rr_product_factor_sequence using
          base := $hbase,
          factor_realrooted := $hfactor,
          recurrence := $hstep)
  | `(tactic|
      rr_product_factor_sequence using
        recurrence := $hstep:term) =>
      `(tactic|
        first
          | rr_product_factor_sequence using cutoff := _, recurrence := $hstep
          | rr_first_realrooted_sequence_or_projection
              (by
                rr_refine_then
                  (RealRooted.isRealRooted_of_product_factor_sequence
                    ?_ ?_ $hstep)
                  with rr_lookup),
              (by
                rr_refine_then
                  (RealRooted.isRealRooted_of_product_factor_right_sequence
                    ?_ ?_ $hstep)
                  with rr_lookup))
  | `(tactic|
      rr_product_factor_sequence using
        cutoff := $N:term,
        recurrence := $hstep:term) =>
      `(tactic|
        rr_first_realrooted_sequence_or_projection
          (by
            rr_refine_then
              (RealRooted.isRealRooted_of_product_factor_sequence_from
                $N ?_ ?_ $hstep)
              with rr_lookup),
          (by
            rr_refine_then
              (RealRooted.isRealRooted_of_product_factor_right_sequence_from
                $N ?_ ?_ $hstep)
              with rr_lookup))
  | `(tactic|
      rr_lag_product_factor_sequence using
        base_zero := $hbase_zero:term,
        base_one := $hbase_one:term,
        factor_realrooted := $hfactor:term,
        recurrence := $hstep:term) =>
      `(tactic|
        rr_product_two_sequence_variants
          (RealRooted.isRealRooted_of_lag_product_factor_sequence
            $hbase_zero $hbase_one $hfactor $hstep),
          (RealRooted.isRealRooted_of_lag_product_factor_right_sequence
            $hbase_zero $hbase_one $hfactor $hstep))
  | `(tactic|
      rr_lag_product_factor_sequence using
        $hbase_zero:term, $hbase_one:term, $hfactor:term, $hstep:term) =>
      `(tactic|
        rr_lag_product_factor_sequence using
          base_zero := $hbase_zero,
          base_one := $hbase_one,
          factor_realrooted := $hfactor,
          recurrence := $hstep)
  | `(tactic|
      rr_lag_product_factor_sequence using
        recurrence := $hstep:term) =>
      `(tactic|
        rr_first_realrooted_sequence_or_projection
          (by
            rr_refine_then
              (RealRooted.isRealRooted_of_lag_product_factor_sequence
                ?_ ?_ ?_ $hstep)
              with rr_lookup),
          (by
            rr_refine_then
              (RealRooted.isRealRooted_of_lag_product_factor_right_sequence
                ?_ ?_ ?_ $hstep)
              with rr_lookup))
  | `(tactic| rr_affine_product_sequence using formula := $hroot:term) =>
      `(tactic|
        exact RealRooted.finiteLinearProductSequence_realRooted $hroot)
  | `(tactic|
      rr_finite_linear_product_scalar_sequence using
        scalar_ne := $hc:term,
        factorization := $hroot:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.finiteLinearProductScalarSequence_realRooted $hc $hroot))
  | `(tactic|
      rr_j1_factorable_lag3_sequence_realrooted using
        scalar_ne_zero := $hc:term,
        root_grid := $hroot:term) =>
      `(tactic|
        rr_finite_linear_product_scalar_sequence using
          scalar_ne := $hc,
          factorization := $hroot)
  | `(tactic|
      rr_product_identity_sequence using
        base := $hbase:term,
        recurrence := $hstep:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_product_identity_sequence $hbase $hstep))
  | `(tactic|
      rr_product_identity_sequence using
        base := $hbase:term,
        cutoff := $N:term,
        recurrence := $hstep:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_product_identity_sequence_from
            $N $hbase $hstep))
  | `(tactic|
      rr_product_identity_sequence using
        $hbase:term, $hstep:term) =>
      `(tactic|
        rr_product_identity_sequence using
          base := $hbase,
          recurrence := $hstep)
  | `(tactic|
      rr_product_root_zero_sequence using
        base := $hbase:term,
        recurrence := $hstep:term) =>
      `(tactic|
        rr_product_two_sequence_variants
          (RealRooted.isRealRooted_of_product_root_zero_sequence $hbase $hstep),
          (RealRooted.isRealRooted_of_product_root_zero_right_sequence
            $hbase $hstep))
  | `(tactic|
      rr_product_root_zero_sequence using
        base := $hbase:term,
        cutoff := $N:term,
        recurrence := $hstep:term) =>
      `(tactic|
        rr_product_two_sequence_variants
          (RealRooted.isRealRooted_of_product_root_zero_sequence_from
            $N $hbase $hstep),
          (RealRooted.isRealRooted_of_product_root_zero_right_sequence_from
            $N $hbase $hstep))
  | `(tactic|
      rr_product_root_zero_sequence using
        $hbase:term, $hstep:term) =>
      `(tactic|
        rr_product_root_zero_sequence using
          base := $hbase,
          recurrence := $hstep)
  | `(tactic|
      rr_product_period_two_sequence using
        base_zero := $hbase_zero:term,
        base_one := $hbase_one:term,
        recurrence := $hstep:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_product_period_two_sequence
            $hbase_zero $hbase_one $hstep))
  | `(tactic|
      rr_product_period_two_sequence using
        base := $hbase:term,
        cutoff := $N:term,
        recurrence := $hstep:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_product_period_two_sequence_from
            $N $hbase $hstep))
  | `(tactic|
      rr_product_period_two_sequence using
        $hbase_zero:term, $hbase_one:term, $hstep:term) =>
      `(tactic|
        rr_product_period_two_sequence using
          base_zero := $hbase_zero,
          base_one := $hbase_one,
          recurrence := $hstep)
  | `(tactic|
      rr_product_lift_sequence using
        quotient_realrooted := $hquot:term,
        factor_realrooted := $hfactor:term,
        factorization := $hrow:term) =>
      `(tactic|
        rr_product_two_sequence_variants
          (RealRooted.isRealRooted_of_product_lift_sequence
            $hquot $hfactor $hrow),
          (RealRooted.isRealRooted_of_product_lift_right_sequence
            $hquot $hfactor $hrow))
  | `(tactic|
      rr_product_lift_sequence using
        base := $hbase:term,
        quotient_realrooted := $hquot:term,
        factor_realrooted := $hfactor:term,
        cutoff := $N:term,
        factorization := $hrow:term) =>
      `(tactic|
        rr_product_two_sequence_variants
          (RealRooted.isRealRooted_of_product_lift_sequence_from
            $N $hbase $hquot $hfactor $hrow),
          (RealRooted.isRealRooted_of_product_lift_right_sequence_from
            $N $hbase $hquot $hfactor $hrow))
  | `(tactic|
      rr_product_lift_sequence using
        $hquot:term, $hfactor:term, $hrow:term) =>
      `(tactic|
        rr_product_lift_sequence using
          quotient_realrooted := $hquot,
          factor_realrooted := $hfactor,
          factorization := $hrow)
  | `(tactic|
      rr_product_tail_sequence using
        base := $hbase:term,
        quotient_realrooted := $hquot:term,
        factor_realrooted := $hfactor:term,
        factorization := $hrow:term) =>
      `(tactic|
        rr_product_two_sequence_variants
          (RealRooted.isRealRooted_of_product_tail_sequence
            $hbase $hquot $hfactor $hrow),
          (RealRooted.isRealRooted_of_product_tail_right_sequence
            $hbase $hquot $hfactor $hrow))
  | `(tactic|
      rr_product_tail_sequence using
        $hbase:term, $hquot:term, $hfactor:term, $hrow:term) =>
      `(tactic|
        rr_product_tail_sequence using
          base := $hbase,
          quotient_realrooted := $hquot,
          factor_realrooted := $hfactor,
          factorization := $hrow)
  | `(tactic|
      rr_model_sequence using
        model_realrooted := $hmodel:term,
        identification := $hidentify:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_model_sequence $hmodel $hidentify))
  | `(tactic|
      rr_scalar_monomial_lift_sequence using
        model_realrooted := $hmodel:term,
        scalar_ne := $hc:term,
        factorization := $hrow:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_scalar_monomial_lift_sequence
            $hmodel $hc $hrow))
  | `(tactic|
      rr_scalar_monomial_tail_sequence using
        base := $hbase:term,
        model_realrooted := $hmodel:term,
        scalar_ne := $hc:term,
        factorization := $hrow:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_scalar_monomial_tail_sequence
            $hbase $hmodel $hc $hrow))
  | `(tactic|
      rr_even_odd_scalar_monomial_lift_sequence using
        even_model_realrooted := $heven_model:term,
        odd_model_realrooted := $hodd_model:term,
        even_scalar_ne := $hceven:term,
        odd_scalar_ne := $hcodd:term,
        even_factorization := $heven:term,
        odd_factorization := $hodd:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_even_odd_scalar_monomial_lift_sequence
            $heven_model $hodd_model $hceven $hcodd $heven $hodd))
  | `(tactic|
      rr_product_lift_sequence_auto using
        quotient_realrooted := $hquot:term,
        factorization := $hrow:term) =>
      `(tactic|
        first
          | rr_product_lift_X_sequence using
              quotient_realrooted := $hquot,
              factorization := $hrow
          | rr_product_lift_checked_scalar_sequence_auto using
              quotient_realrooted := $hquot,
              factorization := $hrow
          | rr_product_lift_C_sequence_auto using
              quotient_realrooted := $hquot,
              factorization := $hrow
          | rr_product_lift_checked_affine_sequence_auto using
              quotient_realrooted := $hquot,
              factorization := $hrow
          | rr_product_lift_checked_affine_pow_sequence_auto using
              quotient_realrooted := $hquot,
              factorization := $hrow
          | rr_product_lift_X_add_C_sequence using
              quotient_realrooted := $hquot,
              factorization := $hrow
          | rr_product_lift_C_add_X_sequence using
              quotient_realrooted := $hquot,
              factorization := $hrow
          | rr_product_lift_X_pow_sequence using
              quotient_realrooted := $hquot,
              factorization := $hrow
          | rr_product_lift_C_pow_sequence_auto using
              quotient_realrooted := $hquot,
              factorization := $hrow
          | rr_product_lift_X_add_C_pow_sequence using
              quotient_realrooted := $hquot,
              factorization := $hrow
          | rr_product_lift_X_add_C_row_pow_sequence using
              quotient_realrooted := $hquot,
              factorization := $hrow
          | rr_product_lift_C_add_X_pow_sequence using
              quotient_realrooted := $hquot,
              factorization := $hrow)
  | `(tactic|
      rr_product_lift_sequence_auto using
        base := $hbase:term,
        quotient_realrooted := $hquot:term,
        cutoff := $N:term,
        factorization := $hrow:term) =>
      `(tactic|
        first
          | rr_product_lift_X_sequence using
              base := $hbase,
              quotient_realrooted := $hquot,
              cutoff := $N,
              factorization := $hrow
          | rr_product_lift_checked_scalar_sequence_auto using
              base := $hbase,
              quotient_realrooted := $hquot,
              cutoff := $N,
              factorization := $hrow
          | rr_product_lift_C_sequence_auto using
              base := $hbase,
              quotient_realrooted := $hquot,
              cutoff := $N,
              factorization := $hrow
          | rr_product_lift_checked_affine_sequence_auto using
              base := $hbase,
              quotient_realrooted := $hquot,
              cutoff := $N,
              factorization := $hrow
          | rr_product_lift_checked_affine_pow_sequence_auto using
              base := $hbase,
              quotient_realrooted := $hquot,
              cutoff := $N,
              factorization := $hrow
          | rr_product_lift_X_add_C_sequence using
              base := $hbase,
              quotient_realrooted := $hquot,
              cutoff := $N,
              factorization := $hrow
          | rr_product_lift_C_add_X_sequence using
              base := $hbase,
              quotient_realrooted := $hquot,
              cutoff := $N,
              factorization := $hrow
          | rr_product_lift_X_pow_sequence using
              base := $hbase,
              quotient_realrooted := $hquot,
              cutoff := $N,
              factorization := $hrow
          | rr_product_lift_C_pow_sequence_auto using
              base := $hbase,
              quotient_realrooted := $hquot,
              cutoff := $N,
              factorization := $hrow
          | rr_product_lift_X_add_C_pow_sequence using
              base := $hbase,
              quotient_realrooted := $hquot,
              cutoff := $N,
              factorization := $hrow
          | rr_product_lift_X_add_C_row_pow_sequence using
              base := $hbase,
              quotient_realrooted := $hquot,
              cutoff := $N,
              factorization := $hrow
          | rr_product_lift_C_add_X_pow_sequence using
              base := $hbase,
              quotient_realrooted := $hquot,
              cutoff := $N,
              factorization := $hrow)
  | `(tactic|
      rr_product_lift_X_sequence using
        quotient_realrooted := $hquot:term,
        factorization := $hrow:term) =>
      `(tactic|
        rr_product_two_sequence_variants
          (RealRooted.isRealRooted_of_X_lift_sequence $hquot $hrow),
          (RealRooted.isRealRooted_of_X_lift_right_sequence $hquot $hrow))
  | `(tactic|
      rr_product_lift_X_sequence using
        base := $hbase:term,
        quotient_realrooted := $hquot:term,
        cutoff := $N:term,
        factorization := $hrow:term) =>
      `(tactic|
        rr_product_two_sequence_variants
          (RealRooted.isRealRooted_of_X_lift_sequence_from $N $hbase $hquot $hrow),
          (RealRooted.isRealRooted_of_X_lift_right_sequence_from
            $N $hbase $hquot $hrow))
  | `(tactic|
      rr_product_lift_X_add_C_sequence using
        quotient_realrooted := $hquot:term,
        factorization := $hrow:term) =>
      `(tactic|
        rr_product_two_sequence_variants
          (RealRooted.isRealRooted_of_X_add_C_lift_sequence $hquot $hrow),
          (RealRooted.isRealRooted_of_X_add_C_lift_right_sequence
            $hquot $hrow))
  | `(tactic|
      rr_product_lift_X_add_C_sequence using
        base := $hbase:term,
        quotient_realrooted := $hquot:term,
        cutoff := $N:term,
        factorization := $hrow:term) =>
      `(tactic|
        rr_product_two_sequence_variants
          (RealRooted.isRealRooted_of_X_add_C_lift_sequence_from
            $N $hbase $hquot $hrow),
          (RealRooted.isRealRooted_of_X_add_C_lift_right_sequence_from
            $N $hbase $hquot $hrow))
  | `(tactic|
      rr_product_lift_C_add_X_sequence using
        quotient_realrooted := $hquot:term,
        factorization := $hrow:term) =>
      `(tactic|
        rr_product_two_sequence_variants
          (RealRooted.isRealRooted_of_C_add_X_lift_sequence $hquot $hrow),
          (RealRooted.isRealRooted_of_C_add_X_lift_right_sequence
            $hquot $hrow))
  | `(tactic|
      rr_product_lift_C_add_X_sequence using
        base := $hbase:term,
        quotient_realrooted := $hquot:term,
        cutoff := $N:term,
        factorization := $hrow:term) =>
      `(tactic|
        rr_product_two_sequence_variants
          (RealRooted.isRealRooted_of_C_add_X_lift_sequence_from
            $N $hbase $hquot $hrow),
          (RealRooted.isRealRooted_of_C_add_X_lift_right_sequence_from
            $N $hbase $hquot $hrow))
  | `(tactic|
      rr_product_lift_C_sequence using
        quotient_realrooted := $hquot:term,
        scalar_ne := $hc:term,
        factorization := $hrow:term) =>
      `(tactic|
        rr_product_two_sequence_variants
          (RealRooted.isRealRooted_of_C_lift_sequence $hquot $hc $hrow),
          (RealRooted.isRealRooted_of_C_lift_right_sequence $hquot $hc $hrow))
  | `(tactic|
      rr_product_lift_C_sequence using
        base := $hbase:term,
        quotient_realrooted := $hquot:term,
        scalar_ne := $hc:term,
        cutoff := $N:term,
        factorization := $hrow:term) =>
      `(tactic|
        rr_product_two_sequence_variants
          (RealRooted.isRealRooted_of_C_lift_sequence_from
            $N $hbase $hquot $hc $hrow),
          (RealRooted.isRealRooted_of_C_lift_right_sequence_from
            $N $hbase $hquot $hc $hrow))
  | `(tactic|
      rr_product_lift_C_sequence_auto using
        quotient_realrooted := $hquot:term,
        factorization := $hrow:term) =>
      `(tactic|
        rr_product_lift_C_sequence using
          quotient_realrooted := $hquot,
          scalar_ne := rr_product_nonzero_seq,
          factorization := $hrow)
  | `(tactic|
      rr_product_lift_C_sequence_auto using
        base := $hbase:term,
        quotient_realrooted := $hquot:term,
        cutoff := $N:term,
        factorization := $hrow:term) =>
      `(tactic|
        rr_product_lift_C_sequence using
          base := $hbase,
          quotient_realrooted := $hquot,
          scalar_ne := rr_product_nonzero_seq_from,
          cutoff := $N,
          factorization := $hrow)
  | `(tactic|
      rr_even_product_odd_X_scalar_sequence using
        even_realrooted := $hquot:term,
        scalar_ne := $ha:term,
        even_factorization := $heven:term,
        odd_factorization := $hodd:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_even_product_odd_X_scalar_sequence
            $hquot $ha $heven $hodd))
  | `(tactic|
      rr_product_lift_affine_sequence using
        quotient_realrooted := $hquot:term,
        slope_ne := $hs:term,
        factorization := $hrow:term) =>
      `(tactic|
        rr_product_two_sequence_variants
          (RealRooted.isRealRooted_of_C_mul_X_add_C_lift_sequence
            $hquot $hs $hrow),
          (RealRooted.isRealRooted_of_C_mul_X_add_C_lift_right_sequence
            $hquot $hs $hrow))
  | `(tactic|
      rr_product_lift_affine_sequence using
        base := $hbase:term,
        quotient_realrooted := $hquot:term,
        slope_ne := $hs:term,
        cutoff := $N:term,
        factorization := $hrow:term) =>
      `(tactic|
        rr_product_two_sequence_variants
          (RealRooted.isRealRooted_of_C_mul_X_add_C_lift_sequence_from
            $N $hbase $hquot $hs $hrow),
          (RealRooted.isRealRooted_of_C_mul_X_add_C_lift_right_sequence_from
            $N $hbase $hquot $hs $hrow))
  | `(tactic|
      rr_product_lift_affine_sequence_auto using
        quotient_realrooted := $hquot:term,
        factorization := $hrow:term) =>
      `(tactic|
        rr_product_lift_affine_sequence using
          quotient_realrooted := $hquot,
          slope_ne := rr_product_nonzero_seq,
          factorization := $hrow)
  | `(tactic|
      rr_product_lift_affine_sequence_auto using
        base := $hbase:term,
        quotient_realrooted := $hquot:term,
        cutoff := $N:term,
        factorization := $hrow:term) =>
      `(tactic|
        rr_product_lift_affine_sequence using
          base := $hbase,
          quotient_realrooted := $hquot,
          slope_ne := rr_product_nonzero_seq_from,
          cutoff := $N,
          factorization := $hrow)
  | `(tactic|
      rr_product_lift_const_first_sequence using
        quotient_realrooted := $hquot:term,
        slope_ne := $hs:term,
        factorization := $hrow:term) =>
      `(tactic|
        rr_product_two_sequence_variants
          (RealRooted.isRealRooted_of_C_add_C_mul_X_lift_sequence
            $hquot $hs $hrow),
          (RealRooted.isRealRooted_of_C_add_C_mul_X_lift_right_sequence
            $hquot $hs $hrow))
  | `(tactic|
      rr_product_lift_const_first_sequence using
        base := $hbase:term,
        quotient_realrooted := $hquot:term,
        slope_ne := $hs:term,
        cutoff := $N:term,
        factorization := $hrow:term) =>
      `(tactic|
        rr_product_two_sequence_variants
          (RealRooted.isRealRooted_of_C_add_C_mul_X_lift_sequence_from
            $N $hbase $hquot $hs $hrow),
          (RealRooted.isRealRooted_of_C_add_C_mul_X_lift_right_sequence_from
            $N $hbase $hquot $hs $hrow))
  | `(tactic|
      rr_product_lift_const_first_sequence_auto using
        quotient_realrooted := $hquot:term,
        factorization := $hrow:term) =>
      `(tactic|
        rr_product_lift_const_first_sequence using
          quotient_realrooted := $hquot,
          slope_ne := rr_product_nonzero_seq,
          factorization := $hrow)
  | `(tactic|
      rr_product_lift_const_first_sequence_auto using
        base := $hbase:term,
        quotient_realrooted := $hquot:term,
        cutoff := $N:term,
        factorization := $hrow:term) =>
      `(tactic|
        rr_product_lift_const_first_sequence using
          base := $hbase,
          quotient_realrooted := $hquot,
          slope_ne := rr_product_nonzero_seq_from,
          cutoff := $N,
          factorization := $hrow)
  | `(tactic|
      rr_product_lift_C_pow_sequence using
        quotient_realrooted := $hquot:term,
        scalar_ne := $hc:term,
        factorization := $hrow:term) =>
      `(tactic|
        rr_product_two_sequence_variants
          (RealRooted.isRealRooted_of_C_pow_lift_sequence $hquot $hc $hrow),
          (RealRooted.isRealRooted_of_C_pow_lift_right_sequence
            $hquot $hc $hrow))
  | `(tactic|
      rr_product_lift_C_pow_sequence using
        base := $hbase:term,
        quotient_realrooted := $hquot:term,
        scalar_ne := $hc:term,
        cutoff := $N:term,
        factorization := $hrow:term) =>
      `(tactic|
        rr_product_two_sequence_variants
          (RealRooted.isRealRooted_of_C_pow_lift_sequence_from
            $N $hbase $hquot $hc $hrow),
          (RealRooted.isRealRooted_of_C_pow_lift_right_sequence_from
            $N $hbase $hquot $hc $hrow))
  | `(tactic|
      rr_product_lift_C_pow_sequence_auto using
        quotient_realrooted := $hquot:term,
        factorization := $hrow:term) =>
      `(tactic|
        rr_product_lift_C_pow_sequence using
          quotient_realrooted := $hquot,
          scalar_ne := rr_product_nonzero_seq,
          factorization := $hrow)
  | `(tactic|
      rr_product_lift_C_pow_sequence_auto using
        base := $hbase:term,
        quotient_realrooted := $hquot:term,
        cutoff := $N:term,
        factorization := $hrow:term) =>
      `(tactic|
        rr_product_lift_C_pow_sequence using
          base := $hbase,
          quotient_realrooted := $hquot,
          scalar_ne := rr_product_nonzero_seq_from,
          cutoff := $N,
          factorization := $hrow)
  | `(tactic|
      rr_product_lift_X_pow_sequence using
        quotient_realrooted := $hquot:term,
        factorization := $hrow:term) =>
      `(tactic|
        rr_product_two_sequence_variants
          (RealRooted.isRealRooted_of_X_pow_lift_sequence $hquot $hrow),
          (RealRooted.isRealRooted_of_X_pow_lift_right_sequence $hquot $hrow))
  | `(tactic|
      rr_product_lift_X_pow_sequence using
        base := $hbase:term,
        quotient_realrooted := $hquot:term,
        cutoff := $N:term,
        factorization := $hrow:term) =>
      `(tactic|
        rr_product_two_sequence_variants
          (RealRooted.isRealRooted_of_X_pow_lift_sequence_from
            $N $hbase $hquot $hrow),
          (RealRooted.isRealRooted_of_X_pow_lift_right_sequence_from
            $N $hbase $hquot $hrow))
  | `(tactic|
      rr_product_lift_X_add_C_pow_sequence using
        quotient_realrooted := $hquot:term,
        factorization := $hrow:term) =>
      `(tactic|
        rr_product_two_sequence_variants
          (RealRooted.isRealRooted_of_X_add_C_pow_lift_sequence $hquot $hrow),
          (RealRooted.isRealRooted_of_X_add_C_pow_lift_right_sequence
            $hquot $hrow))
  | `(tactic|
      rr_product_lift_X_add_C_pow_sequence using
        base := $hbase:term,
        quotient_realrooted := $hquot:term,
        cutoff := $N:term,
        factorization := $hrow:term) =>
      `(tactic|
        rr_product_two_sequence_variants
          (RealRooted.isRealRooted_of_X_add_C_pow_lift_sequence_from
            $N $hbase $hquot $hrow),
          (RealRooted.isRealRooted_of_X_add_C_pow_lift_right_sequence_from
            $N $hbase $hquot $hrow))
  | `(tactic|
      rr_product_lift_X_add_C_row_pow_sequence using
        quotient_realrooted := $hquot:term,
        factorization := $hrow:term) =>
      `(tactic|
        rr_product_two_sequence_variants
          (RealRooted.isRealRooted_of_X_add_C_row_pow_lift_sequence
            $hquot $hrow),
          (RealRooted.isRealRooted_of_X_add_C_row_pow_lift_right_sequence
            $hquot $hrow))
  | `(tactic|
      rr_product_lift_X_add_C_row_pow_sequence using
        base := $hbase:term,
        quotient_realrooted := $hquot:term,
        cutoff := $N:term,
        factorization := $hrow:term) =>
      `(tactic|
        rr_product_two_sequence_variants
          (RealRooted.isRealRooted_of_X_add_C_row_pow_lift_sequence_from
            $N $hbase $hquot $hrow),
          (RealRooted.isRealRooted_of_X_add_C_row_pow_lift_right_sequence_from
            $N $hbase $hquot $hrow))
  | `(tactic|
      rr_product_lift_C_add_X_pow_sequence using
        quotient_realrooted := $hquot:term,
        factorization := $hrow:term) =>
      `(tactic|
        rr_product_two_sequence_variants
          (RealRooted.isRealRooted_of_C_add_X_pow_lift_sequence $hquot $hrow),
          (RealRooted.isRealRooted_of_C_add_X_pow_lift_right_sequence
            $hquot $hrow))
  | `(tactic|
      rr_product_lift_C_add_X_pow_sequence using
        base := $hbase:term,
        quotient_realrooted := $hquot:term,
        cutoff := $N:term,
        factorization := $hrow:term) =>
      `(tactic|
        rr_product_two_sequence_variants
          (RealRooted.isRealRooted_of_C_add_X_pow_lift_sequence_from
            $N $hbase $hquot $hrow),
          (RealRooted.isRealRooted_of_C_add_X_pow_lift_right_sequence_from
            $N $hbase $hquot $hrow))
  | `(tactic|
      rr_product_lift_affine_pow_sequence using
        quotient_realrooted := $hquot:term,
        slope_ne := $hs:term,
        factorization := $hrow:term) =>
      `(tactic|
        rr_product_two_sequence_variants
          (RealRooted.isRealRooted_of_C_mul_X_add_C_pow_lift_sequence
            $hquot $hs $hrow),
          (RealRooted.isRealRooted_of_C_mul_X_add_C_pow_lift_right_sequence
            $hquot $hs $hrow))
  | `(tactic|
      rr_product_lift_affine_pow_sequence using
        base := $hbase:term,
        quotient_realrooted := $hquot:term,
        slope_ne := $hs:term,
        cutoff := $N:term,
        factorization := $hrow:term) =>
      `(tactic|
        rr_product_two_sequence_variants
          (RealRooted.isRealRooted_of_C_mul_X_add_C_pow_lift_sequence_from
            $N $hbase $hquot $hs $hrow),
          (RealRooted.isRealRooted_of_C_mul_X_add_C_pow_lift_right_sequence_from
            $N $hbase $hquot $hs $hrow))
  | `(tactic|
      rr_product_lift_affine_pow_sequence_auto using
        quotient_realrooted := $hquot:term,
        factorization := $hrow:term) =>
      `(tactic|
        rr_product_lift_affine_pow_sequence using
          quotient_realrooted := $hquot,
          slope_ne := rr_product_nonzero_seq,
          factorization := $hrow)
  | `(tactic|
      rr_product_lift_affine_pow_sequence_auto using
        base := $hbase:term,
        quotient_realrooted := $hquot:term,
        cutoff := $N:term,
        factorization := $hrow:term) =>
      `(tactic|
        rr_product_lift_affine_pow_sequence using
          base := $hbase,
          quotient_realrooted := $hquot,
          slope_ne := rr_product_nonzero_seq_from,
          cutoff := $N,
          factorization := $hrow)
  | `(tactic|
      rr_product_lift_const_first_affine_pow_sequence using
        quotient_realrooted := $hquot:term,
        slope_ne := $hs:term,
        factorization := $hrow:term) =>
      `(tactic|
        rr_product_two_sequence_variants
          (RealRooted.isRealRooted_of_C_add_C_mul_X_pow_lift_sequence
            $hquot $hs $hrow),
          (RealRooted.isRealRooted_of_C_add_C_mul_X_pow_lift_right_sequence
            $hquot $hs $hrow))
  | `(tactic|
      rr_product_lift_const_first_affine_pow_sequence using
        base := $hbase:term,
        quotient_realrooted := $hquot:term,
        slope_ne := $hs:term,
        cutoff := $N:term,
        factorization := $hrow:term) =>
      `(tactic|
        rr_product_two_sequence_variants
          (RealRooted.isRealRooted_of_C_add_C_mul_X_pow_lift_sequence_from
            $N $hbase $hquot $hs $hrow),
          (RealRooted.isRealRooted_of_C_add_C_mul_X_pow_lift_right_sequence_from
            $N $hbase $hquot $hs $hrow))
  | `(tactic|
      rr_product_lift_const_first_affine_pow_sequence_auto using
        quotient_realrooted := $hquot:term,
        factorization := $hrow:term) =>
      `(tactic|
        rr_product_lift_const_first_affine_pow_sequence using
          quotient_realrooted := $hquot,
          slope_ne := rr_product_nonzero_seq,
          factorization := $hrow)
  | `(tactic|
      rr_product_lift_const_first_affine_pow_sequence_auto using
        base := $hbase:term,
        quotient_realrooted := $hquot:term,
        cutoff := $N:term,
        factorization := $hrow:term) =>
      `(tactic|
        rr_product_lift_const_first_affine_pow_sequence using
          base := $hbase,
          quotient_realrooted := $hquot,
          slope_ne := rr_product_nonzero_seq_from,
          cutoff := $N,
          factorization := $hrow)
  | `(tactic|
      rr_endpoint_sum_then_X_pair_sequence using
        base := $hbase:term,
        left_nonneg := $hleft_nonneg:term,
        right_nonneg := $hright_nonneg:term,
        sum_step := $hsum_step:term,
        x_step := $hx_step:term,
        coprime := $hcop:term) =>
      `(tactic|
        exact RealRooted.prec_endpoint_sum_then_X_pair_sequence
          $hbase $hleft_nonneg $hright_nonneg $hsum_step $hx_step $hcop)
  | `(tactic|
      rr_endpoint_sum_then_X_pair_sequence_realrooted using
        base := $hbase:term,
        left_nonneg := $hleft_nonneg:term,
        right_nonneg := $hright_nonneg:term,
        sum_step := $hsum_step:term,
        x_step := $hx_step:term,
        coprime := $hcop:term) =>
      `(tactic|
        rr_exact_realrooted_pair_sequence_or_projection
          (RealRooted.isRealRooted_of_endpoint_sum_then_X_pair_sequence
            $hbase $hleft_nonneg $hright_nonneg $hsum_step $hx_step $hcop))
  | `(tactic|
      rr_endpoint_X_then_sum_pair_sequence using
        base := $hbase:term,
        left_nonneg := $hleft_nonneg:term,
        right_nonneg := $hright_nonneg:term,
        x_step := $hx_step:term,
        sum_step := $hsum_step:term,
        coprime := $hcop:term) =>
      `(tactic|
        exact RealRooted.prec_endpoint_X_then_sum_pair_sequence
          $hbase $hleft_nonneg $hright_nonneg $hx_step $hsum_step $hcop)
  | `(tactic|
      rr_endpoint_X_then_sum_pair_sequence_realrooted using
        base := $hbase:term,
        left_nonneg := $hleft_nonneg:term,
        right_nonneg := $hright_nonneg:term,
        x_step := $hx_step:term,
        sum_step := $hsum_step:term,
        coprime := $hcop:term) =>
      `(tactic|
        rr_exact_realrooted_pair_sequence_or_projection
          (RealRooted.isRealRooted_of_endpoint_X_then_sum_pair_sequence
            $hbase $hleft_nonneg $hright_nonneg $hx_step $hsum_step $hcop))
  | `(tactic|
      rr_endpoint_sum_then_X_pair_lift_sequence using
        base := $hbase:term,
        left_nonneg := $hleft_nonneg:term,
        right_nonneg := $hright_nonneg:term,
        sum_step := $hsum_step:term,
        x_step := $hx_step:term,
        coprime := $hcop:term,
        even_factorization := $heven:term,
        odd_factorization := $hodd:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_endpoint_sum_then_X_pair_lift_sequence
            $hbase $hleft_nonneg $hright_nonneg $hsum_step $hx_step $hcop
            $heven $hodd))
  | `(tactic|
      rr_endpoint_X_then_sum_pair_lift_sequence using
        base := $hbase:term,
        left_nonneg := $hleft_nonneg:term,
        right_nonneg := $hright_nonneg:term,
        x_step := $hx_step:term,
        sum_step := $hsum_step:term,
        coprime := $hcop:term,
        even_factorization := $heven:term,
        odd_factorization := $hodd:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_endpoint_X_then_sum_pair_lift_sequence
            $hbase $hleft_nonneg $hright_nonneg $hx_step $hsum_step $hcop
            $heven $hodd))
  | `(tactic|
      rr_endpoint_X_then_sum_pair_lift_swapped_sequence using
        base := $hbase:term,
        left_nonneg := $hleft_nonneg:term,
        right_nonneg := $hright_nonneg:term,
        x_step := $hx_step:term,
        sum_step := $hsum_step:term,
        coprime := $hcop:term,
        even_factorization := $heven:term,
        odd_factorization := $hodd:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_endpoint_X_then_sum_pair_lift_swapped_sequence
            $hbase $hleft_nonneg $hright_nonneg $hx_step $hsum_step $hcop
            $heven $hodd))
  | `(tactic|
      rr_product_affine_sequence using
        base := $hbase:term,
        slope_ne := $hs:term,
        recurrence := $hstep:term) =>
      `(tactic|
        rr_product_two_sequence_variants
          (RealRooted.isRealRooted_of_product_affine_sequence
            $hbase $hs $hstep),
          (RealRooted.isRealRooted_of_product_affine_right_sequence
            $hbase $hs $hstep))
  | `(tactic|
      rr_product_affine_sequence using
        base := $hbase:term,
        slope_ne := $hs:term,
        cutoff := $N:term,
        recurrence := $hstep:term) =>
      `(tactic|
        rr_product_two_sequence_variants
          (RealRooted.isRealRooted_of_product_affine_sequence_from
            $N $hbase $hs $hstep),
          (RealRooted.isRealRooted_of_product_affine_right_sequence_from
            $N $hbase $hs $hstep))
  | `(tactic|
      rr_product_affine_sequence_auto using
        base := $hbase:term,
        recurrence := $hstep:term) =>
      `(tactic|
        rr_product_affine_sequence using
          base := $hbase,
          slope_ne := rr_product_nonzero_seq,
          recurrence := $hstep)
  | `(tactic|
      rr_product_affine_sequence_auto using
        base := $hbase:term,
        cutoff := $N:term,
        recurrence := $hstep:term) =>
      `(tactic|
        rr_product_affine_sequence using
          base := $hbase,
          slope_ne := rr_product_nonzero_seq,
          cutoff := $N,
          recurrence := $hstep)
  | `(tactic|
      rr_product_const_first_sequence using
        base := $hbase:term,
        slope_ne := $hs:term,
        recurrence := $hstep:term) =>
      `(tactic|
        rr_product_two_sequence_variants
          (RealRooted.isRealRooted_of_product_const_first_affine_sequence
            $hbase $hs $hstep),
          (RealRooted.isRealRooted_of_product_const_first_affine_right_sequence
            $hbase $hs $hstep))
  | `(tactic|
      rr_product_const_first_sequence using
        base := $hbase:term,
        slope_ne := $hs:term,
        cutoff := $N:term,
        recurrence := $hstep:term) =>
      `(tactic|
        rr_product_two_sequence_variants
          (RealRooted.isRealRooted_of_product_const_first_affine_sequence_from
            $N $hbase $hs $hstep),
          (RealRooted.isRealRooted_of_product_const_first_affine_right_sequence_from
            $N $hbase $hs $hstep))
  | `(tactic|
      rr_product_const_first_sequence_auto using
        base := $hbase:term,
        recurrence := $hstep:term) =>
      `(tactic|
        rr_product_const_first_sequence using
          base := $hbase,
          slope_ne := rr_product_nonzero_seq,
          recurrence := $hstep)
  | `(tactic|
      rr_product_const_first_sequence_auto using
        base := $hbase:term,
        cutoff := $N:term,
        recurrence := $hstep:term) =>
      `(tactic|
        rr_product_const_first_sequence using
          base := $hbase,
          slope_ne := rr_product_nonzero_seq,
          cutoff := $N,
          recurrence := $hstep)
  | `(tactic|
      rr_product_X_sequence using
        base := $hbase:term,
        recurrence := $hstep:term) =>
      `(tactic|
        rr_product_two_sequence_variants
          (RealRooted.isRealRooted_of_product_X_add_C_sequence $hbase $hstep),
          (RealRooted.isRealRooted_of_product_X_add_C_right_sequence
            $hbase $hstep))
  | `(tactic|
      rr_product_X_sequence using
        base := $hbase:term,
        cutoff := $N:term,
        recurrence := $hstep:term) =>
      `(tactic|
        rr_product_two_sequence_variants
          (RealRooted.isRealRooted_of_product_X_add_C_sequence_from
            $N $hbase $hstep),
          (RealRooted.isRealRooted_of_product_X_add_C_right_sequence_from
            $N $hbase $hstep))
  | `(tactic|
      rr_product_C_add_X_sequence using
        base := $hbase:term,
        recurrence := $hstep:term) =>
      `(tactic|
        rr_product_two_sequence_variants
          (RealRooted.isRealRooted_of_product_C_add_X_sequence $hbase $hstep),
          (RealRooted.isRealRooted_of_product_C_add_X_right_sequence
            $hbase $hstep))
  | `(tactic|
      rr_product_C_add_X_sequence using
        base := $hbase:term,
        cutoff := $N:term,
        recurrence := $hstep:term) =>
      `(tactic|
        rr_product_two_sequence_variants
          (RealRooted.isRealRooted_of_product_C_add_X_sequence_from
            $N $hbase $hstep),
          (RealRooted.isRealRooted_of_product_C_add_X_right_sequence_from
            $N $hbase $hstep))
  | `(tactic|
      rr_product_C_pow_sequence using
        base := $hbase:term,
        scalar_ne := $hc:term,
        recurrence := $hstep:term) =>
      `(tactic|
        rr_product_two_sequence_variants
          (RealRooted.isRealRooted_of_product_C_pow_sequence
            $hbase $hc $hstep),
          (RealRooted.isRealRooted_of_product_C_pow_right_sequence
            $hbase $hc $hstep))
  | `(tactic|
      rr_product_C_pow_sequence using
        base := $hbase:term,
        scalar_ne := $hc:term,
        cutoff := $N:term,
        recurrence := $hstep:term) =>
      `(tactic|
        rr_product_two_sequence_variants
          (RealRooted.isRealRooted_of_product_C_pow_sequence_from
            $N $hbase $hc $hstep),
          (RealRooted.isRealRooted_of_product_C_pow_right_sequence_from
            $N $hbase $hc $hstep))
  | `(tactic|
      rr_product_C_pow_sequence_auto using
        base := $hbase:term,
        recurrence := $hstep:term) =>
      `(tactic|
        rr_product_C_pow_sequence using
          base := $hbase,
          scalar_ne := rr_product_nonzero_seq,
          recurrence := $hstep)
  | `(tactic|
      rr_product_C_pow_sequence_auto using
        base := $hbase:term,
        cutoff := $N:term,
        recurrence := $hstep:term) =>
      `(tactic|
        rr_product_C_pow_sequence using
          base := $hbase,
          scalar_ne := rr_product_nonzero_seq,
          cutoff := $N,
          recurrence := $hstep)
  | `(tactic|
      rr_product_X_pow_sequence using
        base := $hbase:term,
        recurrence := $hstep:term) =>
      `(tactic|
        rr_product_two_sequence_variants
          (RealRooted.isRealRooted_of_product_X_pow_sequence $hbase $hstep),
          (RealRooted.isRealRooted_of_product_X_pow_right_sequence
            $hbase $hstep))
  | `(tactic|
      rr_product_X_pow_sequence using
        base := $hbase:term,
        cutoff := $N:term,
        recurrence := $hstep:term) =>
      `(tactic|
        rr_product_two_sequence_variants
          (RealRooted.isRealRooted_of_product_X_pow_sequence_from
            $N $hbase $hstep),
          (RealRooted.isRealRooted_of_product_X_pow_right_sequence_from
            $N $hbase $hstep))
  | `(tactic|
      rr_product_X_add_C_pow_sequence using
        base := $hbase:term,
        recurrence := $hstep:term) =>
      `(tactic|
        rr_product_two_sequence_variants
          (RealRooted.isRealRooted_of_product_X_add_C_pow_sequence
            $hbase $hstep),
          (RealRooted.isRealRooted_of_product_X_add_C_pow_right_sequence
            $hbase $hstep))
  | `(tactic|
      rr_product_X_add_C_pow_sequence using
        base := $hbase:term,
        cutoff := $N:term,
        recurrence := $hstep:term) =>
      `(tactic|
        rr_product_two_sequence_variants
          (RealRooted.isRealRooted_of_product_X_add_C_pow_sequence_from
            $N $hbase $hstep),
          (RealRooted.isRealRooted_of_product_X_add_C_pow_right_sequence_from
            $N $hbase $hstep))
  | `(tactic|
      rr_product_C_add_X_pow_sequence using
        base := $hbase:term,
        recurrence := $hstep:term) =>
      `(tactic|
        rr_product_two_sequence_variants
          (RealRooted.isRealRooted_of_product_C_add_X_pow_sequence
            $hbase $hstep),
          (RealRooted.isRealRooted_of_product_C_add_X_pow_right_sequence
            $hbase $hstep))
  | `(tactic|
      rr_product_C_add_X_pow_sequence using
        base := $hbase:term,
        cutoff := $N:term,
        recurrence := $hstep:term) =>
      `(tactic|
        rr_product_two_sequence_variants
          (RealRooted.isRealRooted_of_product_C_add_X_pow_sequence_from
            $N $hbase $hstep),
          (RealRooted.isRealRooted_of_product_C_add_X_pow_right_sequence_from
            $N $hbase $hstep))
  | `(tactic|
      rr_product_affine_pow_sequence using
        base := $hbase:term,
        slope_ne := $hs:term,
        recurrence := $hstep:term) =>
      `(tactic|
        rr_product_two_sequence_variants
          (RealRooted.isRealRooted_of_product_C_mul_X_add_C_pow_sequence
            $hbase $hs $hstep),
          (RealRooted.isRealRooted_of_product_C_mul_X_add_C_pow_right_sequence
            $hbase $hs $hstep))
  | `(tactic|
      rr_product_affine_pow_sequence using
        base := $hbase:term,
        slope_ne := $hs:term,
        cutoff := $N:term,
        recurrence := $hstep:term) =>
      `(tactic|
        rr_product_two_sequence_variants
          (RealRooted.isRealRooted_of_product_C_mul_X_add_C_pow_sequence_from
            $N $hbase $hs $hstep),
          (RealRooted.isRealRooted_of_product_C_mul_X_add_C_pow_right_sequence_from
            $N $hbase $hs $hstep))
  | `(tactic|
      rr_product_affine_pow_sequence_auto using
        base := $hbase:term,
        recurrence := $hstep:term) =>
      `(tactic|
        rr_product_affine_pow_sequence using
          base := $hbase,
          slope_ne := rr_product_nonzero_seq,
          recurrence := $hstep)
  | `(tactic|
      rr_product_affine_pow_sequence_auto using
        base := $hbase:term,
        cutoff := $N:term,
        recurrence := $hstep:term) =>
      `(tactic|
        rr_product_affine_pow_sequence using
          base := $hbase,
          slope_ne := rr_product_nonzero_seq,
          cutoff := $N,
          recurrence := $hstep)
  | `(tactic|
      rr_product_const_first_affine_pow_sequence using
        base := $hbase:term,
        slope_ne := $hs:term,
        recurrence := $hstep:term) =>
      `(tactic|
        rr_product_two_sequence_variants
          (RealRooted.isRealRooted_of_product_C_add_C_mul_X_pow_sequence
            $hbase $hs $hstep),
          (RealRooted.isRealRooted_of_product_C_add_C_mul_X_pow_right_sequence
            $hbase $hs $hstep))
  | `(tactic|
      rr_product_const_first_affine_pow_sequence using
        base := $hbase:term,
        slope_ne := $hs:term,
        cutoff := $N:term,
        recurrence := $hstep:term) =>
      `(tactic|
        rr_product_two_sequence_variants
          (RealRooted.isRealRooted_of_product_C_add_C_mul_X_pow_sequence_from
            $N $hbase $hs $hstep),
          (RealRooted.isRealRooted_of_product_C_add_C_mul_X_pow_right_sequence_from
            $N $hbase $hs $hstep))
  | `(tactic|
      rr_product_const_first_affine_pow_sequence_auto using
        base := $hbase:term,
        recurrence := $hstep:term) =>
      `(tactic|
        rr_product_const_first_affine_pow_sequence using
          base := $hbase,
          slope_ne := rr_product_nonzero_seq,
          recurrence := $hstep)
  | `(tactic|
      rr_product_const_first_affine_pow_sequence_auto using
        base := $hbase:term,
        cutoff := $N:term,
        recurrence := $hstep:term) =>
      `(tactic|
        rr_product_const_first_affine_pow_sequence using
          base := $hbase,
          slope_ne := rr_product_nonzero_seq,
          cutoff := $N,
          recurrence := $hstep)
  | `(tactic|
      rr_product_scalar_sequence using
        base := $hbase:term,
        scalar_ne := $ha:term,
        recurrence := $hstep:term) =>
      `(tactic|
        rr_product_two_sequence_variants
          (RealRooted.isRealRooted_of_product_scalar_sequence
            $hbase $ha $hstep),
          (RealRooted.isRealRooted_of_product_scalar_right_sequence
            $hbase $ha $hstep))
  | `(tactic|
      rr_product_scalar_sequence using
        base := $hbase:term,
        scalar_ne := $ha:term,
        cutoff := $N:term,
        recurrence := $hstep:term) =>
      `(tactic|
        rr_product_two_sequence_variants
          (RealRooted.isRealRooted_of_product_scalar_sequence_from
            $N $hbase $ha $hstep),
          (RealRooted.isRealRooted_of_product_scalar_right_sequence_from
            $N $hbase $ha $hstep))
  | `(tactic|
      rr_product_scalar_sequence_auto using
        base := $hbase:term,
        recurrence := $hstep:term) =>
      `(tactic|
        rr_product_scalar_sequence using
          base := $hbase,
          scalar_ne := rr_product_nonzero_seq,
          recurrence := $hstep)
  | `(tactic|
      rr_product_scalar_sequence_auto using
        base := $hbase:term,
        cutoff := $N:term,
        recurrence := $hstep:term) =>
      `(tactic|
        rr_product_scalar_sequence using
          base := $hbase,
          scalar_ne := rr_product_nonzero_seq,
          cutoff := $N,
          recurrence := $hstep)
  | `(tactic|
      rr_product_scalar_linear_sequence using
        base := $hbase:term,
        scalar_ne := $ha:term,
        cutoff := $N:term,
        scalar_step := $hscalar:term,
        linear_step := $hlinear:term) =>
      `(tactic|
        rr_product_four_sequence_variants
          (RealRooted.isRealRooted_of_product_scalar_linear_sequence_from
            $N $hbase $ha $hscalar $hlinear),
          (RealRooted.isRealRooted_of_product_scalar_linear_right_sequence_from
            $N $hbase $ha $hscalar $hlinear),
          (RealRooted.isRealRooted_of_product_scalar_linear_scalar_right_sequence_from
            $N $hbase $ha $hscalar $hlinear),
          (RealRooted.isRealRooted_of_product_scalar_linear_scalar_right_linear_right_sequence_from
            $N $hbase $ha $hscalar $hlinear))
  | `(tactic|
      rr_product_scalar_linear_sequence using
        base := $hbase:term,
        scalar_ne := $ha:term,
        scalar_step := $hscalar:term,
        linear_step := $hlinear:term) =>
      `(tactic|
        rr_product_four_sequence_variants
          (RealRooted.isRealRooted_of_product_scalar_linear_sequence
            $hbase $ha $hscalar $hlinear),
          (RealRooted.isRealRooted_of_product_scalar_linear_right_sequence
            $hbase $ha $hscalar $hlinear),
          (RealRooted.isRealRooted_of_product_scalar_linear_scalar_right_sequence
            $hbase $ha $hscalar $hlinear),
          (RealRooted.isRealRooted_of_product_scalar_linear_scalar_right_linear_right_sequence
            $hbase $ha $hscalar $hlinear))
  | `(tactic|
      rr_product_scalar_linear_sequence_auto using
        base := $hbase:term,
        cutoff := $N:term,
        scalar_step := $hscalar:term,
        linear_step := $hlinear:term) =>
      `(tactic|
        rr_product_scalar_linear_sequence using
          base := $hbase,
          scalar_ne := rr_product_nonzero_seq_from,
          cutoff := $N,
          scalar_step := $hscalar,
          linear_step := $hlinear)
  | `(tactic|
      rr_product_scalar_linear_sequence_auto using
        base := $hbase:term,
        scalar_step := $hscalar:term,
        linear_step := $hlinear:term) =>
      `(tactic|
        rr_product_scalar_linear_sequence using
          base := $hbase,
          scalar_ne := rr_product_nonzero_seq,
          scalar_step := $hscalar,
          linear_step := $hlinear)
  | `(tactic|
      rr_product_scalar_C_add_X_sequence using
        base := $hbase:term,
        scalar_ne := $ha:term,
        cutoff := $N:term,
        scalar_step := $hscalar:term,
        linear_step := $hlinear:term) =>
      `(tactic|
        rr_product_four_sequence_variants
          (RealRooted.isRealRooted_of_product_scalar_C_add_X_sequence_from
            $N $hbase $ha $hscalar $hlinear),
          (RealRooted.isRealRooted_of_product_scalar_C_add_X_right_sequence_from
            $N $hbase $ha $hscalar $hlinear),
          (RealRooted.isRealRooted_of_product_scalar_C_add_X_scalar_right_sequence_from
            $N $hbase $ha $hscalar $hlinear),
          (RealRooted.isRealRooted_of_product_scalar_C_add_X_scalar_right_linear_right_sequence_from
            $N $hbase $ha $hscalar $hlinear))
  | `(tactic|
      rr_product_scalar_C_add_X_sequence using
        base := $hbase:term,
        scalar_ne := $ha:term,
        scalar_step := $hscalar:term,
        linear_step := $hlinear:term) =>
      `(tactic|
        rr_product_four_sequence_variants
          (RealRooted.isRealRooted_of_product_scalar_C_add_X_sequence
            $hbase $ha $hscalar $hlinear),
          (RealRooted.isRealRooted_of_product_scalar_C_add_X_right_sequence
            $hbase $ha $hscalar $hlinear),
          (RealRooted.isRealRooted_of_product_scalar_C_add_X_scalar_right_sequence
            $hbase $ha $hscalar $hlinear),
          (RealRooted.isRealRooted_of_product_scalar_C_add_X_scalar_right_linear_right_sequence
            $hbase $ha $hscalar $hlinear))
  | `(tactic|
      rr_product_scalar_C_add_X_sequence_auto using
        base := $hbase:term,
        cutoff := $N:term,
        scalar_step := $hscalar:term,
        linear_step := $hlinear:term) =>
      `(tactic|
        rr_product_scalar_C_add_X_sequence using
          base := $hbase,
          scalar_ne := rr_product_nonzero_seq_from,
          cutoff := $N,
          scalar_step := $hscalar,
          linear_step := $hlinear)
  | `(tactic|
      rr_product_scalar_C_add_X_sequence_auto using
        base := $hbase:term,
        scalar_step := $hscalar:term,
        linear_step := $hlinear:term) =>
      `(tactic|
        rr_product_scalar_C_add_X_sequence using
          base := $hbase,
          scalar_ne := rr_product_nonzero_seq,
          scalar_step := $hscalar,
          linear_step := $hlinear)
  | `(tactic|
      rr_product_scalar_factor_sequence using
        base := $hbase:term,
        scalar_ne := $ha:term,
        factor_realrooted := $hfactor:term,
        cutoff := $N:term,
        scalar_step := $hscalar:term,
        factor_step := $hstep:term) =>
      `(tactic|
        rr_product_four_sequence_variants
          (RealRooted.isRealRooted_of_product_scalar_factor_sequence_from
            $N $hbase $ha $hfactor $hscalar $hstep),
          (RealRooted.isRealRooted_of_product_scalar_factor_right_sequence_from
            $N $hbase $ha $hfactor $hscalar $hstep),
          (RealRooted.isRealRooted_of_product_scalar_factor_scalar_right_sequence_from
            $N $hbase $ha $hfactor $hscalar $hstep),
          (RealRooted.isRealRooted_of_product_scalar_factor_scalar_right_factor_right_sequence_from
            $N $hbase $ha $hfactor $hscalar $hstep))
  | `(tactic|
      rr_product_scalar_factor_sequence using
        base := $hbase:term,
        scalar_ne := $ha:term,
        factor_realrooted := $hfactor:term,
        scalar_step := $hscalar:term,
        factor_step := $hstep:term) =>
      `(tactic|
        rr_product_four_sequence_variants
          (RealRooted.isRealRooted_of_product_scalar_factor_sequence
            $hbase $ha $hfactor $hscalar $hstep),
          (RealRooted.isRealRooted_of_product_scalar_factor_right_sequence
            $hbase $ha $hfactor $hscalar $hstep),
          (RealRooted.isRealRooted_of_product_scalar_factor_scalar_right_sequence
            $hbase $ha $hfactor $hscalar $hstep),
          (RealRooted.isRealRooted_of_product_scalar_factor_scalar_right_factor_right_sequence
            $hbase $ha $hfactor $hscalar $hstep))
  | `(tactic|
      rr_product_scalar_factor_sequence_auto using
        base := $hbase:term,
        factor_realrooted := $hfactor:term,
        cutoff := $N:term,
        scalar_step := $hscalar:term,
        factor_step := $hstep:term) =>
      `(tactic|
        rr_product_scalar_factor_sequence using
          base := $hbase,
          scalar_ne := rr_product_nonzero_seq_from,
          factor_realrooted := $hfactor,
          cutoff := $N,
          scalar_step := $hscalar,
          factor_step := $hstep)
  | `(tactic|
      rr_product_scalar_factor_sequence_auto using
        base := $hbase:term,
        factor_realrooted := $hfactor:term,
        scalar_step := $hscalar:term,
        factor_step := $hstep:term) =>
      `(tactic|
        rr_product_scalar_factor_sequence using
          base := $hbase,
          scalar_ne := rr_product_nonzero_seq,
          factor_realrooted := $hfactor,
          scalar_step := $hscalar,
          factor_step := $hstep)
  | `(tactic|
      rr_product_scalar_X_pow_sequence using
        base := $hbase:term,
        scalar_ne := $ha:term,
        cutoff := $N:term,
        scalar_step := $hscalar:term,
        factor_step := $hstep:term) =>
      `(tactic|
        rr_product_four_sequence_variants
          (RealRooted.isRealRooted_of_product_scalar_X_pow_sequence_from
            $N $hbase $ha $hscalar $hstep),
          (RealRooted.isRealRooted_of_product_scalar_X_pow_right_sequence_from
            $N $hbase $ha $hscalar $hstep),
          (RealRooted.isRealRooted_of_product_scalar_X_pow_scalar_right_sequence_from
            $N $hbase $ha $hscalar $hstep),
          (RealRooted.isRealRooted_of_product_scalar_X_pow_scalar_right_factor_right_sequence_from
            $N $hbase $ha $hscalar $hstep))
  | `(tactic|
      rr_product_scalar_X_pow_sequence using
        base := $hbase:term,
        scalar_ne := $ha:term,
        scalar_step := $hscalar:term,
        factor_step := $hstep:term) =>
      `(tactic|
        rr_product_four_sequence_variants
          (RealRooted.isRealRooted_of_product_scalar_X_pow_sequence
            $hbase $ha $hscalar $hstep),
          (RealRooted.isRealRooted_of_product_scalar_X_pow_right_sequence
            $hbase $ha $hscalar $hstep),
          (RealRooted.isRealRooted_of_product_scalar_X_pow_scalar_right_sequence
            $hbase $ha $hscalar $hstep),
          (RealRooted.isRealRooted_of_product_scalar_X_pow_scalar_right_factor_right_sequence
            $hbase $ha $hscalar $hstep))
  | `(tactic|
      rr_product_scalar_X_pow_sequence_auto using
        base := $hbase:term,
        cutoff := $N:term,
        scalar_step := $hscalar:term,
        factor_step := $hstep:term) =>
      `(tactic|
        rr_product_scalar_X_pow_sequence using
          base := $hbase,
          scalar_ne := rr_product_nonzero_seq_from,
          cutoff := $N,
          scalar_step := $hscalar,
          factor_step := $hstep)
  | `(tactic|
      rr_product_scalar_X_pow_sequence_auto using
        base := $hbase:term,
        scalar_step := $hscalar:term,
        factor_step := $hstep:term) =>
      `(tactic|
        rr_product_scalar_X_pow_sequence using
          base := $hbase,
          scalar_ne := rr_product_nonzero_seq,
          scalar_step := $hscalar,
          factor_step := $hstep)
  | `(tactic|
      rr_product_scalar_X_add_C_pow_sequence using
        base := $hbase:term,
        scalar_ne := $ha:term,
        cutoff := $N:term,
        scalar_step := $hscalar:term,
        factor_step := $hstep:term) =>
      `(tactic|
        rr_product_four_sequence_variants
          (RealRooted.isRealRooted_of_product_scalar_X_add_C_pow_sequence_from
            $N $hbase $ha $hscalar $hstep),
          (RealRooted.isRealRooted_of_product_scalar_X_add_C_pow_right_sequence_from
            $N $hbase $ha $hscalar $hstep),
          (RealRooted.isRealRooted_of_product_scalar_X_add_C_pow_scalar_right_sequence_from
            $N $hbase $ha $hscalar $hstep),
          (isRealRooted_of_product_scalar_X_add_C_pow_scalar_right_factor_right_sequence_from
            $N $hbase $ha $hscalar $hstep))
  | `(tactic|
      rr_product_scalar_X_add_C_pow_sequence using
        base := $hbase:term,
        scalar_ne := $ha:term,
        scalar_step := $hscalar:term,
        factor_step := $hstep:term) =>
      `(tactic|
        rr_product_four_sequence_variants
          (RealRooted.isRealRooted_of_product_scalar_X_add_C_pow_sequence
            $hbase $ha $hscalar $hstep),
          (RealRooted.isRealRooted_of_product_scalar_X_add_C_pow_right_sequence
            $hbase $ha $hscalar $hstep),
          (RealRooted.isRealRooted_of_product_scalar_X_add_C_pow_scalar_right_sequence
            $hbase $ha $hscalar $hstep),
          (isRealRooted_of_product_scalar_X_add_C_pow_scalar_right_factor_right_sequence
            $hbase $ha $hscalar $hstep))
  | `(tactic|
      rr_product_scalar_X_add_C_pow_sequence_auto using
        base := $hbase:term,
        cutoff := $N:term,
        scalar_step := $hscalar:term,
        factor_step := $hstep:term) =>
      `(tactic|
        rr_product_scalar_X_add_C_pow_sequence using
          base := $hbase,
          scalar_ne := rr_product_nonzero_seq_from,
          cutoff := $N,
          scalar_step := $hscalar,
          factor_step := $hstep)
  | `(tactic|
      rr_product_scalar_X_add_C_pow_sequence_auto using
        base := $hbase:term,
        scalar_step := $hscalar:term,
        factor_step := $hstep:term) =>
      `(tactic|
        rr_product_scalar_X_add_C_pow_sequence using
          base := $hbase,
          scalar_ne := rr_product_nonzero_seq,
          scalar_step := $hscalar,
          factor_step := $hstep)
  | `(tactic|
      rr_product_scalar_C_add_X_pow_sequence using
        base := $hbase:term,
        scalar_ne := $ha:term,
        cutoff := $N:term,
        scalar_step := $hscalar:term,
        factor_step := $hstep:term) =>
      `(tactic|
        rr_product_four_sequence_variants
          (RealRooted.isRealRooted_of_product_scalar_C_add_X_pow_sequence_from
            $N $hbase $ha $hscalar $hstep),
          (RealRooted.isRealRooted_of_product_scalar_C_add_X_pow_right_sequence_from
            $N $hbase $ha $hscalar $hstep),
          (RealRooted.isRealRooted_of_product_scalar_C_add_X_pow_scalar_right_sequence_from
            $N $hbase $ha $hscalar $hstep),
          (isRealRooted_of_product_scalar_C_add_X_pow_scalar_right_factor_right_sequence_from
            $N $hbase $ha $hscalar $hstep))
  | `(tactic|
      rr_product_scalar_C_add_X_pow_sequence using
        base := $hbase:term,
        scalar_ne := $ha:term,
        scalar_step := $hscalar:term,
        factor_step := $hstep:term) =>
      `(tactic|
        rr_product_four_sequence_variants
          (RealRooted.isRealRooted_of_product_scalar_C_add_X_pow_sequence
            $hbase $ha $hscalar $hstep),
          (RealRooted.isRealRooted_of_product_scalar_C_add_X_pow_right_sequence
            $hbase $ha $hscalar $hstep),
          (RealRooted.isRealRooted_of_product_scalar_C_add_X_pow_scalar_right_sequence
            $hbase $ha $hscalar $hstep),
          (isRealRooted_of_product_scalar_C_add_X_pow_scalar_right_factor_right_sequence
            $hbase $ha $hscalar $hstep))
  | `(tactic|
      rr_product_scalar_C_add_X_pow_sequence_auto using
        base := $hbase:term,
        cutoff := $N:term,
        scalar_step := $hscalar:term,
        factor_step := $hstep:term) =>
      `(tactic|
        rr_product_scalar_C_add_X_pow_sequence using
          base := $hbase,
          scalar_ne := rr_product_nonzero_seq_from,
          cutoff := $N,
          scalar_step := $hscalar,
          factor_step := $hstep)
  | `(tactic|
      rr_product_scalar_C_add_X_pow_sequence_auto using
        base := $hbase:term,
        scalar_step := $hscalar:term,
        factor_step := $hstep:term) =>
      `(tactic|
        rr_product_scalar_C_add_X_pow_sequence using
          base := $hbase,
          scalar_ne := rr_product_nonzero_seq,
          scalar_step := $hscalar,
          factor_step := $hstep)

end Tactic
end RealRooted
