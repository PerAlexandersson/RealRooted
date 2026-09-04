import RealRooted.Tactic.Finish

/-!
# Basic product-tactic syntax

Syntax shared by factor certificates, generic product recurrences, and model lifts.
-/

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


end Tactic
end RealRooted
