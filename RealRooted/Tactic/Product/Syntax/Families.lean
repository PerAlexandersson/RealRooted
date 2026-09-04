import RealRooted.Tactic.Finish

/-!
# Product-family tactic syntax

Syntax for affine, powered, scalar, and product-family recurrences.
-/

namespace RealRooted

namespace Tactic

open Lean
open Lean.Elab.Tactic
open Lean.Meta

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

end Tactic
end RealRooted
