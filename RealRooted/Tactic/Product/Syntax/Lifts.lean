import RealRooted.Tactic.Finish

/-!
# Product-lift tactic syntax

Syntax for specialized quotient and row-factor lifts.
-/

namespace RealRooted

namespace Tactic

open Lean
open Lean.Elab.Tactic
open Lean.Meta

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


end Tactic
end RealRooted
