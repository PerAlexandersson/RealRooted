import RealRooted.Tactic.Favard.Basic

/-!
# Favard tactic direct syntax

Parser declarations for direct monic and positive-slope affine Favard certificates.
-/

namespace RealRooted
namespace Tactic

syntax (name := rr_favard) "rr_favard" " using " term ", " term : tactic

syntax (name := rr_favard_inferred) "rr_favard" : tactic

syntax (name := rr_favard_named)
  "rr_favard" " using "
    "recurrence" ":=" term ","
    "beta_pos" ":=" term :
  tactic

syntax (name := rr_favard_auto_named)
  "rr_favard_auto" " using "
    "recurrence" ":=" term :
  tactic

syntax (name := rr_favard_auto_inferred) "rr_favard_auto" : tactic

syntax (name := rr_favard_const)
  "rr_favard_const" " using " term ", " term ", " term ", " term ", " term ", " term :
  tactic

syntax (name := rr_favard_const_named)
  "rr_favard_const" " using "
    "alpha" ":=" term ","
    "beta" ":=" term ","
    "beta_pos" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "step" ":=" term :
  tactic

syntax (name := rr_favard_const_auto_named)
  "rr_favard_const_auto" " using "
    "alpha" ":=" term ","
    "beta" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "step" ":=" term :
  tactic

syntax (name := rr_favard_const_unit_named)
  "rr_favard_const_unit" " using "
    "alpha" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "step" ":=" term :
  tactic

syntax (name := rr_favard_const_unit)
  "rr_favard_const_unit" " using " term ", " term ", " term ", " term :
  tactic

syntax (name := rr_favard_param)
  "rr_favard_param" " using " term ", " term ", " term ", " term ", " term ", " term :
  tactic

syntax (name := rr_favard_param_named)
  "rr_favard_param" " using "
    "alpha" ":=" term ","
    "beta" ":=" term ","
    "beta_pos" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "step" ":=" term :
  tactic

syntax (name := rr_favard_param_auto_named)
  "rr_favard_param_auto" " using "
    "alpha" ":=" term ","
    "beta" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "step" ":=" term :
  tactic

syntax (name := rr_favard_param_unit_named)
  "rr_favard_param_unit" " using "
    "alpha" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "step" ":=" term :
  tactic

syntax (name := rr_favard_param_unit)
  "rr_favard_param_unit" " using " term ", " term ", " term ", " term :
  tactic

syntax (name := rr_favard_affine_const)
  "rr_favard_affine_const" " using " term ", " term ", " term ", " term ", "
    term ", " term ", " term ", " term :
  tactic

syntax (name := rr_favard_affine_const_named)
  "rr_favard_affine_const" " using "
    "slope" ":=" term ","
    "alpha" ":=" term ","
    "beta" ":=" term ","
    "slope_pos" ":=" term ","
    "beta_pos" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "step" ":=" term :
  tactic

syntax (name := rr_favard_affine_const_auto_named)
  "rr_favard_affine_const_auto" " using "
    "slope" ":=" term ","
    "alpha" ":=" term ","
    "beta" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "step" ":=" term :
  tactic

syntax (name := rr_favard_affine_const_unit_named)
  "rr_favard_affine_const_unit" " using "
    "slope" ":=" term ","
    "alpha" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "step" ":=" term :
  tactic

syntax (name := rr_favard_affine_const_unit)
  "rr_favard_affine_const_unit" " using " term ", " term ", " term ", "
    term ", " term :
  tactic

syntax (name := rr_favard_affine_const_row_sign_named)
  "rr_favard_affine_const_row_sign" " using "
    "slope" ":=" term ","
    "alpha" ":=" term ","
    "beta" ":=" term ","
    "slope_pos" ":=" term ","
    "beta_pos" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "step" ":=" term :
  tactic

syntax (name := rr_favard_affine_const_row_sign_auto_named)
  "rr_favard_affine_const_row_sign_auto" " using "
    "slope" ":=" term ","
    "alpha" ":=" term ","
    "beta" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "step" ":=" term :
  tactic

syntax (name := rr_favard_const_row_sign_unit_named)
  "rr_favard_const_row_sign_unit" " using "
    "alpha" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "step" ":=" term :
  tactic

syntax (name := rr_favard_const_row_sign_unit)
  "rr_favard_const_row_sign_unit" " using " term ", " term ", " term ", " term :
  tactic

syntax (name := rr_favard_affine_param)
  "rr_favard_affine_param" " using " term ", " term ", " term ", " term ", "
    term ", " term ", " term ", " term :
  tactic

syntax (name := rr_favard_affine_param_named)
  "rr_favard_affine_param" " using "
    "slope" ":=" term ","
    "alpha" ":=" term ","
    "beta" ":=" term ","
    "slope_pos" ":=" term ","
    "beta_pos" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "step" ":=" term :
  tactic

syntax (name := rr_favard_affine_param_auto_named)
  "rr_favard_affine_param_auto" " using "
    "slope" ":=" term ","
    "alpha" ":=" term ","
    "beta" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "step" ":=" term :
  tactic

syntax (name := rr_favard_affine_param_infer_named)
  "rr_favard_affine_param_infer" " using "
    "slope" ":=" term ","
    "alpha" ":=" term ","
    "beta" ":=" term ","
    "step" ":=" term :
  tactic


end Tactic
end RealRooted
