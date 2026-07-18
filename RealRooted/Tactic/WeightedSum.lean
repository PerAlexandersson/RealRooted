import RealRooted.WeightedSum

/-!
# Weighted-sum tactic frontends

Thin wrappers for the finite Wagner weighted-sum APIs.
-/

open Polynomial

namespace RealRooted
namespace Tactic

syntax (name := rr_weighted_sum_zero_named)
  "rr_weighted_sum_zero" " using " "weights_zero" ":=" term :
  tactic

syntax (name := rr_weighted_sum_pos_lc_named)
  "rr_weighted_sum_pos_lc" " using "
    "weights_nonneg" ":=" term ","
    "terms_pos_lc" ":=" term ","
    "some_weight_pos" ":=" term :
  tactic

syntax (name := rr_weighted_compatible_left_singleton_named)
  "rr_weighted_compatible_left_singleton" " using "
    "weight_pos" ":=" term ","
    "prec" ":=" term ","
    "pos_lc" ":=" term :
  tactic

syntax (name := rr_weighted_compatible_left_cons_zero_named)
  "rr_weighted_compatible_left_cons_zero" " using "
    "weight_zero" ":=" term ","
    "prec" ":=" term ","
    "pos_lc" ":=" term ","
    "tail" ":=" term :
  tactic

syntax (name := rr_weighted_compatible_left_cons_pos_named)
  "rr_weighted_compatible_left_cons_pos" " using "
    "weight_pos" ":=" term ","
    "prec" ":=" term ","
    "pos_lc" ":=" term ","
    "tail" ":=" term ","
    "sum_ne" ":=" term ","
    "sum_splits" ":=" term ","
    "coprime" ":=" term :
  tactic

syntax (name := rr_weighted_compatible_left_prec_named)
  "rr_weighted_compatible_left_prec" " using " "compatible" ":=" term :
  tactic

syntax (name := rr_weighted_sum_left_prec_named)
  "rr_weighted_sum_left_prec" " using " "compatible" ":=" term :
  tactic

syntax (name := rr_sum_left_prec_named)
  "rr_sum_left_prec" " using " "compatible" ":=" term :
  tactic

syntax (name := rr_weighted_sum_right_prec_named)
  "rr_weighted_sum_right_prec" " using "
    "weights_nonneg" ":=" term ","
    "all_prec" ":=" term ","
    "terms_pos_lc" ":=" term ","
    "some_weight_pos" ":=" term :
  tactic

syntax (name := rr_sum_right_prec_named)
  "rr_sum_right_prec" " using "
    "all_prec" ":=" term ","
    "terms_pos_lc" ":=" term ","
    "nonempty" ":=" term :
  tactic

macro_rules
  | `(tactic| rr_weighted_sum_zero using weights_zero := $hzero:term) =>
      `(tactic| exact RealRooted.weightedSum_eq_zero_of_forall_coeff_zero _ $hzero)
  | `(tactic|
      rr_weighted_sum_pos_lc using
        weights_nonneg := $hnonneg:term,
        terms_pos_lc := $hpos:term,
        some_weight_pos := $hex:term) =>
      `(tactic| exact RealRooted.hasPosLeadingCoeff_weightedSum _ $hnonneg $hpos $hex)
  | `(tactic|
      rr_weighted_compatible_left_singleton using
        weight_pos := $ha:term,
        prec := $hprec:term,
        pos_lc := $hpos:term) =>
      `(tactic| exact RealRooted.WeightedCompatibleLeft.singleton $ha $hprec $hpos)
  | `(tactic|
      rr_weighted_compatible_left_cons_zero using
        weight_zero := $ha:term,
        prec := $hprec:term,
        pos_lc := $hpos:term,
        tail := $hl:term) =>
      `(tactic| exact RealRooted.WeightedCompatibleLeft.cons_zero $ha $hprec $hpos $hl)
  | `(tactic|
      rr_weighted_compatible_left_cons_pos using
        weight_pos := $ha:term,
        prec := $hprec:term,
        pos_lc := $hpos:term,
        tail := $hl:term,
        sum_ne := $hne:term,
        sum_splits := $hsplits:term,
        coprime := $hcop:term) =>
      `(tactic|
        exact RealRooted.WeightedCompatibleLeft.cons_pos
          $ha $hprec $hpos $hl $hne $hsplits $hcop)
  | `(tactic| rr_weighted_compatible_left_prec using compatible := $hl:term) =>
      `(tactic| exact RealRooted.WeightedCompatibleLeft.prec $hl)
  | `(tactic| rr_weighted_sum_left_prec using compatible := $hl:term) =>
      `(tactic| exact RealRooted.prec_weightedSum_left $hl)
  | `(tactic| rr_sum_left_prec using compatible := $hl:term) =>
      `(tactic| exact RealRooted.prec_sum_left $hl)
  | `(tactic|
      rr_weighted_sum_right_prec using
        weights_nonneg := $hnonneg:term,
        all_prec := $hprec:term,
        terms_pos_lc := $hpos:term,
        some_weight_pos := $hex:term) =>
      `(tactic|
        exact RealRooted.prec_weightedSum_right _ _ $hnonneg $hprec $hpos $hex)
  | `(tactic|
      rr_sum_right_prec using
        all_prec := $hprec:term,
        terms_pos_lc := $hpos:term,
        nonempty := $hne:term) =>
      `(tactic| exact RealRooted.prec_sum_right _ _ $hprec $hpos $hne)

end Tactic
end RealRooted
