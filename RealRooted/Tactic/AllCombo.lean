import RealRooted.AllCombo

/-!
# All-combination tactic frontends

Thin wrappers for closure and conversion lemmas around `AllComboRealRooted`.
-/

open Polynomial

namespace RealRooted
namespace Tactic

syntax (name := rr_all_combo_splits_named)
  "rr_all_combo_splits" " using "
    "all_combo" ":=" term ","
    "left_scalar" ":=" term ","
    "right_scalar" ":=" term :
  tactic

syntax (name := rr_all_combo_left_realrooted_named)
  "rr_all_combo_left_realrooted" " using "
    "all_combo" ":=" term ","
    "nonzero" ":=" term :
  tactic

syntax (name := rr_all_combo_right_realrooted_named)
  "rr_all_combo_right_realrooted" " using "
    "all_combo" ":=" term ","
    "nonzero" ":=" term :
  tactic

syntax (name := rr_all_combo_comm_named)
  "rr_all_combo_comm" " using " "all_combo" ":=" term :
  tactic

syntax (name := rr_all_combo_C_mul_left_named)
  "rr_all_combo_C_mul_left" " using " "all_combo" ":=" term :
  tactic

syntax (name := rr_all_combo_C_mul_right_named)
  "rr_all_combo_C_mul_right" " using " "all_combo" ":=" term :
  tactic

syntax (name := rr_all_combo_mul_common_factor_named)
  "rr_all_combo_mul_common_factor" " using "
    "all_combo" ":=" term ","
    "factor_splits" ":=" term :
  tactic

syntax (name := rr_all_combo_derivative_named)
  "rr_all_combo_derivative" " using " "all_combo" ":=" term :
  tactic

syntax (name := rr_all_combo_iterate_derivative_named)
  "rr_all_combo_iterate_derivative" " using "
    "all_combo" ":=" term ","
    "index" ":=" term :
  tactic

syntax (name := rr_all_combo_iterateTDeriv_named)
  "rr_all_combo_iterateTDeriv" " using "
    "all_combo" ":=" term ","
    "eps_pos" ":=" term ","
    "index" ":=" term :
  tactic

syntax (name := rr_all_combo_to_pos_combo_named)
  "rr_all_combo_to_pos_combo" " using "
    "all_combo" ":=" term ","
    "positive_combos_ne_zero" ":=" term :
  tactic

syntax (name := rr_all_combo_to_pos_combo_sameDegree_named)
  "rr_all_combo_to_pos_combo_sameDegree" " using "
    "all_combo" ":=" term ","
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "degree_eq" ":=" term :
  tactic

syntax (name := rr_all_combo_to_pos_combo_natDegree_lt_named)
  "rr_all_combo_to_pos_combo_natDegree_lt" " using "
    "all_combo" ":=" term ","
    "right_pos_lc" ":=" term ","
    "degree_lt" ":=" term :
  tactic

syntax (name := rr_all_combo_to_pos_combo_natDegree_gt_named)
  "rr_all_combo_to_pos_combo_natDegree_gt" " using "
    "all_combo" ":=" term ","
    "left_pos_lc" ":=" term ","
    "degree_gt" ":=" term :
  tactic

macro_rules
  | `(tactic|
      rr_all_combo_splits using
        all_combo := $hall:term,
        left_scalar := $a:term,
        right_scalar := $b:term) =>
      `(tactic| exact RealRooted.AllComboRealRooted.splits $hall $a $b)
  | `(tactic|
      rr_all_combo_left_realrooted using
        all_combo := $hall:term,
        nonzero := $hf0:term) =>
      `(tactic| exact RealRooted.AllComboRealRooted.isRealRooted_left $hall $hf0)
  | `(tactic|
      rr_all_combo_right_realrooted using
        all_combo := $hall:term,
        nonzero := $hg0:term) =>
      `(tactic| exact RealRooted.AllComboRealRooted.isRealRooted_right $hall $hg0)
  | `(tactic| rr_all_combo_comm using all_combo := $hall:term) =>
      `(tactic| exact RealRooted.AllComboRealRooted.comm $hall)
  | `(tactic| rr_all_combo_C_mul_left using all_combo := $hall:term) =>
      `(tactic| exact RealRooted.AllComboRealRooted.C_mul_left $hall)
  | `(tactic| rr_all_combo_C_mul_right using all_combo := $hall:term) =>
      `(tactic| exact RealRooted.AllComboRealRooted.C_mul_right $hall)
  | `(tactic|
      rr_all_combo_mul_common_factor using
        all_combo := $hall:term,
        factor_splits := $hd:term) =>
      `(tactic| exact RealRooted.AllComboRealRooted.mul_common_factor $hall $hd)
  | `(tactic| rr_all_combo_derivative using all_combo := $hall:term) =>
      `(tactic| exact RealRooted.AllComboRealRooted.derivative $hall)
  | `(tactic|
      rr_all_combo_iterate_derivative using
        all_combo := $hall:term,
        index := $n:term) =>
      `(tactic| exact RealRooted.AllComboRealRooted.iterate_derivative $hall $n)
  | `(tactic|
      rr_all_combo_iterateTDeriv using
        all_combo := $hall:term,
        eps_pos := $heps:term,
        index := $n:term) =>
      `(tactic| exact RealRooted.AllComboRealRooted.iterateTDeriv $hall $heps $n)
  | `(tactic|
      rr_all_combo_to_pos_combo using
        all_combo := $hall:term,
        positive_combos_ne_zero := $hne:term) =>
      `(tactic|
        exact RealRooted.AllComboRealRooted.toPosComboRealRooted_of_pos_combos_ne_zero
          $hall $hne)
  | `(tactic|
      rr_all_combo_to_pos_combo_sameDegree using
        all_combo := $hall:term,
        left_pos_lc := $hf:term,
        right_pos_lc := $hg:term,
        degree_eq := $hdeg:term) =>
      `(tactic|
        exact RealRooted.AllComboRealRooted.toPosComboRealRooted_of_sameDegree
          $hall $hf $hg $hdeg)
  | `(tactic|
      rr_all_combo_to_pos_combo_natDegree_lt using
        all_combo := $hall:term,
        right_pos_lc := $hg:term,
        degree_lt := $hdeg:term) =>
      `(tactic|
        exact RealRooted.AllComboRealRooted.toPosComboRealRooted_of_natDegree_lt
          $hall $hg $hdeg)
  | `(tactic|
      rr_all_combo_to_pos_combo_natDegree_gt using
        all_combo := $hall:term,
        left_pos_lc := $hf:term,
        degree_gt := $hdeg:term) =>
      `(tactic|
        exact RealRooted.AllComboRealRooted.toPosComboRealRooted_of_natDegree_gt
          $hall $hf $hdeg)

end Tactic
end RealRooted
