import RealRooted.AllCombo

/-!
# All-combination tactic frontends

Thin wrappers for closure and conversion lemmas around `AllComboRealRooted`.
-/

open Polynomial

namespace RealRooted
namespace Tactic

theorem allCombo_sequence_left_realrooted {F G : Nat → ℝ[X]}
    (hall : ∀ i : Nat, AllComboRealRooted (F i) (G i))
    (hF0 : ∀ i : Nat, F i ≠ 0) :
    ∀ i : Nat, F i ≠ 0 ∧ (F i).Splits := fun i =>
  AllComboRealRooted.isRealRooted_left (hall i) (hF0 i)

theorem allCombo_sequence_right_realrooted {F G : Nat → ℝ[X]}
    (hall : ∀ i : Nat, AllComboRealRooted (F i) (G i))
    (hG0 : ∀ i : Nat, G i ≠ 0) :
    ∀ i : Nat, G i ≠ 0 ∧ (G i).Splits := fun i =>
  AllComboRealRooted.isRealRooted_right (hall i) (hG0 i)

theorem allCombo_sequence_comm {F G : Nat → ℝ[X]}
    (hall : ∀ i : Nat, AllComboRealRooted (F i) (G i)) :
    ∀ i : Nat, AllComboRealRooted (G i) (F i) := fun i =>
  AllComboRealRooted.comm (hall i)

theorem allCombo_sequence_C_mul_left {F G : Nat → ℝ[X]} (c : Nat → ℝ)
    (hall : ∀ i : Nat, AllComboRealRooted (F i) (G i)) :
    ∀ i : Nat, AllComboRealRooted (C (c i) * F i) (G i) := fun i =>
  AllComboRealRooted.C_mul_left (c := c i) (hall i)

theorem allCombo_sequence_C_mul_right {F G : Nat → ℝ[X]} (c : Nat → ℝ)
    (hall : ∀ i : Nat, AllComboRealRooted (F i) (G i)) :
    ∀ i : Nat, AllComboRealRooted (F i) (C (c i) * G i) := fun i =>
  AllComboRealRooted.C_mul_right (c := c i) (hall i)

theorem allCombo_sequence_mul_common_factor {D F G : Nat → ℝ[X]}
    (hall : ∀ i : Nat, AllComboRealRooted (F i) (G i))
    (hD : ∀ i : Nat, (D i).Splits) :
    ∀ i : Nat, AllComboRealRooted (D i * F i) (D i * G i) := fun i =>
  AllComboRealRooted.mul_common_factor (hall i) (hD i)

theorem allCombo_sequence_derivative {F G : Nat → ℝ[X]}
    (hall : ∀ i : Nat, AllComboRealRooted (F i) (G i)) :
    ∀ i : Nat, AllComboRealRooted (F i).derivative (G i).derivative := fun i =>
  AllComboRealRooted.derivative (hall i)

theorem allCombo_sequence_iterate_derivative {F G : Nat → ℝ[X]} (K : Nat → ℕ)
    (hall : ∀ i : Nat, AllComboRealRooted (F i) (G i)) :
    ∀ i : Nat,
      AllComboRealRooted ((Polynomial.derivative^[K i]) (F i))
        ((Polynomial.derivative^[K i]) (G i)) := fun i =>
  AllComboRealRooted.iterate_derivative (hall i) (K i)

theorem allCombo_sequence_iterateTDeriv
    {F G : Nat → ℝ[X]} (eps : Nat → ℝ) (K : Nat → ℕ)
    (hall : ∀ i : Nat, AllComboRealRooted (F i) (G i))
    (heps : ∀ i : Nat, 0 < eps i) :
    ∀ i : Nat,
      AllComboRealRooted (iterateTDeriv (eps i) (K i) (F i))
        (iterateTDeriv (eps i) (K i) (G i)) := fun i =>
  AllComboRealRooted.iterateTDeriv (hall i) (heps i) (K i)

theorem allCombo_sequence_to_pos_combo_sameDegree {F G : Nat → ℝ[X]}
    (hall : ∀ i : Nat, AllComboRealRooted (F i) (G i))
    (hF : ∀ i : Nat, HasPosLeadingCoeff (F i))
    (hG : ∀ i : Nat, HasPosLeadingCoeff (G i))
    (hdeg : ∀ i : Nat, (F i).natDegree = (G i).natDegree) :
    ∀ i : Nat, PosComboRealRooted (F i) (G i) := fun i =>
  AllComboRealRooted.toPosComboRealRooted_of_sameDegree
    (hall i) (hF i) (hG i) (hdeg i)

theorem allCombo_sequence_to_pos_combo_natDegree_lt {F G : Nat → ℝ[X]}
    (hall : ∀ i : Nat, AllComboRealRooted (F i) (G i))
    (hG : ∀ i : Nat, HasPosLeadingCoeff (G i))
    (hdeg : ∀ i : Nat, (F i).natDegree < (G i).natDegree) :
    ∀ i : Nat, PosComboRealRooted (F i) (G i) := fun i =>
  AllComboRealRooted.toPosComboRealRooted_of_natDegree_lt
    (hall i) (hG i) (hdeg i)

theorem allCombo_sequence_to_pos_combo_natDegree_gt {F G : Nat → ℝ[X]}
    (hall : ∀ i : Nat, AllComboRealRooted (F i) (G i))
    (hF : ∀ i : Nat, HasPosLeadingCoeff (F i))
    (hdeg : ∀ i : Nat, (G i).natDegree < (F i).natDegree) :
    ∀ i : Nat, PosComboRealRooted (F i) (G i) := fun i =>
  AllComboRealRooted.toPosComboRealRooted_of_natDegree_gt
    (hall i) (hF i) (hdeg i)

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

syntax (name := rr_all_combo_sequence_left_realrooted_named)
  "rr_all_combo_sequence_left_realrooted" " using "
    "all_combo" ":=" term ","
    "nonzero" ":=" term :
  tactic

syntax (name := rr_all_combo_right_realrooted_named)
  "rr_all_combo_right_realrooted" " using "
    "all_combo" ":=" term ","
    "nonzero" ":=" term :
  tactic

syntax (name := rr_all_combo_sequence_right_realrooted_named)
  "rr_all_combo_sequence_right_realrooted" " using "
    "all_combo" ":=" term ","
    "nonzero" ":=" term :
  tactic

syntax (name := rr_all_combo_comm_named)
  "rr_all_combo_comm" " using " "all_combo" ":=" term :
  tactic

syntax (name := rr_all_combo_sequence_comm_named)
  "rr_all_combo_sequence_comm" " using " "all_combo" ":=" term :
  tactic

syntax (name := rr_all_combo_C_mul_left_named)
  "rr_all_combo_C_mul_left" " using " "all_combo" ":=" term :
  tactic

syntax (name := rr_all_combo_sequence_C_mul_left_named)
  "rr_all_combo_sequence_C_mul_left" " using "
    "scalar" ":=" term ","
    "all_combo" ":=" term :
  tactic

syntax (name := rr_all_combo_C_mul_right_named)
  "rr_all_combo_C_mul_right" " using " "all_combo" ":=" term :
  tactic

syntax (name := rr_all_combo_sequence_C_mul_right_named)
  "rr_all_combo_sequence_C_mul_right" " using "
    "scalar" ":=" term ","
    "all_combo" ":=" term :
  tactic

syntax (name := rr_all_combo_mul_common_factor_named)
  "rr_all_combo_mul_common_factor" " using "
    "all_combo" ":=" term ","
    "factor_splits" ":=" term :
  tactic

syntax (name := rr_all_combo_sequence_mul_common_factor_named)
  "rr_all_combo_sequence_mul_common_factor" " using "
    "all_combo" ":=" term ","
    "factor_splits" ":=" term :
  tactic

syntax (name := rr_all_combo_derivative_named)
  "rr_all_combo_derivative" " using " "all_combo" ":=" term :
  tactic

syntax (name := rr_all_combo_sequence_derivative_named)
  "rr_all_combo_sequence_derivative" " using " "all_combo" ":=" term :
  tactic

syntax (name := rr_all_combo_iterate_derivative_named)
  "rr_all_combo_iterate_derivative" " using "
    "all_combo" ":=" term ","
    "index" ":=" term :
  tactic

syntax (name := rr_all_combo_sequence_iterate_derivative_named)
  "rr_all_combo_sequence_iterate_derivative" " using "
    "all_combo" ":=" term ","
    "index" ":=" term :
  tactic

syntax (name := rr_all_combo_iterateTDeriv_named)
  "rr_all_combo_iterateTDeriv" " using "
    "all_combo" ":=" term ","
    "eps_pos" ":=" term ","
    "index" ":=" term :
  tactic

syntax (name := rr_all_combo_sequence_iterateTDeriv_named)
  "rr_all_combo_sequence_iterateTDeriv" " using "
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

syntax (name := rr_all_combo_sequence_to_pos_combo_sameDegree_named)
  "rr_all_combo_sequence_to_pos_combo_sameDegree" " using "
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

syntax (name := rr_all_combo_sequence_to_pos_combo_natDegree_lt_named)
  "rr_all_combo_sequence_to_pos_combo_natDegree_lt" " using "
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

syntax (name := rr_all_combo_sequence_to_pos_combo_natDegree_gt_named)
  "rr_all_combo_sequence_to_pos_combo_natDegree_gt" " using "
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
      rr_all_combo_sequence_left_realrooted using
        all_combo := $hall:term,
        nonzero := $hf0:term) =>
      `(tactic| exact RealRooted.Tactic.allCombo_sequence_left_realrooted $hall $hf0)
  | `(tactic|
      rr_all_combo_right_realrooted using
        all_combo := $hall:term,
        nonzero := $hg0:term) =>
      `(tactic| exact RealRooted.AllComboRealRooted.isRealRooted_right $hall $hg0)
  | `(tactic|
      rr_all_combo_sequence_right_realrooted using
        all_combo := $hall:term,
        nonzero := $hg0:term) =>
      `(tactic| exact RealRooted.Tactic.allCombo_sequence_right_realrooted $hall $hg0)
  | `(tactic| rr_all_combo_comm using all_combo := $hall:term) =>
      `(tactic| exact RealRooted.AllComboRealRooted.comm $hall)
  | `(tactic| rr_all_combo_sequence_comm using all_combo := $hall:term) =>
      `(tactic| exact RealRooted.Tactic.allCombo_sequence_comm $hall)
  | `(tactic| rr_all_combo_C_mul_left using all_combo := $hall:term) =>
      `(tactic| exact RealRooted.AllComboRealRooted.C_mul_left $hall)
  | `(tactic|
      rr_all_combo_sequence_C_mul_left using
        scalar := $c:term,
        all_combo := $hall:term) =>
      `(tactic| exact RealRooted.Tactic.allCombo_sequence_C_mul_left $c $hall)
  | `(tactic| rr_all_combo_C_mul_right using all_combo := $hall:term) =>
      `(tactic| exact RealRooted.AllComboRealRooted.C_mul_right $hall)
  | `(tactic|
      rr_all_combo_sequence_C_mul_right using
        scalar := $c:term,
        all_combo := $hall:term) =>
      `(tactic| exact RealRooted.Tactic.allCombo_sequence_C_mul_right $c $hall)
  | `(tactic|
      rr_all_combo_mul_common_factor using
        all_combo := $hall:term,
        factor_splits := $hd:term) =>
      `(tactic| exact RealRooted.AllComboRealRooted.mul_common_factor $hall $hd)
  | `(tactic|
      rr_all_combo_sequence_mul_common_factor using
        all_combo := $hall:term,
        factor_splits := $hd:term) =>
      `(tactic| exact RealRooted.Tactic.allCombo_sequence_mul_common_factor $hall $hd)
  | `(tactic| rr_all_combo_derivative using all_combo := $hall:term) =>
      `(tactic| exact RealRooted.AllComboRealRooted.derivative $hall)
  | `(tactic| rr_all_combo_sequence_derivative using all_combo := $hall:term) =>
      `(tactic| exact RealRooted.Tactic.allCombo_sequence_derivative $hall)
  | `(tactic|
      rr_all_combo_iterate_derivative using
        all_combo := $hall:term,
        index := $n:term) =>
      `(tactic| exact RealRooted.AllComboRealRooted.iterate_derivative $hall $n)
  | `(tactic|
      rr_all_combo_sequence_iterate_derivative using
        all_combo := $hall:term,
        index := $n:term) =>
      `(tactic| exact RealRooted.Tactic.allCombo_sequence_iterate_derivative $n $hall)
  | `(tactic|
      rr_all_combo_iterateTDeriv using
        all_combo := $hall:term,
        eps_pos := $heps:term,
        index := $n:term) =>
      `(tactic| exact RealRooted.AllComboRealRooted.iterateTDeriv $hall $heps $n)
  | `(tactic|
      rr_all_combo_sequence_iterateTDeriv using
        all_combo := $hall:term,
        eps_pos := $heps:term,
        index := $n:term) =>
      `(tactic| exact RealRooted.Tactic.allCombo_sequence_iterateTDeriv
          _ $n $hall $heps)
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
      rr_all_combo_sequence_to_pos_combo_sameDegree using
        all_combo := $hall:term,
        left_pos_lc := $hf:term,
        right_pos_lc := $hg:term,
        degree_eq := $hdeg:term) =>
      `(tactic|
        exact RealRooted.Tactic.allCombo_sequence_to_pos_combo_sameDegree
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
      rr_all_combo_sequence_to_pos_combo_natDegree_lt using
        all_combo := $hall:term,
        right_pos_lc := $hg:term,
        degree_lt := $hdeg:term) =>
      `(tactic|
        exact RealRooted.Tactic.allCombo_sequence_to_pos_combo_natDegree_lt
          $hall $hg $hdeg)
  | `(tactic|
      rr_all_combo_to_pos_combo_natDegree_gt using
        all_combo := $hall:term,
        left_pos_lc := $hf:term,
        degree_gt := $hdeg:term) =>
      `(tactic|
        exact RealRooted.AllComboRealRooted.toPosComboRealRooted_of_natDegree_gt
          $hall $hf $hdeg)
  | `(tactic|
      rr_all_combo_sequence_to_pos_combo_natDegree_gt using
        all_combo := $hall:term,
        left_pos_lc := $hf:term,
        degree_gt := $hdeg:term) =>
      `(tactic|
        exact RealRooted.Tactic.allCombo_sequence_to_pos_combo_natDegree_gt
          $hall $hf $hdeg)

end Tactic
end RealRooted
