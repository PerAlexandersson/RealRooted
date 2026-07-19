import RealRooted.AffineFamily

/-!
# Positive-combination tactic frontends

Thin wrappers for `PosComboRealRooted` and positive/nonnegative linear
combination certificates.
-/

open Polynomial

namespace RealRooted
namespace Tactic

theorem posCombo_sequence_nonneg_right_prec
    {F G : Nat → ℝ[X]} {a b : Nat → ℝ}
    (hfg : ∀ i : Nat, Prec (F i) (G i))
    (hF : ∀ i : Nat, HasPosLeadingCoeff (F i))
    (hG : ∀ i : Nat, HasPosLeadingCoeff (G i))
    (ha : ∀ i : Nat, 0 ≤ a i)
    (hb : ∀ i : Nat, 0 ≤ b i)
    (hab : ∀ i : Nat, 0 < a i ∨ 0 < b i) :
    ∀ i : Nat, Prec (C (a i) * F i + C (b i) * G i) (G i) := fun i =>
  prec_nonneg_combo_right (hfg i) (hF i) (hG i) (ha i) (hb i) (hab i)

theorem posCombo_sequence_nonneg_realrooted
    {F G : Nat → ℝ[X]} {a b : Nat → ℝ}
    (hfg : ∀ i : Nat, Prec (F i) (G i))
    (hF : ∀ i : Nat, HasPosLeadingCoeff (F i))
    (hG : ∀ i : Nat, HasPosLeadingCoeff (G i))
    (ha : ∀ i : Nat, 0 ≤ a i)
    (hb : ∀ i : Nat, 0 ≤ b i)
    (hab : ∀ i : Nat, 0 < a i ∨ 0 < b i) :
    ∀ i : Nat,
      (C (a i) * F i + C (b i) * G i) ≠ 0 ∧
        (C (a i) * F i + C (b i) * G i).Splits := fun i =>
  isRealRooted_nonneg_combo_of_prec
    (hfg i) (hF i) (hG i) (ha i) (hb i) (hab i)

theorem posCombo_sequence_positive_realrooted
    {F G : Nat → ℝ[X]} {a b : Nat → ℝ}
    (hfg : ∀ i : Nat, Prec (F i) (G i))
    (hF : ∀ i : Nat, HasPosLeadingCoeff (F i))
    (hG : ∀ i : Nat, HasPosLeadingCoeff (G i))
    (ha : ∀ i : Nat, 0 < a i)
    (hb : ∀ i : Nat, 0 < b i) :
    ∀ i : Nat,
      (C (a i) * F i + C (b i) * G i) ≠ 0 ∧
        (C (a i) * F i + C (b i) * G i).Splits := fun i =>
  isRealRooted_pos_combo_of_prec
    (hfg i) (hF i) (hG i) (ha i) (hb i)

theorem posCombo_sequence_comm {F G : Nat → ℝ[X]}
    (hfg : ∀ i : Nat, PosComboRealRooted (F i) (G i)) :
    ∀ i : Nat, PosComboRealRooted (G i) (F i) := fun i =>
  PosComboRealRooted.comm (hfg i)

theorem posCombo_sequence_add_realrooted {F G : Nat → ℝ[X]}
    (hfg : ∀ i : Nat, PosComboRealRooted (F i) (G i)) :
    ∀ i : Nat, F i + G i ≠ 0 ∧ (F i + G i).Splits := fun i =>
  PosComboRealRooted.isRealRooted_add (hfg i)

theorem posCombo_sequence_add_right_realrooted
    {F G : Nat → ℝ[X]} {mu : Nat → ℝ}
    (hfg : ∀ i : Nat, PosComboRealRooted (F i) (G i))
    (hmu : ∀ i : Nat, 0 < mu i) :
    ∀ i : Nat, F i + C (mu i) * G i ≠ 0 ∧
      (F i + C (mu i) * G i).Splits := fun i =>
  PosComboRealRooted.isRealRooted_add_right (hfg i) (hmu i)

theorem posCombo_sequence_add_left_realrooted
    {F G : Nat → ℝ[X]} {lam : Nat → ℝ}
    (hfg : ∀ i : Nat, PosComboRealRooted (F i) (G i))
    (hlam : ∀ i : Nat, 0 < lam i) :
    ∀ i : Nat, C (lam i) * F i + G i ≠ 0 ∧
      (C (lam i) * F i + G i).Splits := fun i =>
  PosComboRealRooted.isRealRooted_add_left (hfg i) (hlam i)

theorem posCombo_sequence_of_prec {F G : Nat → ℝ[X]}
    (hfg : ∀ i : Nat, Prec (F i) (G i))
    (hF : ∀ i : Nat, HasPosLeadingCoeff (F i))
    (hG : ∀ i : Nat, HasPosLeadingCoeff (G i)) :
    ∀ i : Nat, PosComboRealRooted (F i) (G i) := fun i =>
  PosComboRealRooted.of_prec (hfg i) (hF i) (hG i)

theorem posCombo_sequence_of_common_left {F G H : Nat → ℝ[X]}
    (hHF : ∀ i : Nat, Prec (H i) (F i))
    (hHG : ∀ i : Nat, Prec (H i) (G i))
    (hF : ∀ i : Nat, HasPosLeadingCoeff (F i))
    (hG : ∀ i : Nat, HasPosLeadingCoeff (G i)) :
    ∀ i : Nat, PosComboRealRooted (F i) (G i) := fun i =>
  PosComboRealRooted.of_commonLeftInterleaver
    (hHF i) (hHG i) (hF i) (hG i)

theorem posCombo_sequence_left_same_degree_realrooted
    {F G : Nat → ℝ[X]}
    (hfg : ∀ i : Nat, PosComboRealRooted (F i) (G i))
    (hF : ∀ i : Nat, HasPosLeadingCoeff (F i))
    (hG : ∀ i : Nat, HasPosLeadingCoeff (G i))
    (hdeg : ∀ i : Nat, (G i).natDegree = (F i).natDegree) :
    ∀ i : Nat, F i ≠ 0 ∧ (F i).Splits := fun i =>
  PosComboRealRooted.isRealRooted_left_of_sameDegree
    (hfg i) (hF i) (hG i) (hdeg i)

theorem posCombo_sequence_right_same_degree_realrooted
    {F G : Nat → ℝ[X]}
    (hfg : ∀ i : Nat, PosComboRealRooted (F i) (G i))
    (hF : ∀ i : Nat, HasPosLeadingCoeff (F i))
    (hG : ∀ i : Nat, HasPosLeadingCoeff (G i))
    (hdeg : ∀ i : Nat, (G i).natDegree = (F i).natDegree) :
    ∀ i : Nat, G i ≠ 0 ∧ (G i).Splits := fun i =>
  PosComboRealRooted.isRealRooted_right_of_sameDegree
    (hfg i) (hF i) (hG i) (hdeg i)

theorem posCombo_sequence_closed_segment_same_degree_realrooted
    {F G : Nat → ℝ[X]} {beta : Nat → ℝ}
    (hfg : ∀ i : Nat, PosComboRealRooted (F i) (G i))
    (hF : ∀ i : Nat, HasPosLeadingCoeff (F i))
    (hG : ∀ i : Nat, HasPosLeadingCoeff (G i))
    (hdeg : ∀ i : Nat, (G i).natDegree = (F i).natDegree)
    (hbeta0 : ∀ i : Nat, 0 ≤ beta i)
    (hbeta1 : ∀ i : Nat, beta i ≤ 1) :
    ∀ i : Nat, C (1 - beta i) * F i + C (beta i) * G i ≠ 0 ∧
      (C (1 - beta i) * F i + C (beta i) * G i).Splits := fun i =>
  PosComboRealRooted.isRealRooted_closed_segment_of_sameDegree
    (hfg i) (hF i) (hG i) (hdeg i) (hbeta0 i) (hbeta1 i)

syntax (name := rr_pos_combo_nonneg_right_prec_named)
  "rr_pos_combo_nonneg_right_prec" " using "
    "prec" ":=" term ","
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "left_coeff_nonneg" ":=" term ","
    "right_coeff_nonneg" ":=" term ","
    "some_coeff_pos" ":=" term :
  tactic

syntax (name := rr_pos_combo_sequence_nonneg_right_prec_named)
  "rr_pos_combo_sequence_nonneg_right_prec" " using "
    "prec" ":=" term ","
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "left_coeff_nonneg" ":=" term ","
    "right_coeff_nonneg" ":=" term ","
    "some_coeff_pos" ":=" term :
  tactic

syntax (name := rr_pos_combo_nonneg_realrooted_named)
  "rr_pos_combo_nonneg_realrooted" " using "
    "prec" ":=" term ","
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "left_coeff_nonneg" ":=" term ","
    "right_coeff_nonneg" ":=" term ","
    "some_coeff_pos" ":=" term :
  tactic

syntax (name := rr_pos_combo_sequence_nonneg_realrooted_named)
  "rr_pos_combo_sequence_nonneg_realrooted" " using "
    "prec" ":=" term ","
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "left_coeff_nonneg" ":=" term ","
    "right_coeff_nonneg" ":=" term ","
    "some_coeff_pos" ":=" term :
  tactic

syntax (name := rr_pos_combo_positive_realrooted_named)
  "rr_pos_combo_positive_realrooted" " using "
    "prec" ":=" term ","
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "left_coeff_pos" ":=" term ","
    "right_coeff_pos" ":=" term :
  tactic

syntax (name := rr_pos_combo_sequence_positive_realrooted_named)
  "rr_pos_combo_sequence_positive_realrooted" " using "
    "prec" ":=" term ","
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "left_coeff_pos" ":=" term ","
    "right_coeff_pos" ":=" term :
  tactic

syntax (name := rr_pos_combo_to_hyp_named)
  "rr_pos_combo_to_hyp" " using " "pos_combo" ":=" term :
  tactic

syntax (name := rr_pos_combo_comm_named)
  "rr_pos_combo_comm" " using " "pos_combo" ":=" term :
  tactic

syntax (name := rr_pos_combo_sequence_comm_named)
  "rr_pos_combo_sequence_comm" " using " "pos_combo" ":=" term :
  tactic

syntax (name := rr_pos_combo_reflect_named)
  "rr_pos_combo_reflect" " using "
    "pos_combo" ":=" term ","
    "left_degree_bound" ":=" term ","
    "right_degree_bound" ":=" term :
  tactic

syntax (name := rr_pos_combo_reflect_iff_named)
  "rr_pos_combo_reflect_iff" " using "
    "left_degree_bound" ":=" term ","
    "right_degree_bound" ":=" term :
  tactic

syntax (name := rr_pos_combo_add_realrooted_named)
  "rr_pos_combo_add_realrooted" " using " "pos_combo" ":=" term :
  tactic

syntax (name := rr_pos_combo_sequence_add_realrooted_named)
  "rr_pos_combo_sequence_add_realrooted" " using " "pos_combo" ":=" term :
  tactic

syntax (name := rr_pos_combo_divX_named)
  "rr_pos_combo_divX" " using "
    "pos_combo" ":=" term ","
    "left_const_zero" ":=" term ","
    "right_const_zero" ":=" term :
  tactic

syntax (name := rr_pos_combo_add_right_realrooted_named)
  "rr_pos_combo_add_right_realrooted" " using "
    "pos_combo" ":=" term ","
    "parameter_pos" ":=" term :
  tactic

syntax (name := rr_pos_combo_sequence_add_right_realrooted_named)
  "rr_pos_combo_sequence_add_right_realrooted" " using "
    "pos_combo" ":=" term ","
    "parameter_pos" ":=" term :
  tactic

syntax (name := rr_pos_combo_add_left_realrooted_named)
  "rr_pos_combo_add_left_realrooted" " using "
    "pos_combo" ":=" term ","
    "parameter_pos" ":=" term :
  tactic

syntax (name := rr_pos_combo_sequence_add_left_realrooted_named)
  "rr_pos_combo_sequence_add_left_realrooted" " using "
    "pos_combo" ":=" term ","
    "parameter_pos" ":=" term :
  tactic

syntax (name := rr_pos_combo_of_prec_named)
  "rr_pos_combo_of_prec" " using "
    "prec" ":=" term ","
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term :
  tactic

syntax (name := rr_pos_combo_sequence_of_prec_named)
  "rr_pos_combo_sequence_of_prec" " using "
    "prec" ":=" term ","
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term :
  tactic

syntax (name := rr_pos_combo_iff_add_right_named)
  "rr_pos_combo_iff_add_right" :
  tactic

syntax (name := rr_pos_combo_iff_add_left_named)
  "rr_pos_combo_iff_add_left" :
  tactic

syntax (name := rr_pos_combo_of_add_right_named)
  "rr_pos_combo_of_add_right" " using " "family" ":=" term :
  tactic

syntax (name := rr_pos_combo_of_add_left_named)
  "rr_pos_combo_of_add_left" " using " "family" ":=" term :
  tactic

syntax (name := rr_pos_combo_of_common_left_named)
  "rr_pos_combo_of_common_left" " using "
    "common_to_left" ":=" term ","
    "common_to_right" ":=" term ","
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term :
  tactic

syntax (name := rr_pos_combo_sequence_of_common_left_named)
  "rr_pos_combo_sequence_of_common_left" " using "
    "common_to_left" ":=" term ","
    "common_to_right" ":=" term ","
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term :
  tactic

syntax (name := rr_pos_combo_left_same_degree_realrooted_named)
  "rr_pos_combo_left_same_degree_realrooted" " using "
    "pos_combo" ":=" term ","
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "same_degree" ":=" term :
  tactic

syntax (name := rr_pos_combo_sequence_left_same_degree_realrooted_named)
  "rr_pos_combo_sequence_left_same_degree_realrooted" " using "
    "pos_combo" ":=" term ","
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "same_degree" ":=" term :
  tactic

syntax (name := rr_pos_combo_right_same_degree_realrooted_named)
  "rr_pos_combo_right_same_degree_realrooted" " using "
    "pos_combo" ":=" term ","
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "same_degree" ":=" term :
  tactic

syntax (name := rr_pos_combo_sequence_right_same_degree_realrooted_named)
  "rr_pos_combo_sequence_right_same_degree_realrooted" " using "
    "pos_combo" ":=" term ","
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "same_degree" ":=" term :
  tactic

syntax (name := rr_pos_combo_closed_segment_realrooted_named)
  "rr_pos_combo_closed_segment_realrooted" " using "
    "pos_combo" ":=" term ","
    "left_ne_zero" ":=" term ","
    "left_splits" ":=" term ","
    "right_ne_zero" ":=" term ","
    "right_splits" ":=" term ","
    "parameter_nonneg" ":=" term ","
    "parameter_le_one" ":=" term :
  tactic

syntax (name := rr_pos_combo_closed_segment_same_degree_realrooted_named)
  "rr_pos_combo_closed_segment_same_degree_realrooted" " using "
    "pos_combo" ":=" term ","
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "same_degree" ":=" term ","
    "parameter_nonneg" ":=" term ","
    "parameter_le_one" ":=" term :
  tactic

syntax (name := rr_pos_combo_sequence_closed_segment_same_degree_realrooted_named)
  "rr_pos_combo_sequence_closed_segment_same_degree_realrooted" " using "
    "pos_combo" ":=" term ","
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "same_degree" ":=" term ","
    "parameter_nonneg" ":=" term ","
    "parameter_le_one" ":=" term :
  tactic

syntax (name := rr_pos_combo_asw_right_pencil_named)
  "rr_pos_combo_asw_right_pencil" " using "
    "asw" ":=" term ","
    "nonzero" ":=" term ","
    "pf" ":=" term :
  tactic

syntax (name := rr_pos_combo_asw_right_pencil_tnn_named)
  "rr_pos_combo_asw_right_pencil_tnn" " using "
    "asw" ":=" term ","
    "nonzero" ":=" term ","
    "tnn" ":=" term :
  tactic

syntax (name := rr_pos_combo_family_pair_right_named)
  "rr_pos_combo_family_pair_right" " using "
    "pos_combo" ":=" term ","
    "first_parameter_pos" ":=" term ","
    "second_parameter_pos" ":=" term :
  tactic

syntax (name := rr_pos_combo_family_pair_left_named)
  "rr_pos_combo_family_pair_left" " using "
    "pos_combo" ":=" term ","
    "first_parameter_pos" ":=" term ","
    "second_parameter_pos" ":=" term :
  tactic

syntax (name := rr_pos_combo_family_pair_segment_named)
  "rr_pos_combo_family_pair_segment" " using "
    "pos_combo" ":=" term ","
    "first_parameter_pos" ":=" term ","
    "first_parameter_lt_one" ":=" term ","
    "second_parameter_pos" ":=" term ","
    "second_parameter_lt_one" ":=" term :
  tactic

syntax (name := rr_pos_combo_family_no_common_right_named)
  "rr_pos_combo_family_no_common_right" " using "
    "no_common_roots" ":=" term ","
    "parameters_ne" ":=" term :
  tactic

syntax (name := rr_pos_combo_family_no_common_left_named)
  "rr_pos_combo_family_no_common_left" " using "
    "no_common_roots" ":=" term ","
    "parameters_ne" ":=" term :
  tactic

syntax (name := rr_pos_combo_family_isCoprime_right_named)
  "rr_pos_combo_family_isCoprime_right" " using "
    "pos_combo" ":=" term ","
    "no_common_roots" ":=" term ","
    "first_parameter_pos" ":=" term ","
    "parameters_ne" ":=" term :
  tactic

syntax (name := rr_pos_combo_family_isCoprime_left_named)
  "rr_pos_combo_family_isCoprime_left" " using "
    "pos_combo" ":=" term ","
    "no_common_roots" ":=" term ","
    "first_parameter_pos" ":=" term ","
    "parameters_ne" ":=" term :
  tactic

syntax (name := rr_pos_combo_family_no_common_segment_named)
  "rr_pos_combo_family_no_common_segment" " using "
    "no_common_roots" ":=" term ","
    "parameters_ne" ":=" term :
  tactic

syntax (name := rr_pos_combo_family_isCoprime_segment_named)
  "rr_pos_combo_family_isCoprime_segment" " using "
    "pos_combo" ":=" term ","
    "no_common_roots" ":=" term ","
    "first_parameter_pos" ":=" term ","
    "first_parameter_lt_one" ":=" term ","
    "parameters_ne" ":=" term :
  tactic

syntax (name := rr_pos_combo_mul_common_factor_named)
  "rr_pos_combo_mul_common_factor" " using " "pos_combo" ":=" term :
  tactic

syntax (name := rr_pos_combo_mul_X_sub_C_named)
  "rr_pos_combo_mul_X_sub_C" " using " "pos_combo" ":=" term :
  tactic

syntax (name := rr_pos_combo_convex_right_prec_named)
  "rr_pos_combo_convex_right_prec" " using "
    "prec" ":=" term ","
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "left_coeff_pos" ":=" term ","
    "right_coeff_pos" ":=" term :
  tactic

syntax (name := rr_pos_combo_nonneg_left_prec_named)
  "rr_pos_combo_nonneg_left_prec" " using "
    "prec" ":=" term ","
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "left_coeff_nonneg" ":=" term ","
    "right_coeff_nonneg" ":=" term ","
    "some_coeff_pos" ":=" term ","
    "combo_ne_zero" ":=" term ","
    "combo_splits" ":=" term ","
    "coprime" ":=" term :
  tactic

syntax (name := rr_pos_combo_convex_left_prec_named)
  "rr_pos_combo_convex_left_prec" " using "
    "prec" ":=" term ","
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "left_coeff_pos" ":=" term ","
    "right_coeff_pos" ":=" term ","
    "combo_ne_zero" ":=" term ","
    "combo_splits" ":=" term ","
    "coprime" ":=" term :
  tactic

syntax (name := rr_pos_combo_convex_left_common_factor_prec_named)
  "rr_pos_combo_convex_left_common_factor_prec" " using "
    "factor_ne_zero" ":=" term ","
    "factor_splits" ":=" term ","
    "left_factorization" ":=" term ","
    "right_factorization" ":=" term ","
    "reduced_prec" ":=" term ","
    "reduced_left_pos_lc" ":=" term ","
    "reduced_right_pos_lc" ":=" term ","
    "left_coeff_pos" ":=" term ","
    "right_coeff_pos" ":=" term ","
    "reduced_combo_ne_zero" ":=" term ","
    "reduced_combo_splits" ":=" term ","
    "reduced_coprime" ":=" term :
  tactic

syntax (name := rr_pos_combo_right_natDegree_le_realrooted_named)
  "rr_pos_combo_right_natDegree_le_realrooted" " using "
    "pos_combo" ":=" term ","
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "degree_le" ":=" term :
  tactic

syntax (name := rr_pos_combo_left_natDegree_le_realrooted_named)
  "rr_pos_combo_left_natDegree_le_realrooted" " using "
    "pos_combo" ":=" term ","
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "degree_le" ":=" term :
  tactic

syntax (name := rr_pos_combo_right_succ_degree_realrooted_named)
  "rr_pos_combo_right_succ_degree_realrooted" " using "
    "pos_combo" ":=" term ","
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "succ_degree" ":=" term :
  tactic

syntax (name := rr_pos_combo_left_succ_degree_realrooted_named)
  "rr_pos_combo_left_succ_degree_realrooted" " using "
    "pos_combo" ":=" term ","
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "succ_degree" ":=" term :
  tactic

syntax (name := rr_pos_combo_left_succ_degree_splits_named)
  "rr_pos_combo_left_succ_degree_splits" " using "
    "pos_combo" ":=" term ","
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "succ_degree" ":=" term :
  tactic

syntax (name := rr_pos_combo_right_succ_degree_splits_named)
  "rr_pos_combo_right_succ_degree_splits" " using "
    "pos_combo" ":=" term ","
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "succ_degree" ":=" term :
  tactic

syntax (name := rr_pos_combo_left_closed_segment_succ_degree_splits_named)
  "rr_pos_combo_left_closed_segment_succ_degree_splits" " using "
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "pos_combo" ":=" term ","
    "succ_degree" ":=" term :
  tactic

syntax (name := rr_pos_combo_right_closed_segment_succ_degree_splits_named)
  "rr_pos_combo_right_closed_segment_succ_degree_splits" " using "
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "pos_combo" ":=" term ","
    "succ_degree" ":=" term :
  tactic

syntax (name := rr_pos_combo_left_closed_segment_succ_degree_realrooted_named)
  "rr_pos_combo_left_closed_segment_succ_degree_realrooted" " using "
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "pos_combo" ":=" term ","
    "succ_degree" ":=" term :
  tactic

syntax (name := rr_pos_combo_right_closed_segment_succ_degree_realrooted_named)
  "rr_pos_combo_right_closed_segment_succ_degree_realrooted" " using "
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "pos_combo" ":=" term ","
    "succ_degree" ":=" term :
  tactic

syntax (name := rr_pos_combo_left_nonneg_closed_segment_succ_degree_splits_named)
  "rr_pos_combo_left_nonneg_closed_segment_succ_degree_splits" " using "
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "left_nonneg_coeffs" ":=" term ","
    "right_nonneg_coeffs" ":=" term ","
    "pos_combo" ":=" term ","
    "succ_degree" ":=" term :
  tactic

syntax (name := rr_pos_combo_right_nonneg_closed_segment_succ_degree_splits_named)
  "rr_pos_combo_right_nonneg_closed_segment_succ_degree_splits" " using "
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "left_nonneg_coeffs" ":=" term ","
    "right_nonneg_coeffs" ":=" term ","
    "pos_combo" ":=" term ","
    "succ_degree" ":=" term :
  tactic

syntax (name := rr_pos_combo_left_nonneg_closed_segment_succ_degree_realrooted_named)
  "rr_pos_combo_left_nonneg_closed_segment_succ_degree_realrooted" " using "
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "left_nonneg_coeffs" ":=" term ","
    "right_nonneg_coeffs" ":=" term ","
    "pos_combo" ":=" term ","
    "succ_degree" ":=" term :
  tactic

syntax (name := rr_pos_combo_right_nonneg_closed_segment_succ_degree_realrooted_named)
  "rr_pos_combo_right_nonneg_closed_segment_succ_degree_realrooted" " using "
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "left_nonneg_coeffs" ":=" term ","
    "right_nonneg_coeffs" ":=" term ","
    "pos_combo" ":=" term ","
    "succ_degree" ":=" term :
  tactic

macro_rules
  | `(tactic|
      rr_pos_combo_nonneg_right_prec using
        prec := $hfg:term,
        left_pos_lc := $hfpos:term,
        right_pos_lc := $hgpos:term,
        left_coeff_nonneg := $ha:term,
        right_coeff_nonneg := $hb:term,
        some_coeff_pos := $hab:term) =>
      `(tactic|
        exact RealRooted.prec_nonneg_combo_right
          $hfg $hfpos $hgpos $ha $hb $hab)
  | `(tactic|
      rr_pos_combo_sequence_nonneg_right_prec using
        prec := $hfg:term,
        left_pos_lc := $hfpos:term,
        right_pos_lc := $hgpos:term,
        left_coeff_nonneg := $ha:term,
        right_coeff_nonneg := $hb:term,
        some_coeff_pos := $hab:term) =>
      `(tactic|
        exact RealRooted.Tactic.posCombo_sequence_nonneg_right_prec
          $hfg $hfpos $hgpos $ha $hb $hab)
  | `(tactic|
      rr_pos_combo_nonneg_realrooted using
        prec := $hfg:term,
        left_pos_lc := $hfpos:term,
        right_pos_lc := $hgpos:term,
        left_coeff_nonneg := $ha:term,
        right_coeff_nonneg := $hb:term,
        some_coeff_pos := $hab:term) =>
      `(tactic|
        exact RealRooted.isRealRooted_nonneg_combo_of_prec
          $hfg $hfpos $hgpos $ha $hb $hab)
  | `(tactic|
      rr_pos_combo_sequence_nonneg_realrooted using
        prec := $hfg:term,
        left_pos_lc := $hfpos:term,
        right_pos_lc := $hgpos:term,
        left_coeff_nonneg := $ha:term,
        right_coeff_nonneg := $hb:term,
        some_coeff_pos := $hab:term) =>
      `(tactic|
        exact RealRooted.Tactic.posCombo_sequence_nonneg_realrooted
          $hfg $hfpos $hgpos $ha $hb $hab)
  | `(tactic|
      rr_pos_combo_positive_realrooted using
        prec := $hfg:term,
        left_pos_lc := $hfpos:term,
        right_pos_lc := $hgpos:term,
        left_coeff_pos := $ha:term,
        right_coeff_pos := $hb:term) =>
      `(tactic|
        exact RealRooted.isRealRooted_pos_combo_of_prec
          $hfg $hfpos $hgpos $ha $hb)
  | `(tactic|
      rr_pos_combo_sequence_positive_realrooted using
        prec := $hfg:term,
        left_pos_lc := $hfpos:term,
        right_pos_lc := $hgpos:term,
        left_coeff_pos := $ha:term,
        right_coeff_pos := $hb:term) =>
      `(tactic|
        exact RealRooted.Tactic.posCombo_sequence_positive_realrooted
          $hfg $hfpos $hgpos $ha $hb)
  | `(tactic| rr_pos_combo_to_hyp using pos_combo := $hfg:term) =>
      `(tactic| exact RealRooted.PosComboRealRooted.toPosComboHyp $hfg)
  | `(tactic| rr_pos_combo_comm using pos_combo := $hfg:term) =>
      `(tactic| exact RealRooted.PosComboRealRooted.comm $hfg)
  | `(tactic| rr_pos_combo_sequence_comm using pos_combo := $hfg:term) =>
      `(tactic| exact RealRooted.Tactic.posCombo_sequence_comm $hfg)
  | `(tactic|
      rr_pos_combo_reflect using
        pos_combo := $hfg:term,
        left_degree_bound := $hfN:term,
        right_degree_bound := $hgN:term) =>
      `(tactic|
        exact RealRooted.PosComboRealRooted.reflect_of_natDegree_le
          $hfg $hfN $hgN)
  | `(tactic|
      rr_pos_combo_reflect_iff using
        left_degree_bound := $hfN:term,
        right_degree_bound := $hgN:term) =>
      `(tactic|
        exact RealRooted.PosComboRealRooted.reflect_iff_natDegree_le
          $hfN $hgN)
  | `(tactic| rr_pos_combo_add_realrooted using pos_combo := $hfg:term) =>
      `(tactic| exact RealRooted.PosComboRealRooted.isRealRooted_add $hfg)
  | `(tactic| rr_pos_combo_sequence_add_realrooted using pos_combo := $hfg:term) =>
      `(tactic| exact RealRooted.Tactic.posCombo_sequence_add_realrooted $hfg)
  | `(tactic|
      rr_pos_combo_divX using
        pos_combo := $hfg:term,
        left_const_zero := $hf0:term,
        right_const_zero := $hg0:term) =>
      `(tactic|
        exact RealRooted.PosComboRealRooted.divX_of_coeff_zero
          $hfg $hf0 $hg0)
  | `(tactic|
      rr_pos_combo_add_right_realrooted using
        pos_combo := $hfg:term,
        parameter_pos := $hμ:term) =>
      `(tactic|
        exact RealRooted.PosComboRealRooted.isRealRooted_add_right $hfg $hμ)
  | `(tactic|
      rr_pos_combo_sequence_add_right_realrooted using
        pos_combo := $hfg:term,
        parameter_pos := $hμ:term) =>
      `(tactic|
        exact RealRooted.Tactic.posCombo_sequence_add_right_realrooted
          $hfg $hμ)
  | `(tactic|
      rr_pos_combo_add_left_realrooted using
        pos_combo := $hfg:term,
        parameter_pos := $hlam:term) =>
      `(tactic|
        exact RealRooted.PosComboRealRooted.isRealRooted_add_left $hfg $hlam)
  | `(tactic|
      rr_pos_combo_sequence_add_left_realrooted using
        pos_combo := $hfg:term,
        parameter_pos := $hlam:term) =>
      `(tactic|
        exact RealRooted.Tactic.posCombo_sequence_add_left_realrooted
          $hfg $hlam)
  | `(tactic|
      rr_pos_combo_of_prec using
        prec := $hfg:term,
        left_pos_lc := $hfpos:term,
        right_pos_lc := $hgpos:term) =>
      `(tactic|
        exact RealRooted.PosComboRealRooted.of_prec
          $hfg $hfpos $hgpos)
  | `(tactic|
      rr_pos_combo_sequence_of_prec using
        prec := $hfg:term,
        left_pos_lc := $hfpos:term,
        right_pos_lc := $hgpos:term) =>
      `(tactic|
        exact RealRooted.Tactic.posCombo_sequence_of_prec
          $hfg $hfpos $hgpos)
  | `(tactic| rr_pos_combo_iff_add_right) =>
      `(tactic| exact RealRooted.PosComboRealRooted.iff_add_right)
  | `(tactic| rr_pos_combo_iff_add_left) =>
      `(tactic| exact RealRooted.PosComboRealRooted.iff_add_left)
  | `(tactic| rr_pos_combo_of_add_right using family := $hfamily:term) =>
      `(tactic| exact RealRooted.PosComboRealRooted.of_add_right $hfamily)
  | `(tactic| rr_pos_combo_of_add_left using family := $hfamily:term) =>
      `(tactic| exact RealRooted.PosComboRealRooted.of_add_left $hfamily)
  | `(tactic|
      rr_pos_combo_of_common_left using
        common_to_left := $hhf:term,
        common_to_right := $hhg:term,
        left_pos_lc := $hfpos:term,
        right_pos_lc := $hgpos:term) =>
      `(tactic|
        exact RealRooted.PosComboRealRooted.of_commonLeftInterleaver
          $hhf $hhg $hfpos $hgpos)
  | `(tactic|
      rr_pos_combo_sequence_of_common_left using
        common_to_left := $hhf:term,
        common_to_right := $hhg:term,
        left_pos_lc := $hfpos:term,
        right_pos_lc := $hgpos:term) =>
      `(tactic|
        exact RealRooted.Tactic.posCombo_sequence_of_common_left
          $hhf $hhg $hfpos $hgpos)
  | `(tactic|
      rr_pos_combo_left_same_degree_realrooted using
        pos_combo := $hfg:term,
        left_pos_lc := $hfpos:term,
        right_pos_lc := $hgpos:term,
        same_degree := $hdeg:term) =>
      `(tactic|
        exact RealRooted.PosComboRealRooted.isRealRooted_left_of_sameDegree
          $hfg $hfpos $hgpos $hdeg)
  | `(tactic|
      rr_pos_combo_sequence_left_same_degree_realrooted using
        pos_combo := $hfg:term,
        left_pos_lc := $hfpos:term,
        right_pos_lc := $hgpos:term,
        same_degree := $hdeg:term) =>
      `(tactic|
        exact RealRooted.Tactic.posCombo_sequence_left_same_degree_realrooted
          $hfg $hfpos $hgpos $hdeg)
  | `(tactic|
      rr_pos_combo_right_same_degree_realrooted using
        pos_combo := $hfg:term,
        left_pos_lc := $hfpos:term,
        right_pos_lc := $hgpos:term,
        same_degree := $hdeg:term) =>
      `(tactic|
        exact RealRooted.PosComboRealRooted.isRealRooted_right_of_sameDegree
          $hfg $hfpos $hgpos $hdeg)
  | `(tactic|
      rr_pos_combo_sequence_right_same_degree_realrooted using
        pos_combo := $hfg:term,
        left_pos_lc := $hfpos:term,
        right_pos_lc := $hgpos:term,
        same_degree := $hdeg:term) =>
      `(tactic|
        exact RealRooted.Tactic.posCombo_sequence_right_same_degree_realrooted
          $hfg $hfpos $hgpos $hdeg)
  | `(tactic|
      rr_pos_combo_closed_segment_realrooted using
        pos_combo := $hfg:term,
        left_ne_zero := $hfne:term,
        left_splits := $hfsplits:term,
        right_ne_zero := $hgne:term,
        right_splits := $hgsplits:term,
        parameter_nonneg := $hβ0:term,
        parameter_le_one := $hβ1:term) =>
      `(tactic|
        exact RealRooted.PosComboRealRooted.isRealRooted_closed_segment
          $hfg $hfne $hfsplits $hgne $hgsplits $hβ0 $hβ1)
  | `(tactic|
      rr_pos_combo_closed_segment_same_degree_realrooted using
        pos_combo := $hfg:term,
        left_pos_lc := $hfpos:term,
        right_pos_lc := $hgpos:term,
        same_degree := $hdeg:term,
        parameter_nonneg := $hβ0:term,
        parameter_le_one := $hβ1:term) =>
      `(tactic|
        exact
          RealRooted.PosComboRealRooted.isRealRooted_closed_segment_of_sameDegree
            $hfg $hfpos $hgpos $hdeg $hβ0 $hβ1)
  | `(tactic|
      rr_pos_combo_sequence_closed_segment_same_degree_realrooted using
        pos_combo := $hfg:term,
        left_pos_lc := $hfpos:term,
        right_pos_lc := $hgpos:term,
        same_degree := $hdeg:term,
        parameter_nonneg := $hβ0:term,
        parameter_le_one := $hβ1:term) =>
      `(tactic|
        exact
          RealRooted.Tactic.posCombo_sequence_closed_segment_same_degree_realrooted
            $hfg $hfpos $hgpos $hdeg $hβ0 $hβ1)
  | `(tactic|
      rr_pos_combo_asw_right_pencil using
        asw := $hASW:term,
        nonzero := $hne:term,
        pf := $hpf:term) =>
      `(tactic|
        exact RealRooted.PosComboRealRooted.of_aissenSchoenbergWhitney_right_pencil
          $hASW $hne $hpf)
  | `(tactic|
      rr_pos_combo_asw_right_pencil_tnn using
        asw := $hASW:term,
        nonzero := $hne:term,
        tnn := $htnn:term) =>
      `(tactic|
        exact RealRooted.PosComboRealRooted.of_aissenSchoenbergWhitney_right_pencil_tnn
          $hASW $hne $htnn)
  | `(tactic|
      rr_pos_combo_family_pair_right using
        pos_combo := $hfg:term,
        first_parameter_pos := $hμ₁:term,
        second_parameter_pos := $hμ₂:term) =>
      `(tactic|
        exact RealRooted.PosComboRealRooted.family_pair_right
          $hfg $hμ₁ $hμ₂)
  | `(tactic|
      rr_pos_combo_family_pair_left using
        pos_combo := $hfg:term,
        first_parameter_pos := $hlam₁:term,
        second_parameter_pos := $hlam₂:term) =>
      `(tactic|
        exact RealRooted.PosComboRealRooted.family_pair_left
          $hfg $hlam₁ $hlam₂)
  | `(tactic|
      rr_pos_combo_family_pair_segment using
        pos_combo := $hfg:term,
        first_parameter_pos := $hβ₁0:term,
        first_parameter_lt_one := $hβ₁1:term,
        second_parameter_pos := $hβ₂0:term,
        second_parameter_lt_one := $hβ₂1:term) =>
      `(tactic|
        exact RealRooted.PosComboRealRooted.family_pair_segment
          $hfg $hβ₁0 $hβ₁1 $hβ₂0 $hβ₂1)
  | `(tactic|
      rr_pos_combo_family_no_common_right using
        no_common_roots := $hno:term,
        parameters_ne := $hμ:term) =>
      `(tactic|
        exact RealRooted.PosComboRealRooted.family_no_common_right $hno $hμ)
  | `(tactic|
      rr_pos_combo_family_no_common_left using
        no_common_roots := $hno:term,
        parameters_ne := $hlam:term) =>
      `(tactic|
        exact RealRooted.PosComboRealRooted.family_no_common_left $hno $hlam)
  | `(tactic|
      rr_pos_combo_family_isCoprime_right using
        pos_combo := $hfg:term,
        no_common_roots := $hno:term,
        first_parameter_pos := $hμ₁:term,
        parameters_ne := $hμ:term) =>
      `(tactic|
        exact RealRooted.PosComboRealRooted.family_isCoprime_right
          $hfg $hno $hμ₁ $hμ)
  | `(tactic|
      rr_pos_combo_family_isCoprime_left using
        pos_combo := $hfg:term,
        no_common_roots := $hno:term,
        first_parameter_pos := $hlam₁:term,
        parameters_ne := $hlam:term) =>
      `(tactic|
        exact RealRooted.PosComboRealRooted.family_isCoprime_left
          $hfg $hno $hlam₁ $hlam)
  | `(tactic|
      rr_pos_combo_family_no_common_segment using
        no_common_roots := $hno:term,
        parameters_ne := $hβ:term) =>
      `(tactic|
        exact RealRooted.PosComboRealRooted.family_no_common_segment $hno $hβ)
  | `(tactic|
      rr_pos_combo_family_isCoprime_segment using
        pos_combo := $hfg:term,
        no_common_roots := $hno:term,
        first_parameter_pos := $hβ₁0:term,
        first_parameter_lt_one := $hβ₁1:term,
        parameters_ne := $hβ:term) =>
      `(tactic|
        exact RealRooted.PosComboRealRooted.family_isCoprime_segment
          $hfg $hno $hβ₁0 $hβ₁1 $hβ)
  | `(tactic| rr_pos_combo_mul_common_factor using pos_combo := $hfg:term) =>
      `(tactic|
        exact RealRooted.PosComboRealRooted.of_mul_common_factor $hfg)
  | `(tactic| rr_pos_combo_mul_X_sub_C using pos_combo := $hfg:term) =>
      `(tactic| exact RealRooted.PosComboRealRooted.of_mul_X_sub_C $hfg)
  | `(tactic|
      rr_pos_combo_convex_right_prec using
        prec := $hfg:term,
        left_pos_lc := $hfpos:term,
        right_pos_lc := $hgpos:term,
        left_coeff_pos := $ha:term,
        right_coeff_pos := $hb:term) =>
      `(tactic|
        exact RealRooted.prec_convex_right
          $hfg $hfpos $hgpos $ha $hb)
  | `(tactic|
      rr_pos_combo_nonneg_left_prec using
        prec := $hfg:term,
        left_pos_lc := $hfpos:term,
        right_pos_lc := $hgpos:term,
        left_coeff_nonneg := $ha:term,
        right_coeff_nonneg := $hb:term,
        some_coeff_pos := $hab:term,
        combo_ne_zero := $hne:term,
        combo_splits := $hsplits:term,
        coprime := $hcop:term) =>
      `(tactic|
        exact RealRooted.prec_nonneg_combo_left
          $hfg $hfpos $hgpos $ha $hb $hab $hne $hsplits $hcop)
  | `(tactic|
      rr_pos_combo_convex_left_prec using
        prec := $hfg:term,
        left_pos_lc := $hfpos:term,
        right_pos_lc := $hgpos:term,
        left_coeff_pos := $ha:term,
        right_coeff_pos := $hb:term,
        combo_ne_zero := $hne:term,
        combo_splits := $hsplits:term,
        coprime := $hcop:term) =>
      `(tactic|
        exact RealRooted.prec_convex_left
          $hfg $hfpos $hgpos $ha $hb $hne $hsplits $hcop)
  | `(tactic|
      rr_pos_combo_convex_left_common_factor_prec using
        factor_ne_zero := $hdne:term,
        factor_splits := $hdsplits:term,
        left_factorization := $hfdef:term,
        right_factorization := $hgdef:term,
        reduced_prec := $hfg:term,
        reduced_left_pos_lc := $hfpos:term,
        reduced_right_pos_lc := $hgpos:term,
        left_coeff_pos := $ha:term,
        right_coeff_pos := $hb:term,
        reduced_combo_ne_zero := $hne:term,
        reduced_combo_splits := $hsplits:term,
        reduced_coprime := $hcop:term) =>
      `(tactic|
        exact RealRooted.prec_convex_left_of_common_factor
          $hdne $hdsplits $hfdef $hgdef $hfg $hfpos $hgpos
          $ha $hb $hne $hsplits $hcop)
  | `(tactic|
      rr_pos_combo_right_natDegree_le_realrooted using
        pos_combo := $hfg:term,
        left_pos_lc := $hfpos:term,
        right_pos_lc := $hgpos:term,
        degree_le := $hdeg:term) =>
      `(tactic|
        exact RealRooted.PosComboRealRooted.isRealRooted_right_of_natDegree_le
          $hfg $hfpos $hgpos $hdeg)
  | `(tactic|
      rr_pos_combo_left_natDegree_le_realrooted using
        pos_combo := $hfg:term,
        left_pos_lc := $hfpos:term,
        right_pos_lc := $hgpos:term,
        degree_le := $hdeg:term) =>
      `(tactic|
        exact RealRooted.PosComboRealRooted.isRealRooted_left_of_natDegree_le
          $hfg $hfpos $hgpos $hdeg)
  | `(tactic|
      rr_pos_combo_right_succ_degree_realrooted using
        pos_combo := $hfg:term,
        left_pos_lc := $hfpos:term,
        right_pos_lc := $hgpos:term,
        succ_degree := $hsucc:term) =>
      `(tactic|
        exact RealRooted.PosComboRealRooted.isRealRooted_right_of_succDegree
          $hfg $hfpos $hgpos $hsucc)
  | `(tactic|
      rr_pos_combo_left_succ_degree_realrooted using
        pos_combo := $hfg:term,
        left_pos_lc := $hfpos:term,
        right_pos_lc := $hgpos:term,
        succ_degree := $hsucc:term) =>
      `(tactic|
        exact RealRooted.PosComboRealRooted.isRealRooted_left_of_succDegree
          $hfg $hfpos $hgpos $hsucc)
  | `(tactic|
      rr_pos_combo_left_succ_degree_splits using
        pos_combo := $hfg:term,
        left_pos_lc := $hfpos:term,
        right_pos_lc := $hgpos:term,
        succ_degree := $hsucc:term) =>
      `(tactic|
        exact RealRooted.PosComboRealRooted.left_splits_of_succDegree
          $hfg $hfpos $hgpos $hsucc)
  | `(tactic|
      rr_pos_combo_right_succ_degree_splits using
        pos_combo := $hfg:term,
        left_pos_lc := $hfpos:term,
        right_pos_lc := $hgpos:term,
        succ_degree := $hsucc:term) =>
      `(tactic|
        exact RealRooted.PosComboRealRooted.right_splits_of_succDegree
          $hfg $hfpos $hgpos $hsucc)
  | `(tactic|
      rr_pos_combo_left_closed_segment_succ_degree_splits using
        left_pos_lc := $hfpos:term,
        right_pos_lc := $hgpos:term,
        pos_combo := $hfg:term,
        succ_degree := $hsucc:term) =>
      `(tactic|
        exact RealRooted.left_splits_closedSegment_of_succDegree
          $hfpos $hgpos $hfg $hsucc)
  | `(tactic|
      rr_pos_combo_right_closed_segment_succ_degree_splits using
        left_pos_lc := $hfpos:term,
        right_pos_lc := $hgpos:term,
        pos_combo := $hfg:term,
        succ_degree := $hsucc:term) =>
      `(tactic|
        exact RealRooted.right_splits_closedSegment_of_succDegree
          $hfpos $hgpos $hfg $hsucc)
  | `(tactic|
      rr_pos_combo_left_closed_segment_succ_degree_realrooted using
        left_pos_lc := $hfpos:term,
        right_pos_lc := $hgpos:term,
        pos_combo := $hfg:term,
        succ_degree := $hsucc:term) =>
      `(tactic|
        exact RealRooted.left_ne_zero_and_splits_closedSegment_of_succDegree
          $hfpos $hgpos $hfg $hsucc)
  | `(tactic|
      rr_pos_combo_right_closed_segment_succ_degree_realrooted using
        left_pos_lc := $hfpos:term,
        right_pos_lc := $hgpos:term,
        pos_combo := $hfg:term,
        succ_degree := $hsucc:term) =>
      `(tactic|
        exact RealRooted.right_ne_zero_and_splits_closedSegment_of_succDegree
          $hfpos $hgpos $hfg $hsucc)
  | `(tactic|
      rr_pos_combo_left_nonneg_closed_segment_succ_degree_splits using
        left_pos_lc := $hfpos:term,
        right_pos_lc := $hgpos:term,
        left_nonneg_coeffs := $hfnn:term,
        right_nonneg_coeffs := $hgnn:term,
        pos_combo := $hfg:term,
        succ_degree := $hsucc:term) =>
      `(tactic|
        exact RealRooted.left_splits_nonneg_closedSegment_of_succDegree
          $hfpos $hgpos $hfnn $hgnn $hfg $hsucc)
  | `(tactic|
      rr_pos_combo_right_nonneg_closed_segment_succ_degree_splits using
        left_pos_lc := $hfpos:term,
        right_pos_lc := $hgpos:term,
        left_nonneg_coeffs := $hfnn:term,
        right_nonneg_coeffs := $hgnn:term,
        pos_combo := $hfg:term,
        succ_degree := $hsucc:term) =>
      `(tactic|
        exact RealRooted.right_splits_nonneg_closedSegment_of_succDegree
          $hfpos $hgpos $hfnn $hgnn $hfg $hsucc)
  | `(tactic|
      rr_pos_combo_left_nonneg_closed_segment_succ_degree_realrooted using
        left_pos_lc := $hfpos:term,
        right_pos_lc := $hgpos:term,
        left_nonneg_coeffs := $hfnn:term,
        right_nonneg_coeffs := $hgnn:term,
        pos_combo := $hfg:term,
        succ_degree := $hsucc:term) =>
      `(tactic|
        exact
          RealRooted.left_ne_zero_and_splits_nonneg_closedSegment_of_succDegree
            $hfpos $hgpos $hfnn $hgnn $hfg $hsucc)
  | `(tactic|
      rr_pos_combo_right_nonneg_closed_segment_succ_degree_realrooted using
        left_pos_lc := $hfpos:term,
        right_pos_lc := $hgpos:term,
        left_nonneg_coeffs := $hfnn:term,
        right_nonneg_coeffs := $hgnn:term,
        pos_combo := $hfg:term,
        succ_degree := $hsucc:term) =>
      `(tactic|
        exact
          RealRooted.right_ne_zero_and_splits_nonneg_closedSegment_of_succDegree
            $hfpos $hgpos $hfnn $hgnn $hfg $hsucc)

end Tactic
end RealRooted
