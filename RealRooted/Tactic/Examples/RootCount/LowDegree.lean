import RealRooted.Tactic.RootCount.LowDegreeRules

/-!
# Root-count tactic regressions: low-degree frontends

Regression examples for the low-degree root-count frontends of
`RealRooted.Tactic.RootCount.LowDegreeRules`: same-degree positive combinations and
compatible pairs of degree at most three.
-/

open Polynomial

namespace RealRooted
namespace Tactic

example {f g : ℝ[X]} {μ₀ μ₁ x : ℝ}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfg : PosComboRealRooted f g)
    (hdeg : g.natDegree = f.natDegree)
    (hμ₀ : 0 ≤ μ₀)
    (hμ₀μ₁ : μ₀ ≤ μ₁)
    (hne : ∀ μ ∈ Set.Icc μ₀ μ₁, ¬ (f + C μ * g).IsRoot x) :
    ((f + C μ₀ * g).roots.filter (x < ·)).card =
      ((f + C μ₁ * g).roots.filter (x < ·)).card := by
  rr_rightFamily_sameDegree_gt_count_eq using
    left_pos_lc := hf_pos,
    right_pos_lc := hg_pos,
    pos_combo := hfg,
    same_degree := hdeg,
    left_parameter_nonneg := hμ₀,
    interval_order := hμ₀μ₁,
    threshold_not_root := hne

example {f g : ℝ[X]} {x : ℝ}
    (hdeg : ∀ μ ∈ Set.Icc (0 : ℝ) 1,
      (f + C μ * g).natDegree = (f + C (0 : ℝ) * g).natDegree)
    (hrr : ∀ μ ∈ Set.Icc (0 : ℝ) 1, (f + C μ * g).Splits)
    (hne : ∀ μ ∈ Set.Icc (0 : ℝ) 1, ¬ (f + C μ * g).IsRoot x) :
    ((f + C (0 : ℝ) * g).roots.filter (x < ·)).card =
      ((f + C (1 : ℝ) * g).roots.filter (x < ·)).card := by
  rr_rightFamily_zero_one_gt_count_eq using
    degree_on_interval := hdeg,
    splits_on_interval := hrr,
    threshold_not_root := hne

example {f g : ℝ[X]} {x : ℝ}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfg : PosComboRealRooted f g)
    (hdeg : g.natDegree = f.natDegree)
    (hxg : ¬ g.IsRoot x)
    (hno : ∀ {μ : ℝ}, 0 ≤ μ → ¬ (f + C μ * g).IsRoot x) :
    (f.roots.filter (x < ·)).card = (g.roots.filter (x < ·)).card := by
  rr_sameDegree_gt_count_eq_no_rightFamily using
    left_pos_lc := hf_pos,
    right_pos_lc := hg_pos,
    pos_combo := hfg,
    same_degree := hdeg,
    right_not_root := hxg,
    no_right_family_roots := hno

example {f g : ℝ[X]} {x : ℝ}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfg : PosComboRealRooted f g)
    (hdeg : g.natDegree = f.natDegree)
    (hxg : ¬ g.IsRoot x)
    (hno : ∀ {μ : ℝ}, 0 ≤ μ → ¬ (f + C μ * g).IsRoot x) :
    ((f.roots.filter (x < ·)).card : ℤ) -
        (g.roots.filter (x < ·)).card ≤ 1 ∧
      ((g.roots.filter (x < ·)).card : ℤ) -
        (f.roots.filter (x < ·)).card ≤ 1 := by
  rr_sameDegree_rootCountAbove_no_rightFamily using
    left_pos_lc := hf_pos,
    right_pos_lc := hg_pos,
    pos_combo := hfg,
    same_degree := hdeg,
    right_not_root := hxg,
    no_right_family_roots := hno

example {f g : ℝ[X]} {x : ℝ}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfg : PosComboRealRooted f g)
    (hdeg : g.natDegree = f.natDegree)
    (hxf : ¬ f.IsRoot x)
    (hxg : ¬ g.IsRoot x)
    (hno : ¬ ∃ μ : ℝ, 0 < μ ∧ (f + C μ * g).IsRoot x) :
    ((f.roots.filter (x < ·)).card : ℤ) -
        (g.roots.filter (x < ·)).card ≤ 1 ∧
      ((g.roots.filter (x < ·)).card : ℤ) -
        (f.roots.filter (x < ·)).card ≤ 1 := by
  rr_sameDegree_rootCountAbove_no_pos_crossing using
    left_pos_lc := hf_pos,
    right_pos_lc := hg_pos,
    pos_combo := hfg,
    same_degree := hdeg,
    left_not_root := hxf,
    right_not_root := hxg,
    no_positive_crossing := hno

example {f g : ℝ[X]} {x : ℝ}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfg : PosComboRealRooted f g)
    (hdeg : g.natDegree = f.natDegree)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hxf : ¬ f.IsRoot x)
    (hxg : ¬ g.IsRoot x)
    (hcross : ∃ μ : ℝ, 0 < μ ∧ (f + C μ * g).IsRoot x) :
    ((f.roots.filter (x < ·)).card : ℤ) -
        (g.roots.filter (x < ·)).card ≤ 1 ∧
      ((g.roots.filter (x < ·)).card : ℤ) -
        (f.roots.filter (x < ·)).card ≤ 1 := by
  rr_sameDegree_rootCountAbove_pos_crossing using
    left_pos_lc := hf_pos,
    right_pos_lc := hg_pos,
    pos_combo := hfg,
    same_degree := hdeg,
    no_common_roots := hno,
    left_not_root := hxf,
    right_not_root := hxg,
    positive_crossing := hcross

example {F G : Nat → ℝ[X]} {μ₀ μ₁ x : Nat → ℝ}
    (hF_pos : ∀ i : Nat, HasPosLeadingCoeff (F i))
    (hG_pos : ∀ i : Nat, HasPosLeadingCoeff (G i))
    (hFG : ∀ i : Nat, PosComboRealRooted (F i) (G i))
    (hdeg : ∀ i : Nat, (G i).natDegree = (F i).natDegree)
    (hμ₀ : ∀ i : Nat, 0 ≤ μ₀ i)
    (hμ₀μ₁ : ∀ i : Nat, μ₀ i ≤ μ₁ i)
    (hne : ∀ i : Nat, ∀ μ ∈ Set.Icc (μ₀ i) (μ₁ i),
      ¬ (F i + C μ * G i).IsRoot (x i)) :
    ∀ i : Nat,
      ((F i + C (μ₀ i) * G i).roots.filter (x i < ·)).card =
        ((F i + C (μ₁ i) * G i).roots.filter (x i < ·)).card := by
  rr_rightFamily_sameDegree_gt_count_eq_sequence using
    left_pos_lc := hF_pos,
    right_pos_lc := hG_pos,
    pos_combo := hFG,
    same_degree := hdeg,
    left_parameter_nonneg := hμ₀,
    interval_order := hμ₀μ₁,
    threshold_not_root := hne

example {F G : Nat → ℝ[X]} {x : Nat → ℝ}
    (hdeg : ∀ i : Nat, ∀ μ ∈ Set.Icc (0 : ℝ) 1,
      (F i + C μ * G i).natDegree =
        (F i + C (0 : ℝ) * G i).natDegree)
    (hrr : ∀ i : Nat, ∀ μ ∈ Set.Icc (0 : ℝ) 1,
      (F i + C μ * G i).Splits)
    (hne : ∀ i : Nat, ∀ μ ∈ Set.Icc (0 : ℝ) 1,
      ¬ (F i + C μ * G i).IsRoot (x i)) :
    ∀ i : Nat,
      ((F i + C (0 : ℝ) * G i).roots.filter (x i < ·)).card =
        ((F i + C (1 : ℝ) * G i).roots.filter (x i < ·)).card := by
  rr_rightFamily_zero_one_gt_count_eq_sequence using
    degree_on_interval := hdeg,
    splits_on_interval := hrr,
    threshold_not_root := hne

example {F G : Nat → ℝ[X]} {x : Nat → ℝ}
    (hF_pos : ∀ i : Nat, HasPosLeadingCoeff (F i))
    (hG_pos : ∀ i : Nat, HasPosLeadingCoeff (G i))
    (hFG : ∀ i : Nat, PosComboRealRooted (F i) (G i))
    (hdeg : ∀ i : Nat, (G i).natDegree = (F i).natDegree)
    (hxG : ∀ i : Nat, ¬ (G i).IsRoot (x i))
    (hno : ∀ i : Nat, ∀ {μ : ℝ}, 0 ≤ μ →
      ¬ (F i + C μ * G i).IsRoot (x i)) :
    ∀ i : Nat,
      ((F i).roots.filter (x i < ·)).card =
        ((G i).roots.filter (x i < ·)).card := by
  rr_sameDegree_gt_count_eq_no_rightFamily_sequence using
    left_pos_lc := hF_pos,
    right_pos_lc := hG_pos,
    pos_combo := hFG,
    same_degree := hdeg,
    right_not_root := hxG,
    no_right_family_roots := hno

example {F G : Nat → ℝ[X]} {x : Nat → ℝ}
    (hF_pos : ∀ i : Nat, HasPosLeadingCoeff (F i))
    (hG_pos : ∀ i : Nat, HasPosLeadingCoeff (G i))
    (hFG : ∀ i : Nat, PosComboRealRooted (F i) (G i))
    (hdeg : ∀ i : Nat, (G i).natDegree = (F i).natDegree)
    (hxG : ∀ i : Nat, ¬ (G i).IsRoot (x i))
    (hno : ∀ i : Nat, ∀ {μ : ℝ}, 0 ≤ μ →
      ¬ (F i + C μ * G i).IsRoot (x i)) :
    ∀ i : Nat,
      (((F i).roots.filter (x i < ·)).card : ℤ) -
          ((G i).roots.filter (x i < ·)).card ≤ 1 ∧
        (((G i).roots.filter (x i < ·)).card : ℤ) -
          ((F i).roots.filter (x i < ·)).card ≤ 1 := by
  rr_sameDegree_rootCountAbove_no_rightFamily_sequence using
    left_pos_lc := hF_pos,
    right_pos_lc := hG_pos,
    pos_combo := hFG,
    same_degree := hdeg,
    right_not_root := hxG,
    no_right_family_roots := hno

example {F G : Nat → ℝ[X]} {x : Nat → ℝ}
    (hF_pos : ∀ i : Nat, HasPosLeadingCoeff (F i))
    (hG_pos : ∀ i : Nat, HasPosLeadingCoeff (G i))
    (hFG : ∀ i : Nat, PosComboRealRooted (F i) (G i))
    (hdeg : ∀ i : Nat, (G i).natDegree = (F i).natDegree)
    (hxF : ∀ i : Nat, ¬ (F i).IsRoot (x i))
    (hxG : ∀ i : Nat, ¬ (G i).IsRoot (x i))
    (hno : ∀ i : Nat,
      ¬ ∃ μ : ℝ, 0 < μ ∧ (F i + C μ * G i).IsRoot (x i)) :
    ∀ i : Nat,
      (((F i).roots.filter (x i < ·)).card : ℤ) -
          ((G i).roots.filter (x i < ·)).card ≤ 1 ∧
        (((G i).roots.filter (x i < ·)).card : ℤ) -
          ((F i).roots.filter (x i < ·)).card ≤ 1 := by
  rr_sameDegree_rootCountAbove_no_pos_crossing_sequence using
    left_pos_lc := hF_pos,
    right_pos_lc := hG_pos,
    pos_combo := hFG,
    same_degree := hdeg,
    left_not_root := hxF,
    right_not_root := hxG,
    no_positive_crossing := hno

example {F G : Nat → ℝ[X]} {x : Nat → ℝ}
    (hF_pos : ∀ i : Nat, HasPosLeadingCoeff (F i))
    (hG_pos : ∀ i : Nat, HasPosLeadingCoeff (G i))
    (hFG : ∀ i : Nat, PosComboRealRooted (F i) (G i))
    (hdeg : ∀ i : Nat, (G i).natDegree = (F i).natDegree)
    (hno : ∀ i : Nat, ∀ r, (F i).IsRoot r → ¬ (G i).IsRoot r)
    (hxF : ∀ i : Nat, ¬ (F i).IsRoot (x i))
    (hxG : ∀ i : Nat, ¬ (G i).IsRoot (x i))
    (hcross : ∀ i : Nat,
      ∃ μ : ℝ, 0 < μ ∧ (F i + C μ * G i).IsRoot (x i)) :
    ∀ i : Nat,
      (((F i).roots.filter (x i < ·)).card : ℤ) -
          ((G i).roots.filter (x i < ·)).card ≤ 1 ∧
        (((G i).roots.filter (x i < ·)).card : ℤ) -
          ((F i).roots.filter (x i < ·)).card ≤ 1 := by
  rr_sameDegree_rootCountAbove_pos_crossing_sequence using
    left_pos_lc := hF_pos,
    right_pos_lc := hG_pos,
    pos_combo := hFG,
    same_degree := hdeg,
    no_common_roots := hno,
    left_not_root := hxF,
    right_not_root := hxG,
    positive_crossing := hcross

example {f g : ℝ[X]} {x : ℝ}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g)
    (hdeg : g.natDegree = f.natDegree)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hfdeg : f.natDegree ≤ 2) :
    ((f.roots.filter (· ≤ x)).card : ℤ) -
        (g.roots.filter (· ≤ x)).card ≤ 1 ∧
      ((g.roots.filter (· ≤ x)).card : ℤ) -
        (f.roots.filter (· ≤ x)).card ≤ 1 := by
  rr_posCombo_sameDegree_rootCount_degree_le_two using
    left_pos_lc := hf_pos,
    right_pos_lc := hg_pos,
    left_nonneg_coeffs := hfnn,
    right_nonneg_coeffs := hgnn,
    pos_combo := hfg,
    same_degree := hdeg,
    no_common_roots := hno,
    left_degree_le_two := hfdeg,
    threshold := x

example {f g : ℝ[X]} {x : ℝ}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g)
    (hdeg : g.natDegree = f.natDegree)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hfdeg : f.natDegree ≤ 2) :
    ((f.roots.filter (x < ·)).card : ℤ) -
        (g.roots.filter (x < ·)).card ≤ 1 ∧
      ((g.roots.filter (x < ·)).card : ℤ) -
        (f.roots.filter (x < ·)).card ≤ 1 := by
  rr_posCombo_sameDegree_rootCountAbove_degree_le_two using
    left_pos_lc := hf_pos,
    right_pos_lc := hg_pos,
    left_nonneg_coeffs := hfnn,
    right_nonneg_coeffs := hgnn,
    pos_combo := hfg,
    same_degree := hdeg,
    no_common_roots := hno,
    left_degree_le_two := hfdeg,
    threshold := x

example {f g : ℝ[X]}
    (hfdeg : f.natDegree ≤ 1) :
    (∀ j, 1 ≤ j → j < f.natDegree →
        (rootSeqDesc g).getD j 0 ≤ (rootSeqDesc f).getD (j - 1) 0) ∧
      (∀ j, 1 ≤ j → j < f.natDegree →
        (rootSeqDesc f).getD j 0 ≤ (rootSeqDesc g).getD (j - 1) 0) := by
  rr_sameDegree_rootCrossing_degree_le_one using
    left_degree_le_one := hfdeg

example {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g)
    (hdeg : g.natDegree = f.natDegree)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hfdeg : f.natDegree ≤ 2) :
    (∀ j, 1 ≤ j → j < f.natDegree →
        (rootSeqDesc g).getD j 0 ≤ (rootSeqDesc f).getD (j - 1) 0) ∧
      (∀ j, 1 ≤ j → j < f.natDegree →
        (rootSeqDesc f).getD j 0 ≤ (rootSeqDesc g).getD (j - 1) 0) := by
  rr_posCombo_sameDegree_rootCrossing_degree_le_two using
    left_pos_lc := hf_pos,
    right_pos_lc := hg_pos,
    left_nonneg_coeffs := hfnn,
    right_nonneg_coeffs := hgnn,
    pos_combo := hfg,
    same_degree := hdeg,
    no_common_roots := hno,
    left_degree_le_two := hfdeg

example {f g : ℝ[X]} {x : ℝ}
    (hcomp : Compatible f g)
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hdeg : g.natDegree = f.natDegree + 1)
    (hf_split : f.Splits)
    (hfdeg : f.natDegree ≤ 2) :
    ((f.roots.filter (x < ·)).card : ℤ) -
        (g.roots.filter (x < ·)).card ≤ 2 ∧
      ((g.roots.filter (x < ·)).card : ℤ) -
        (f.roots.filter (x < ·)).card ≤ 2 := by
  rr_compatible_succDegree_rootCountAbove_le_two using
    compatible := hcomp,
    left_pos_lc := hf_pos,
    right_pos_lc := hg_pos,
    succ_degree := hdeg,
    left_splits := hf_split,
    left_degree_le_two := hfdeg,
    threshold := x

example {f g : ℝ[X]} {x : ℝ}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g)
    (hdeg : g.natDegree = f.natDegree)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hfdeg : f.natDegree ≤ 3) :
    ((f.roots.filter (· ≤ x)).card : ℤ) -
        (g.roots.filter (· ≤ x)).card ≤ 1 ∧
      ((g.roots.filter (· ≤ x)).card : ℤ) -
        (f.roots.filter (· ≤ x)).card ≤ 1 := by
  rr_posCombo_sameDegree_rootCount_degree_le_three using
    left_pos_lc := hf_pos,
    right_pos_lc := hg_pos,
    left_nonneg_coeffs := hfnn,
    right_nonneg_coeffs := hgnn,
    pos_combo := hfg,
    same_degree := hdeg,
    no_common_roots := hno,
    left_degree_le_three := hfdeg,
    threshold := x

example {f g : ℝ[X]} {x : ℝ}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g)
    (hdeg : g.natDegree = f.natDegree)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hfdeg : f.natDegree ≤ 3) :
    ((f.roots.filter (x < ·)).card : ℤ) -
        (g.roots.filter (x < ·)).card ≤ 1 ∧
      ((g.roots.filter (x < ·)).card : ℤ) -
        (f.roots.filter (x < ·)).card ≤ 1 := by
  rr_posCombo_sameDegree_rootCountAbove_degree_le_three using
    left_pos_lc := hf_pos,
    right_pos_lc := hg_pos,
    left_nonneg_coeffs := hfnn,
    right_nonneg_coeffs := hgnn,
    pos_combo := hfg,
    same_degree := hdeg,
    no_common_roots := hno,
    left_degree_le_three := hfdeg,
    threshold := x

example {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g)
    (hdeg : g.natDegree = f.natDegree)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hfdeg : f.natDegree ≤ 3) :
    (∀ j, 1 ≤ j → j < f.natDegree →
        (rootSeqDesc g).getD j 0 ≤ (rootSeqDesc f).getD (j - 1) 0) ∧
      (∀ j, 1 ≤ j → j < f.natDegree →
        (rootSeqDesc f).getD j 0 ≤ (rootSeqDesc g).getD (j - 1) 0) := by
  rr_posCombo_sameDegree_rootCrossing_degree_le_three using
    left_pos_lc := hf_pos,
    right_pos_lc := hg_pos,
    left_nonneg_coeffs := hfnn,
    right_nonneg_coeffs := hgnn,
    pos_combo := hfg,
    same_degree := hdeg,
    no_common_roots := hno,
    left_degree_le_three := hfdeg

example {F G : Nat → ℝ[X]} {x : Nat → ℝ}
    (hF_pos : ∀ i : Nat, HasPosLeadingCoeff (F i))
    (hG_pos : ∀ i : Nat, HasPosLeadingCoeff (G i))
    (hFnn : ∀ i : Nat, HasNonnegCoeffs (F i))
    (hGnn : ∀ i : Nat, HasNonnegCoeffs (G i))
    (hFG : ∀ i : Nat, PosComboRealRooted (F i) (G i))
    (hdeg : ∀ i : Nat, (G i).natDegree = (F i).natDegree)
    (hno : ∀ i : Nat, ∀ r, (F i).IsRoot r → ¬ (G i).IsRoot r)
    (hFdeg : ∀ i : Nat, (F i).natDegree ≤ 2) :
    ∀ i : Nat,
      (((F i).roots.filter (· ≤ x i)).card : ℤ) -
          ((G i).roots.filter (· ≤ x i)).card ≤ 1 ∧
        (((G i).roots.filter (· ≤ x i)).card : ℤ) -
          ((F i).roots.filter (· ≤ x i)).card ≤ 1 := by
  rr_posCombo_sameDegree_rootCount_degree_le_two_sequence using
    left_pos_lc := hF_pos,
    right_pos_lc := hG_pos,
    left_nonneg_coeffs := hFnn,
    right_nonneg_coeffs := hGnn,
    pos_combo := hFG,
    same_degree := hdeg,
    no_common_roots := hno,
    left_degree_le_two := hFdeg

example {F G : Nat → ℝ[X]} {x : Nat → ℝ}
    (hF_pos : ∀ i : Nat, HasPosLeadingCoeff (F i))
    (hG_pos : ∀ i : Nat, HasPosLeadingCoeff (G i))
    (hFnn : ∀ i : Nat, HasNonnegCoeffs (F i))
    (hGnn : ∀ i : Nat, HasNonnegCoeffs (G i))
    (hFG : ∀ i : Nat, PosComboRealRooted (F i) (G i))
    (hdeg : ∀ i : Nat, (G i).natDegree = (F i).natDegree)
    (hno : ∀ i : Nat, ∀ r, (F i).IsRoot r → ¬ (G i).IsRoot r)
    (hFdeg : ∀ i : Nat, (F i).natDegree ≤ 2) :
    ∀ i : Nat,
      (((F i).roots.filter (x i < ·)).card : ℤ) -
          ((G i).roots.filter (x i < ·)).card ≤ 1 ∧
        (((G i).roots.filter (x i < ·)).card : ℤ) -
          ((F i).roots.filter (x i < ·)).card ≤ 1 := by
  rr_posCombo_sameDegree_rootCountAbove_degree_le_two_sequence using
    left_pos_lc := hF_pos,
    right_pos_lc := hG_pos,
    left_nonneg_coeffs := hFnn,
    right_nonneg_coeffs := hGnn,
    pos_combo := hFG,
    same_degree := hdeg,
    no_common_roots := hno,
    left_degree_le_two := hFdeg

example {F G : Nat → ℝ[X]}
    (hFdeg : ∀ i : Nat, (F i).natDegree ≤ 1) :
    ∀ i : Nat,
      (∀ j, 1 ≤ j → j < (F i).natDegree →
          (rootSeqDesc (G i)).getD j 0 ≤
            (rootSeqDesc (F i)).getD (j - 1) 0) ∧
        (∀ j, 1 ≤ j → j < (F i).natDegree →
          (rootSeqDesc (F i)).getD j 0 ≤
            (rootSeqDesc (G i)).getD (j - 1) 0) := by
  rr_sameDegree_rootCrossing_degree_le_one_sequence using
    left_degree_le_one := hFdeg

example {F G : Nat → ℝ[X]}
    (hF_pos : ∀ i : Nat, HasPosLeadingCoeff (F i))
    (hG_pos : ∀ i : Nat, HasPosLeadingCoeff (G i))
    (hFnn : ∀ i : Nat, HasNonnegCoeffs (F i))
    (hGnn : ∀ i : Nat, HasNonnegCoeffs (G i))
    (hFG : ∀ i : Nat, PosComboRealRooted (F i) (G i))
    (hdeg : ∀ i : Nat, (G i).natDegree = (F i).natDegree)
    (hno : ∀ i : Nat, ∀ r, (F i).IsRoot r → ¬ (G i).IsRoot r)
    (hFdeg : ∀ i : Nat, (F i).natDegree ≤ 2) :
    ∀ i : Nat,
      (∀ j, 1 ≤ j → j < (F i).natDegree →
          (rootSeqDesc (G i)).getD j 0 ≤
            (rootSeqDesc (F i)).getD (j - 1) 0) ∧
        (∀ j, 1 ≤ j → j < (F i).natDegree →
          (rootSeqDesc (F i)).getD j 0 ≤
            (rootSeqDesc (G i)).getD (j - 1) 0) := by
  rr_posCombo_sameDegree_rootCrossing_degree_le_two_sequence using
    left_pos_lc := hF_pos,
    right_pos_lc := hG_pos,
    left_nonneg_coeffs := hFnn,
    right_nonneg_coeffs := hGnn,
    pos_combo := hFG,
    same_degree := hdeg,
    no_common_roots := hno,
    left_degree_le_two := hFdeg

example {F G : Nat → ℝ[X]} {x : Nat → ℝ}
    (hcomp : ∀ i : Nat, Compatible (F i) (G i))
    (hF_pos : ∀ i : Nat, HasPosLeadingCoeff (F i))
    (hG_pos : ∀ i : Nat, HasPosLeadingCoeff (G i))
    (hdeg : ∀ i : Nat, (G i).natDegree = (F i).natDegree + 1)
    (hFsplit : ∀ i : Nat, (F i).Splits)
    (hFdeg : ∀ i : Nat, (F i).natDegree ≤ 2) :
    ∀ i : Nat,
      (((F i).roots.filter (x i < ·)).card : ℤ) -
          ((G i).roots.filter (x i < ·)).card ≤ 2 ∧
        (((G i).roots.filter (x i < ·)).card : ℤ) -
          ((F i).roots.filter (x i < ·)).card ≤ 2 := by
  rr_compatible_succDegree_rootCountAbove_le_two_sequence using
    compatible := hcomp,
    left_pos_lc := hF_pos,
    right_pos_lc := hG_pos,
    succ_degree := hdeg,
    left_splits := hFsplit,
    left_degree_le_two := hFdeg

example {F G : Nat → ℝ[X]} {x : Nat → ℝ}
    (hF_pos : ∀ i : Nat, HasPosLeadingCoeff (F i))
    (hG_pos : ∀ i : Nat, HasPosLeadingCoeff (G i))
    (hFnn : ∀ i : Nat, HasNonnegCoeffs (F i))
    (hGnn : ∀ i : Nat, HasNonnegCoeffs (G i))
    (hFG : ∀ i : Nat, PosComboRealRooted (F i) (G i))
    (hdeg : ∀ i : Nat, (G i).natDegree = (F i).natDegree)
    (hno : ∀ i : Nat, ∀ r, (F i).IsRoot r → ¬ (G i).IsRoot r)
    (hFdeg : ∀ i : Nat, (F i).natDegree ≤ 3) :
    ∀ i : Nat,
      (((F i).roots.filter (· ≤ x i)).card : ℤ) -
          ((G i).roots.filter (· ≤ x i)).card ≤ 1 ∧
        (((G i).roots.filter (· ≤ x i)).card : ℤ) -
          ((F i).roots.filter (· ≤ x i)).card ≤ 1 := by
  rr_posCombo_sameDegree_rootCount_degree_le_three_sequence using
    left_pos_lc := hF_pos,
    right_pos_lc := hG_pos,
    left_nonneg_coeffs := hFnn,
    right_nonneg_coeffs := hGnn,
    pos_combo := hFG,
    same_degree := hdeg,
    no_common_roots := hno,
    left_degree_le_three := hFdeg

example {F G : Nat → ℝ[X]} {x : Nat → ℝ}
    (hF_pos : ∀ i : Nat, HasPosLeadingCoeff (F i))
    (hG_pos : ∀ i : Nat, HasPosLeadingCoeff (G i))
    (hFnn : ∀ i : Nat, HasNonnegCoeffs (F i))
    (hGnn : ∀ i : Nat, HasNonnegCoeffs (G i))
    (hFG : ∀ i : Nat, PosComboRealRooted (F i) (G i))
    (hdeg : ∀ i : Nat, (G i).natDegree = (F i).natDegree)
    (hno : ∀ i : Nat, ∀ r, (F i).IsRoot r → ¬ (G i).IsRoot r)
    (hFdeg : ∀ i : Nat, (F i).natDegree ≤ 3) :
    ∀ i : Nat,
      (((F i).roots.filter (x i < ·)).card : ℤ) -
          ((G i).roots.filter (x i < ·)).card ≤ 1 ∧
        (((G i).roots.filter (x i < ·)).card : ℤ) -
          ((F i).roots.filter (x i < ·)).card ≤ 1 := by
  rr_posCombo_sameDegree_rootCountAbove_degree_le_three_sequence using
    left_pos_lc := hF_pos,
    right_pos_lc := hG_pos,
    left_nonneg_coeffs := hFnn,
    right_nonneg_coeffs := hGnn,
    pos_combo := hFG,
    same_degree := hdeg,
    no_common_roots := hno,
    left_degree_le_three := hFdeg

example {F G : Nat → ℝ[X]}
    (hF_pos : ∀ i : Nat, HasPosLeadingCoeff (F i))
    (hG_pos : ∀ i : Nat, HasPosLeadingCoeff (G i))
    (hFnn : ∀ i : Nat, HasNonnegCoeffs (F i))
    (hGnn : ∀ i : Nat, HasNonnegCoeffs (G i))
    (hFG : ∀ i : Nat, PosComboRealRooted (F i) (G i))
    (hdeg : ∀ i : Nat, (G i).natDegree = (F i).natDegree)
    (hno : ∀ i : Nat, ∀ r, (F i).IsRoot r → ¬ (G i).IsRoot r)
    (hFdeg : ∀ i : Nat, (F i).natDegree ≤ 3) :
    ∀ i : Nat,
      (∀ j, 1 ≤ j → j < (F i).natDegree →
          (rootSeqDesc (G i)).getD j 0 ≤
            (rootSeqDesc (F i)).getD (j - 1) 0) ∧
        (∀ j, 1 ≤ j → j < (F i).natDegree →
          (rootSeqDesc (F i)).getD j 0 ≤
            (rootSeqDesc (G i)).getD (j - 1) 0) := by
  rr_posCombo_sameDegree_rootCrossing_degree_le_three_sequence using
    left_pos_lc := hF_pos,
    right_pos_lc := hG_pos,
    left_nonneg_coeffs := hFnn,
    right_nonneg_coeffs := hGnn,
    pos_combo := hFG,
    same_degree := hdeg,
    no_common_roots := hno,
    left_degree_le_three := hFdeg

end Tactic
end RealRooted
