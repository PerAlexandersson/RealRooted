import RealRooted.CommonInterleaver.SuccDegreeLowDegree
import RealRooted.SameDegreeCountFromAnalytic
import RealRooted.SameDegreeCubicSecondRootFromAnalytic
import RealRooted.Tactic.RootCount.SequenceCore

/-!
# Low-degree root-count endpoints

Sequence lifts and analytic degree-at-most-three endpoints for root counts,
upper-threshold counts, and root crossing.
-/

open Polynomial

namespace RealRooted
namespace Tactic

theorem rightFamily_sameDegree_gt_count_eq_sequence
    {F G : Nat → ℝ[X]} {μ₀ μ₁ x : Nat → ℝ}
    (hFpos : ∀ i : Nat, HasPosLeadingCoeff (F i))
    (hGpos : ∀ i : Nat, HasPosLeadingCoeff (G i))
    (hFG : ∀ i : Nat, PosComboRealRooted (F i) (G i))
    (hdeg : ∀ i : Nat, (G i).natDegree = (F i).natDegree)
    (hμ₀ : ∀ i : Nat, 0 ≤ μ₀ i)
    (hμ₀μ₁ : ∀ i : Nat, μ₀ i ≤ μ₁ i)
    (hne : ∀ i : Nat, ∀ μ ∈ Set.Icc (μ₀ i) (μ₁ i),
      ¬ (F i + C μ * G i).IsRoot (x i)) :
    ∀ i : Nat,
      ((F i + C (μ₀ i) * G i).roots.filter (x i < ·)).card =
        ((F i + C (μ₁ i) * G i).roots.filter (x i < ·)).card := fun i =>
  RealRooted.rightFamily_card_roots_gt_eq_of_no_isRoot_interval_sameDegree
    (hFpos i) (hGpos i) (hFG i) (hdeg i) (hμ₀ i) (hμ₀μ₁ i) (hne i)

theorem rightFamily_zero_one_gt_count_eq_sequence
    {F G : Nat → ℝ[X]} {x : Nat → ℝ}
    (hdeg : ∀ i : Nat, ∀ μ ∈ Set.Icc (0 : ℝ) 1,
      (F i + C μ * G i).natDegree =
        (F i + C (0 : ℝ) * G i).natDegree)
    (hrr : ∀ i : Nat, ∀ μ ∈ Set.Icc (0 : ℝ) 1,
      (F i + C μ * G i).Splits)
    (hne : ∀ i : Nat, ∀ μ ∈ Set.Icc (0 : ℝ) 1,
      ¬ (F i + C μ * G i).IsRoot (x i)) :
    ∀ i : Nat,
      ((F i + C (0 : ℝ) * G i).roots.filter (x i < ·)).card =
        ((F i + C (1 : ℝ) * G i).roots.filter (x i < ·)).card := fun i =>
  RealRooted.rightFamily_card_roots_gt_eq_zero_one_of_constant_degree
    (hdeg i) (hrr i) (hne i)

theorem sameDegree_gt_count_eq_no_rightFamily_sequence
    {F G : Nat → ℝ[X]} {x : Nat → ℝ}
    (hFpos : ∀ i : Nat, HasPosLeadingCoeff (F i))
    (hGpos : ∀ i : Nat, HasPosLeadingCoeff (G i))
    (hFG : ∀ i : Nat, PosComboRealRooted (F i) (G i))
    (hdeg : ∀ i : Nat, (G i).natDegree = (F i).natDegree)
    (hxG : ∀ i : Nat, ¬ (G i).IsRoot (x i))
    (hno : ∀ i : Nat, ∀ {μ : ℝ}, 0 ≤ μ →
      ¬ (F i + C μ * G i).IsRoot (x i)) :
    ∀ i : Nat,
      ((F i).roots.filter (x i < ·)).card =
        ((G i).roots.filter (x i < ·)).card := fun i =>
  RealRooted.sameDegree_card_roots_gt_eq_of_no_rightFamily_isRoot
    (hFpos i) (hGpos i) (hFG i) (hdeg i) (hxG i) (hno i)

theorem sameDegree_rootCountAbove_no_rightFamily_sequence
    {F G : Nat → ℝ[X]} {x : Nat → ℝ}
    (hFpos : ∀ i : Nat, HasPosLeadingCoeff (F i))
    (hGpos : ∀ i : Nat, HasPosLeadingCoeff (G i))
    (hFG : ∀ i : Nat, PosComboRealRooted (F i) (G i))
    (hdeg : ∀ i : Nat, (G i).natDegree = (F i).natDegree)
    (hxG : ∀ i : Nat, ¬ (G i).IsRoot (x i))
    (hno : ∀ i : Nat, ∀ {μ : ℝ}, 0 ≤ μ →
      ¬ (F i + C μ * G i).IsRoot (x i)) :
    ∀ i : Nat,
      (((F i).roots.filter (x i < ·)).card : ℤ) -
          ((G i).roots.filter (x i < ·)).card ≤ 1 ∧
        (((G i).roots.filter (x i < ·)).card : ℤ) -
          ((F i).roots.filter (x i < ·)).card ≤ (1 : ℤ) := fun i =>
  RealRooted.sameDegree_rootCountAbove_pointwise_of_no_rightFamily_isRoot
    (hFpos i) (hGpos i) (hFG i) (hdeg i) (hxG i) (hno i)

theorem sameDegree_rootCountAbove_no_pos_crossing_sequence
    {F G : Nat → ℝ[X]} {x : Nat → ℝ}
    (hFpos : ∀ i : Nat, HasPosLeadingCoeff (F i))
    (hGpos : ∀ i : Nat, HasPosLeadingCoeff (G i))
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
          ((F i).roots.filter (x i < ·)).card ≤ (1 : ℤ) := fun i =>
  RealRooted.sameDegree_rootCountAbove_pointwise_of_not_exists_pos_isRoot
    (hFpos i) (hGpos i) (hFG i) (hdeg i) (hxF i) (hxG i) (hno i)

theorem sameDegree_rootCountAbove_pos_crossing_sequence
    {F G : Nat → ℝ[X]} {x : Nat → ℝ}
    (hFpos : ∀ i : Nat, HasPosLeadingCoeff (F i))
    (hGpos : ∀ i : Nat, HasPosLeadingCoeff (G i))
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
          ((F i).roots.filter (x i < ·)).card ≤ (1 : ℤ) := fun i =>
  RealRooted.sameDegree_rootCountAbove_pointwise_of_exists_pos_isRoot
    (hFpos i) (hGpos i) (hFG i) (hdeg i) (hno i) (hxF i) (hxG i)
    (hcross i)

theorem posCombo_sameDegree_rootCount_degree_le_two_sequence
    {F G : Nat → ℝ[X]} {x : Nat → ℝ}
    (hFpos : ∀ i : Nat, HasPosLeadingCoeff (F i))
    (hGpos : ∀ i : Nat, HasPosLeadingCoeff (G i))
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
          ((F i).roots.filter (· ≤ x i)).card ≤ (1 : ℤ) := fun i =>
  rootCount_diff_le_one_of_posCombo_sameDegree_natDegree_le_two
    (hFpos i) (hGpos i) (hFnn i) (hGnn i) (hFG i) (hdeg i) (hno i)
    (hFdeg i) (x i)

theorem posCombo_sameDegree_rootCountAbove_degree_le_two_sequence
    {F G : Nat → ℝ[X]} {x : Nat → ℝ}
    (hFpos : ∀ i : Nat, HasPosLeadingCoeff (F i))
    (hGpos : ∀ i : Nat, HasPosLeadingCoeff (G i))
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
          ((F i).roots.filter (x i < ·)).card ≤ (1 : ℤ) := fun i =>
  rootCountAbove_diff_le_one_of_posCombo_sameDegree_natDegree_le_two
    (hFpos i) (hGpos i) (hFnn i) (hGnn i) (hFG i) (hdeg i) (hno i)
    (hFdeg i) (x i)

/-- The proved analytic cubic second-root bound closes the degree-`≤ 3`
same-degree root-count route. -/
theorem posCombo_sameDegree_rootCount_degree_le_three
    {f g : ℝ[X]} (x : ℝ)
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
  rcases Nat.le_or_eq_of_le_succ hfdeg with hle | hfdeg3
  · exact rootCount_diff_le_one_of_posCombo_sameDegree_natDegree_le_two
      hf_pos hg_pos hfnn hgnn hfg hdeg hno hle x
  · have hgdeg3 : g.natDegree = 3 := by rw [hdeg, hfdeg3]
    exact sameDegree_cubic_rootCount_le_one_of_secondRootBound
      cubicSecondRootBound_from_analytic hfdeg3 hgdeg3
      (hfg.isRealRooted_left_of_sameDegree hf_pos hg_pos hdeg).2
      (hfg.isRealRooted_right_of_sameDegree hf_pos hg_pos hdeg).2
      hf_pos hg_pos hfg x

/-- Sequence form of `posCombo_sameDegree_rootCount_degree_le_three`. -/
theorem posCombo_sameDegree_rootCount_degree_le_three_sequence
    {F G : Nat → ℝ[X]} {x : Nat → ℝ}
    (hFpos : ∀ i : Nat, HasPosLeadingCoeff (F i))
    (hGpos : ∀ i : Nat, HasPosLeadingCoeff (G i))
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
          ((F i).roots.filter (· ≤ x i)).card ≤ 1 := fun i =>
  posCombo_sameDegree_rootCount_degree_le_three (x i)
    (hFpos i) (hGpos i) (hFnn i) (hGnn i) (hFG i) (hdeg i) (hno i)
    (hFdeg i)

/-- Upper-threshold form of the analytic degree-`≤ 3` root-count route. -/
theorem posCombo_sameDegree_rootCountAbove_degree_le_three
    {f g : ℝ[X]} (x : ℝ)
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
        (f.roots.filter (x < ·)).card ≤ 1 :=
  sameDegreeRootCountAbove_of_rootCount
    (hfg.isRealRooted_left_of_sameDegree hf_pos hg_pos hdeg).2
    (hfg.isRealRooted_right_of_sameDegree hf_pos hg_pos hdeg).2
    hdeg
    (fun y => posCombo_sameDegree_rootCount_degree_le_three y
      hf_pos hg_pos hfnn hgnn hfg hdeg hno hfdeg)
    x

/-- Sequence form of `posCombo_sameDegree_rootCountAbove_degree_le_three`. -/
theorem posCombo_sameDegree_rootCountAbove_degree_le_three_sequence
    {F G : Nat → ℝ[X]} {x : Nat → ℝ}
    (hFpos : ∀ i : Nat, HasPosLeadingCoeff (F i))
    (hGpos : ∀ i : Nat, HasPosLeadingCoeff (G i))
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
          ((F i).roots.filter (x i < ·)).card ≤ 1 := fun i =>
  posCombo_sameDegree_rootCountAbove_degree_le_three (x i)
    (hFpos i) (hGpos i) (hFnn i) (hGnn i) (hFG i) (hdeg i) (hno i)
    (hFdeg i)

/-- Root-crossing form of the analytic degree-`≤ 3` route. -/
theorem posCombo_sameDegree_rootCrossing_degree_le_three
    {f g : ℝ[X]}
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
        (rootSeqDesc f).getD j 0 ≤ (rootSeqDesc g).getD (j - 1) 0) :=
  rootCrossing_of_rootCountAbove_diff_le_one
    (hfg.isRealRooted_left_of_sameDegree hf_pos hg_pos hdeg).2
    (hfg.isRealRooted_right_of_sameDegree hf_pos hg_pos hdeg).2
    hdeg
    (fun x => posCombo_sameDegree_rootCountAbove_degree_le_three x
      hf_pos hg_pos hfnn hgnn hfg hdeg hno hfdeg)

/-- Sequence form of `posCombo_sameDegree_rootCrossing_degree_le_three`. -/
theorem posCombo_sameDegree_rootCrossing_degree_le_three_sequence
    {F G : Nat → ℝ[X]}
    (hFpos : ∀ i : Nat, HasPosLeadingCoeff (F i))
    (hGpos : ∀ i : Nat, HasPosLeadingCoeff (G i))
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
            (rootSeqDesc (G i)).getD (j - 1) 0) := fun i =>
  posCombo_sameDegree_rootCrossing_degree_le_three
    (hFpos i) (hGpos i) (hFnn i) (hGnn i) (hFG i) (hdeg i) (hno i)
    (hFdeg i)

theorem sameDegree_rootCrossing_degree_le_one_sequence
    {F G : Nat → ℝ[X]}
    (hFdeg : ∀ i : Nat, (F i).natDegree ≤ 1) :
    ∀ i : Nat,
      (∀ j, 1 ≤ j → j < (F i).natDegree →
          (rootSeqDesc (G i)).getD j 0 ≤
            (rootSeqDesc (F i)).getD (j - 1) 0) ∧
        (∀ j, 1 ≤ j → j < (F i).natDegree →
          (rootSeqDesc (F i)).getD j 0 ≤
            (rootSeqDesc (G i)).getD (j - 1) 0) := fun i =>
  sameDegreeRootCrossing_of_natDegree_le_one (hFdeg i)

theorem posCombo_sameDegree_rootCrossing_degree_le_two_sequence
    {F G : Nat → ℝ[X]}
    (hFpos : ∀ i : Nat, HasPosLeadingCoeff (F i))
    (hGpos : ∀ i : Nat, HasPosLeadingCoeff (G i))
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
            (rootSeqDesc (G i)).getD (j - 1) 0) := fun i =>
  sameDegreeRootCrossing_of_posCombo_natDegree_le_two
    (hFpos i) (hGpos i) (hFnn i) (hGnn i) (hFG i) (hdeg i) (hno i)
    (hFdeg i)

theorem compatible_succDegree_rootCountAbove_le_two_sequence
    {F G : Nat → ℝ[X]} {x : Nat → ℝ}
    (hcomp : ∀ i : Nat, Compatible (F i) (G i))
    (hFpos : ∀ i : Nat, HasPosLeadingCoeff (F i))
    (hGpos : ∀ i : Nat, HasPosLeadingCoeff (G i))
    (hdeg : ∀ i : Nat, (G i).natDegree = (F i).natDegree + 1)
    (hFsplit : ∀ i : Nat, (F i).Splits)
    (hFdeg : ∀ i : Nat, (F i).natDegree ≤ 2) :
    ∀ i : Nat,
      (((F i).roots.filter (x i < ·)).card : ℤ) -
          ((G i).roots.filter (x i < ·)).card ≤ 2 ∧
        (((G i).roots.filter (x i < ·)).card : ℤ) -
          ((F i).roots.filter (x i < ·)).card ≤ (2 : ℤ) := fun i =>
  compatibleSuccDegreeRootCountAbove_le_two_of_natDegree_le_two
    (hcomp i) (hFpos i) (hGpos i) (hdeg i) (hFsplit i) (hFdeg i) (x i)

theorem posCombo_sameDegree_rootCount_cubicInterior_sequence
    {F G : Nat → ℝ[X]} {x : Nat → ℝ}
    (hbelow : CubicInteriorTwoBelowStatement)
    (habove : CubicInteriorTwoAboveStatement)
    (hFpos : ∀ i : Nat, HasPosLeadingCoeff (F i))
    (hGpos : ∀ i : Nat, HasPosLeadingCoeff (G i))
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
          ((F i).roots.filter (· ≤ x i)).card ≤ (1 : ℤ) := fun i =>
  rootCount_diff_le_one_of_posCombo_sameDegree_natDegree_le_three_of_cubicInterior
    hbelow habove (hFpos i) (hGpos i) (hFnn i) (hGnn i) (hFG i)
    (hdeg i) (hno i) (hFdeg i) (x i)

theorem posCombo_sameDegree_rootCountAbove_cubicInterior_sequence
    {F G : Nat → ℝ[X]} {x : Nat → ℝ}
    (hbelow : CubicInteriorTwoBelowStatement)
    (habove : CubicInteriorTwoAboveStatement)
    (hFpos : ∀ i : Nat, HasPosLeadingCoeff (F i))
    (hGpos : ∀ i : Nat, HasPosLeadingCoeff (G i))
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
          ((F i).roots.filter (x i < ·)).card ≤ (1 : ℤ) := fun i =>
  rootCountAbove_diff_le_one_of_posCombo_sameDegree_natDegree_le_three_of_cubicInterior
    hbelow habove (hFpos i) (hGpos i) (hFnn i) (hGnn i) (hFG i)
    (hdeg i) (hno i) (hFdeg i) (x i)

theorem posCombo_sameDegree_rootCrossing_cubicInterior_sequence
    {F G : Nat → ℝ[X]}
    (hbelow : CubicInteriorTwoBelowStatement)
    (habove : CubicInteriorTwoAboveStatement)
    (hFpos : ∀ i : Nat, HasPosLeadingCoeff (F i))
    (hGpos : ∀ i : Nat, HasPosLeadingCoeff (G i))
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
            (rootSeqDesc (G i)).getD (j - 1) 0) := fun i =>
  sameDegreeRootCrossing_of_posCombo_natDegree_le_three_of_cubicInterior
    hbelow habove (hFpos i) (hGpos i) (hFnn i) (hGnn i) (hFG i)
    (hdeg i) (hno i) (hFdeg i)

end Tactic
end RealRooted
