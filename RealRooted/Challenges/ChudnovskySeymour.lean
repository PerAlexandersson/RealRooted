import RealRooted.ChudnovskySeymour
import RealRooted.CommonInterleaverSeq
import RealRooted.SuccDegreeRootCrossing

/-!
# Chudnovsky--Seymour challenge entry point

This module exposes the roadmap target statements and a small solved
low-degree package for the Chudnovsky--Seymour compatibility/common-interleaver
machinery.
-/

open Polynomial

noncomputable section

namespace RealRooted
namespace Challenges
namespace ChudnovskySeymour

/-- Four-way compatibility/common-interleaver package for a finite family. -/
abbrev fourWayPackage (fs : List ℝ[X]) : Prop :=
  ChudnovskySeymourFourWayPackage fs

/-- Challenge-facing projection from the four-way package to `1 ↔ 2`. -/
theorem pairwiseCompatible_iff_pairwiseHasCommonInterleaver_of_fourWay
    {fs : List ℝ[X]}
    (hfour : fourWayPackage fs) :
    PairwiseCompatible fs ↔ PairwiseHasCommonInterleaver fs :=
  RealRooted.pairwiseCompatible_iff_pairwiseHasCommonInterleaver_of_fourWay hfour

/-- Challenge-facing projection from the four-way package to `2 ↔ 3`. -/
theorem pairwiseHasCommonInterleaver_iff_commonInterleaver_of_fourWay
    {fs : List ℝ[X]}
    (hfour : fourWayPackage fs) :
    PairwiseHasCommonInterleaver fs ↔ HasCommonInterleaver fs :=
  RealRooted.pairwiseHasCommonInterleaver_iff_hasCommonInterleaver_of_fourWay hfour

/-- Challenge-facing projection from the four-way package to `3 ↔ 4`. -/
theorem commonInterleaver_iff_familyCompatible_of_fourWay
    {fs : List ℝ[X]}
    (hfour : fourWayPackage fs) :
    HasCommonInterleaver fs ↔ FamilyCompatible fs :=
  RealRooted.hasCommonInterleaver_iff_familyCompatible_of_fourWay hfour

/-- Challenge-facing projection from the four-way package to `1 ↔ 3`. -/
theorem pairwiseCompatible_iff_commonInterleaver_of_fourWay
    {fs : List ℝ[X]}
    (hfour : fourWayPackage fs) :
    PairwiseCompatible fs ↔ HasCommonInterleaver fs :=
  RealRooted.pairwiseCompatible_iff_hasCommonInterleaver_of_fourWay hfour

/-- Challenge-facing projection from the four-way package to `1 ↔ 4`. -/
theorem pairwiseCompatible_iff_familyCompatible_of_fourWay
    {fs : List ℝ[X]}
    (hfour : fourWayPackage fs) :
    PairwiseCompatible fs ↔ FamilyCompatible fs :=
  (pairwiseCompatible_iff_commonInterleaver_of_fourWay hfour).trans
    (commonInterleaver_iff_familyCompatible_of_fourWay hfour)

/-- Roadmap target for pairwise compatibility versus common left interleavers. -/
abbrev commonLeftInterleaverTarget : Prop :=
  chudnovskySeymour_pairwiseCompatible_iff_commonLeftInterleaver_target

/-- Roadmap target for pairwise compatibility versus common right interleavers. -/
abbrev commonInterleaverTarget : Prop :=
  chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_target

/-- Roadmap target for the nonnegative-coefficient common right interleaver
form. -/
abbrev commonInterleaverNonnegCoeffsTarget : Prop :=
  chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_nonnegCoeffs_target

/-- Roadmap target for the nonnegative-coefficient finite-family compatibility
form. -/
abbrev familyCompatibleNonnegCoeffsTarget : Prop :=
  chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_nonnegCoeffs_target

/-- Roadmap target for the nonnegative-coefficient four-way package. -/
abbrev fourWayNonnegCoeffsTarget : Prop :=
  chudnovskySeymour_fourWay_nonnegCoeffs_target

/-! ## Pair endpoint targets for milestones B1 and B2 -/

/-- Milestone B1 (#41): repaired same-degree no-common pair endpoint. -/
abbrev sameDegreePairTarget : Prop :=
  PosComboNoCommonSameDegreePairHasCommonInterleaverNonnegStatement

/-- Strong same-degree orientation alternative used by several reductions. -/
abbrev sameDegreeOrientationAlternativeTarget : Prop :=
  PosComboNoCommonSameDegreeOrientationAlternativeNonnegStatement

/-- Same-degree root-slot reformulation of milestone B1. -/
abbrev sameDegreeSlotDataTarget : Prop :=
  PosComboNoCommonSameDegreeSlotDataNonnegStatement

/-- Same-degree descending-root crossing subtarget for milestone B1. -/
abbrev sameDegreeRootCrossingTarget : Prop :=
  PosComboNoCommonSameDegreeRootCrossingNonnegStatement

/-- Same-degree analytic root-count subtarget for milestone B1. -/
abbrev sameDegreeRootCountTarget : Prop :=
  PosComboNoCommonSameDegreeRootCountNonnegStatement

/-- Same-degree upper-threshold root-count subtarget for milestone B1. -/
abbrev sameDegreeRootCountAboveTarget : Prop :=
  PosComboNoCommonSameDegreeRootCountAboveNonnegStatement

/-- Same-degree lower root-count subtarget restricted to common non-root
thresholds. -/
abbrev sameDegreeRootCountNonRootTarget : Prop :=
  PosComboNoCommonSameDegreeRootCountNonRootNonnegStatement

/-- Same-degree upper root-count subtarget restricted to common non-root
thresholds. -/
abbrev sameDegreeRootCountAboveNonRootTarget : Prop :=
  PosComboNoCommonSameDegreeRootCountAboveNonRootNonnegStatement

/-- Milestone B2 (#42): repaired succ-degree no-common pair endpoint. -/
abbrev succDegreePairTarget : Prop :=
  PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement

/-- Strong fixed-orientation succ-degree endpoint. -/
abbrev succDegreeOrientationTarget : Prop :=
  PosComboNoCommonSuccDegreeOrientationNonnegStatement

/-- Succ-degree left-endpoint real-rootedness subtarget. -/
abbrev succDegreeLeftSplitsTarget : Prop :=
  PosComboSuccDegreeLeftSplitsNonnegStatement

/-- Residual succ-degree left-endpoint target after removing the nonzero
constant-term and common-`X` branches. -/
abbrev succDegreeResidualLeftSplitsTarget : Prop :=
  PosComboSuccDegreeResidualLeftSplitsNonnegStatement

/-- Zero-aware forward Aissen--Schoenberg--Whitney target used by the PF-limit
left-endpoint route. -/
abbrev forwardASWTarget : Prop :=
  aissenSchoenbergWhitneyForwardOrZeroStatement

/-- Splitting-only forward Aissen--Schoenberg--Whitney target; this is now
equivalent to the zero-aware target used by the PF-limit route. -/
abbrev forwardASWSplitsTarget : Prop :=
  aissenSchoenbergWhitneyForwardSplitsStatement

/-- Affine-family bridge target for packaging the no-common nonnegative
positive-combination hypotheses into Branden's affine-family input. -/
abbrev affineFamilyTarget : Prop :=
  PosComboNoCommonAffineFamilyStatement

/-- Boundary-right-pair orientation target; this is a stronger sufficient
condition for the affine-family bridge. -/
abbrev boundaryRightPairOrientationTarget : Prop :=
  PosComboNoCommonBoundaryRightPairOrientationStatement

/-- Succ-degree root-slot reformulation of milestone B2. -/
abbrev succDegreeSlotDataTarget : Prop :=
  PosComboNoCommonSuccDegreeSlotDataNonnegStatement

/-- Succ-degree descending-root crossing subtarget for milestone B2. -/
abbrev succDegreeRootCrossingTarget : Prop :=
  PosComboNoCommonSuccDegreeRootCrossingNonnegStatement

/-- Succ-degree analytic root-count subtarget for milestone B2. -/
abbrev succDegreeRootCountTarget : Prop :=
  PosComboNoCommonSuccDegreeRootCountNonnegStatement

/-- Succ-degree upper-threshold root-count subtarget for milestone B2. -/
abbrev succDegreeRootCountAboveTarget : Prop :=
  PosComboNoCommonSuccDegreeRootCountAboveNonnegStatement

/-- Succ-degree upper-threshold root-count subtarget restricted to common
non-root thresholds. -/
abbrev succDegreeRootCountAboveNonRootTarget : Prop :=
  PosComboNoCommonSuccDegreeRootCountAboveNonRootNonnegStatement

/-- Succ-degree residual constant-term root-count branch. -/
abbrev succDegreeRootCountResidualTarget : Prop :=
  PosComboNoCommonSuccDegreeRootCountResidualNonnegStatement

/-- Succ-degree nonzero constant-term root-count branch. -/
abbrev succDegreeRootCountLeadTarget : Prop :=
  PosComboNoCommonSuccDegreeRootCountLeadNonnegStatement

/-- Challenge-facing equivalence between the same-degree slot-data target and
the repaired same-degree pair endpoint. -/
theorem sameDegreeSlotDataTarget_iff_pairTarget :
    sameDegreeSlotDataTarget ↔ sameDegreePairTarget :=
  posComboNoCommonSameDegreeSlotData_iff_pairHasCommonInterleaver

/-- Challenge-facing reduction from same-degree slot data to the repaired
same-degree pair endpoint. -/
theorem sameDegreePairTarget_of_slotData
    (hslot : sameDegreeSlotDataTarget) :
    sameDegreePairTarget :=
  sameDegreePairHasCommonInterleaver_nonneg_of_slotData hslot

/-- Challenge-facing reduction from same-degree root crossing to slot data. -/
theorem sameDegreeSlotDataTarget_of_rootCrossing
    (hcross : sameDegreeRootCrossingTarget) :
    sameDegreeSlotDataTarget :=
  posComboNoCommonSameDegreeSlotData_of_rootCrossing hcross

/-- Challenge-facing reduction from same-degree root crossing to the repaired
same-degree pair endpoint. -/
theorem sameDegreePairTarget_of_rootCrossing
    (hcross : sameDegreeRootCrossingTarget) :
    sameDegreePairTarget :=
  sameDegreePairHasCommonInterleaver_nonneg_of_rootCrossing hcross

/-- Challenge-facing reduction from same-degree root counts to same-degree
root crossing. -/
theorem sameDegreeRootCrossingTarget_of_rootCount
    (hcount : sameDegreeRootCountTarget) :
    sameDegreeRootCrossingTarget :=
  posComboNoCommonSameDegreeRootCrossing_of_rootCount hcount

/-- Challenge-facing reduction from same-degree upper-threshold root counts to
same-degree root crossing. -/
theorem sameDegreeRootCrossingTarget_of_rootCountAbove
    (hcount : sameDegreeRootCountAboveTarget) :
    sameDegreeRootCrossingTarget :=
  posComboNoCommonSameDegreeRootCrossing_of_rootCountAbove hcount

/-- Challenge-facing conversion from same-degree upper-threshold root counts to
the lower-threshold formulation. -/
theorem sameDegreeRootCountTarget_of_rootCountAbove
    (hcount : sameDegreeRootCountAboveTarget) :
    sameDegreeRootCountTarget :=
  posComboNoCommonSameDegreeRootCount_of_rootCountAbove hcount

/-- Challenge-facing conversion from same-degree lower-threshold root counts to
the upper-threshold formulation. -/
theorem sameDegreeRootCountAboveTarget_of_rootCount
    (hcount : sameDegreeRootCountTarget) :
    sameDegreeRootCountAboveTarget :=
  posComboNoCommonSameDegreeRootCountAbove_of_rootCount hcount

/-- Challenge-facing reduction from common-non-root same-degree lower root
counts to the full lower-threshold formulation. -/
theorem sameDegreeRootCountTarget_of_nonRoot
    (hcount : sameDegreeRootCountNonRootTarget) :
    sameDegreeRootCountTarget :=
  posComboNoCommonSameDegreeRootCount_of_nonRoot hcount

/-- Challenge-facing reduction from common-non-root same-degree upper root
counts to the full upper-threshold formulation. -/
theorem sameDegreeRootCountAboveTarget_of_nonRoot
    (hcount : sameDegreeRootCountAboveNonRootTarget) :
    sameDegreeRootCountAboveTarget :=
  posComboNoCommonSameDegreeRootCountAbove_of_nonRoot hcount

/-- Challenge-facing reduction from same-degree root counts to slot data. -/
theorem sameDegreeSlotDataTarget_of_rootCount
    (hcount : sameDegreeRootCountTarget) :
    sameDegreeSlotDataTarget :=
  posComboNoCommonSameDegreeSlotData_of_rootCount hcount

/-- Challenge-facing reduction from same-degree upper-threshold root counts to
slot data. -/
theorem sameDegreeSlotDataTarget_of_rootCountAbove
    (hcount : sameDegreeRootCountAboveTarget) :
    sameDegreeSlotDataTarget :=
  posComboNoCommonSameDegreeSlotData_of_rootCountAbove hcount

/-- Challenge-facing reduction from same-degree root counts to the repaired
same-degree pair endpoint. -/
theorem sameDegreePairTarget_of_rootCount
    (hcount : sameDegreeRootCountTarget) :
    sameDegreePairTarget :=
  sameDegreePairHasCommonInterleaver_nonneg_of_rootCount hcount

/-- Challenge-facing reduction from same-degree upper-threshold root counts to
the repaired same-degree pair endpoint. -/
theorem sameDegreePairTarget_of_rootCountAbove
    (hcount : sameDegreeRootCountAboveTarget) :
    sameDegreePairTarget :=
  sameDegreePairHasCommonInterleaver_nonneg_of_rootCountAbove hcount

/-- Challenge-facing reduction from the same-degree orientation alternative to
same-degree root crossing. -/
theorem sameDegreeRootCrossingTarget_of_orientationAlternative
    (horient : sameDegreeOrientationAlternativeTarget) :
    sameDegreeRootCrossingTarget :=
  posComboNoCommonSameDegreeRootCrossing_of_orientationAlternative horient

/-- Challenge-facing low-degree base case for the same-degree root-crossing
inequalities. -/
theorem sameDegreeRootCrossingPair_of_natDegree_le_one
    {f g : ℝ[X]} (hf_deg_le_one : f.natDegree ≤ 1) :
    (∀ j, 1 ≤ j → j < f.natDegree →
        (rootSeqDesc g).getD j 0 ≤ (rootSeqDesc f).getD (j - 1) 0) ∧
    (∀ j, 1 ≤ j → j < f.natDegree →
        (rootSeqDesc f).getD j 0 ≤ (rootSeqDesc g).getD (j - 1) 0) :=
  sameDegreeRootCrossing_of_natDegree_le_one hf_deg_le_one

/-- Challenge-facing low-degree base case for the same-degree root-count
formulation. -/
theorem sameDegreeRootCountPair_of_natDegree_le_one
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hdeg : g.natDegree = f.natDegree) (hf_deg_le_one : f.natDegree ≤ 1) (x : ℝ) :
      ((f.roots.filter (· ≤ x)).card : ℤ) - (g.roots.filter (· ≤ x)).card ≤ 1 ∧
      ((g.roots.filter (· ≤ x)).card : ℤ) - (f.roots.filter (· ≤ x)).card ≤ 1 :=
  rootCount_diff_le_one_of_natDegree_le_one hf hg hdeg hf_deg_le_one x

/-- Challenge-facing low-degree base case for the upper-threshold same-degree
root-count formulation. -/
theorem sameDegreeRootCountAbovePair_of_natDegree_le_one
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hdeg : g.natDegree = f.natDegree) (hf_deg_le_one : f.natDegree ≤ 1) (x : ℝ) :
      ((f.roots.filter (x < ·)).card : ℤ) - (g.roots.filter (x < ·)).card ≤ 1 ∧
      ((g.roots.filter (x < ·)).card : ℤ) - (f.roots.filter (x < ·)).card ≤ 1 :=
  rootCountAbove_diff_le_one_of_natDegree_le_one hf hg hdeg hf_deg_le_one x

/-- Challenge-facing low-degree base case for the repaired same-degree
pair-interleaver endpoint. -/
theorem sameDegreePairHasCommonInterleaver_of_natDegree_le_one
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hdeg : g.natDegree = f.natDegree)
    (hf_deg_le_one : f.natDegree ≤ 1) :
    ∃ h : ℝ[X], Prec f h ∧ Prec g h :=
  posComboNoCommonSameDegreePairHasCommonInterleaver_of_degree_le_one
    hf_pos hg_pos hdeg hf_deg_le_one

/-- Challenge-facing low-degree base case for same-degree root-slot data. -/
theorem sameDegreeSlotDataPair_of_natDegree_le_one
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hdeg : g.natDegree = f.natDegree)
    (hf_deg_le_one : f.natDegree ≤ 1) :
    ∀ j, j < f.natDegree + 1 →
      ∀ (hjf : j < (rootSeqDesc f).length + 1)
        (hjg : j < (rootSeqDesc g).length + 1),
        (rootSlotInterval (rootSeqDesc f) ⟨j, hjf⟩ ∩
          rootSlotInterval (rootSeqDesc g) ⟨j, hjg⟩).Nonempty :=
  sameDegreeSlotData_of_natDegree_le_one
    hf_pos hg_pos hdeg hf_deg_le_one

/-- Challenge-facing reduction from the same-degree orientation alternative to
the repaired same-degree pair endpoint. -/
theorem sameDegreePairTarget_of_orientationAlternative
    (horient : sameDegreeOrientationAlternativeTarget) :
    sameDegreePairTarget :=
  posComboNoCommonSameDegreePairHasCommonInterleaver_of_orientationAlternative_nonneg
    horient

/-- Challenge-facing equivalence between the succ-degree slot-data target and
the repaired succ-degree pair endpoint. -/
theorem succDegreeSlotDataTarget_iff_pairTarget :
    succDegreeSlotDataTarget ↔ succDegreePairTarget :=
  posComboNoCommonSuccDegreeSlotData_iff_pairHasCommonInterleaver

/-- Challenge-facing reduction from succ-degree slot data to the repaired
succ-degree pair endpoint. -/
theorem succDegreePairTarget_of_slotData
    (hslot : succDegreeSlotDataTarget) :
    succDegreePairTarget :=
  succDegreePairHasCommonInterleaver_nonneg_of_slotData hslot

/-- Challenge-facing reduction from the fixed succ-degree orientation to
succ-degree root crossing. -/
theorem succDegreeRootCrossingTarget_of_orientation
    (horient : succDegreeOrientationTarget) :
    succDegreeRootCrossingTarget :=
  posComboNoCommonSuccDegreeRootCrossing_of_orientation horient

/-- Challenge-facing reduction from the fixed succ-degree orientation to
upper-threshold succ-degree root counts. -/
theorem succDegreeRootCountAboveTarget_of_orientation
    (horient : succDegreeOrientationTarget) :
    succDegreeRootCountAboveTarget :=
  posComboNoCommonSuccDegreeRootCountAbove_of_orientation horient

/-- Challenge-facing reduction from the fixed succ-degree orientation to
lower-threshold succ-degree root counts. -/
theorem succDegreeRootCountTarget_of_orientation
    (horient : succDegreeOrientationTarget) :
    succDegreeRootCountTarget :=
  posComboNoCommonSuccDegreeRootCount_of_orientation horient

/-- Challenge-facing reduction from succ-degree root counts to succ-degree
root crossing. -/
theorem succDegreeRootCrossingTarget_of_rootCount
    (hcount : succDegreeRootCountTarget) :
    succDegreeRootCrossingTarget :=
  posComboNoCommonSuccDegreeRootCrossing_of_rootCount hcount

/-- Challenge-facing reduction from upper-threshold succ-degree root counts to
succ-degree root crossing. -/
theorem succDegreeRootCrossingTarget_of_rootCountAbove
    (hcount : succDegreeRootCountAboveTarget) :
    succDegreeRootCrossingTarget :=
  posComboNoCommonSuccDegreeRootCrossing_of_rootCountAbove hcount

/-- Challenge-facing conversion from upper-threshold succ-degree root counts
to lower-threshold succ-degree root counts. -/
theorem succDegreeRootCountTarget_of_rootCountAbove
    (hcount : succDegreeRootCountAboveTarget) :
    succDegreeRootCountTarget :=
  posComboNoCommonSuccDegreeRootCount_of_rootCountAbove hcount

/-- Challenge-facing conversion from lower-threshold succ-degree root counts
to upper-threshold succ-degree root counts. -/
theorem succDegreeRootCountAboveTarget_of_rootCount
    (hcount : succDegreeRootCountTarget) :
    succDegreeRootCountAboveTarget :=
  posComboNoCommonSuccDegreeRootCountAbove_of_rootCount hcount

/-- Challenge-facing reduction from common-non-root succ-degree upper root
counts to the full upper-threshold formulation. -/
theorem succDegreeRootCountAboveTarget_of_nonRoot
    (hcount : succDegreeRootCountAboveNonRootTarget) :
    succDegreeRootCountAboveTarget :=
  posComboNoCommonSuccDegreeRootCountAbove_of_nonRoot hcount

/-- Challenge-facing reduction from common-non-root succ-degree upper root
counts to the lower-threshold formulation. -/
theorem succDegreeRootCountTarget_of_nonRoot
    (hcount : succDegreeRootCountAboveNonRootTarget) :
    succDegreeRootCountTarget :=
  posComboNoCommonSuccDegreeRootCount_of_nonRoot hcount

/-- Challenge-facing reduction from the succ-degree constant-term branches to
the full lower-threshold root-count formulation. -/
theorem succDegreeRootCountTarget_of_residual_and_lead
    (hlead : succDegreeRootCountLeadTarget)
    (hres : succDegreeRootCountResidualTarget) :
    succDegreeRootCountTarget :=
  posComboNoCommonSuccDegreeRootCount_of_residual_and_lead hlead hres

/-- Challenge-facing reduction from the succ-degree constant-term branches to
the upper-threshold root-count formulation. -/
theorem succDegreeRootCountAboveTarget_of_residual_and_lead
    (hlead : succDegreeRootCountLeadTarget)
    (hres : succDegreeRootCountResidualTarget) :
    succDegreeRootCountAboveTarget :=
  posComboNoCommonSuccDegreeRootCountAbove_of_residual_and_lead hlead hres

/-- Challenge-facing reduction from the succ-degree constant-term branches to
root crossing. -/
theorem succDegreeRootCrossingTarget_of_residual_and_lead
    (hlead : succDegreeRootCountLeadTarget)
    (hres : succDegreeRootCountResidualTarget) :
    succDegreeRootCrossingTarget :=
  posComboNoCommonSuccDegreeRootCrossing_of_residual_and_lead hlead hres

/-- Challenge-facing reduction from succ-degree root counts to slot data. -/
theorem succDegreeSlotDataTarget_of_rootCount
    (hcount : succDegreeRootCountTarget) :
    succDegreeSlotDataTarget :=
  posComboNoCommonSuccDegreeSlotData_of_rootCount hcount

/-- Challenge-facing reduction from succ-degree upper-threshold root counts to
slot data. -/
theorem succDegreeSlotDataTarget_of_rootCountAbove
    (hcount : succDegreeRootCountAboveTarget) :
    succDegreeSlotDataTarget :=
  posComboNoCommonSuccDegreeSlotData_of_rootCountAbove hcount

/-- Challenge-facing reduction from common-non-root succ-degree upper root
counts to slot data. -/
theorem succDegreeSlotDataTarget_of_nonRoot
    (hcount : succDegreeRootCountAboveNonRootTarget) :
    succDegreeSlotDataTarget :=
  posComboNoCommonSuccDegreeSlotData_of_nonRoot hcount

/-- Challenge-facing reduction from the succ-degree constant-term branches to
slot data. -/
theorem succDegreeSlotDataTarget_of_residual_and_lead
    (hlead : succDegreeRootCountLeadTarget)
    (hres : succDegreeRootCountResidualTarget) :
    succDegreeSlotDataTarget :=
  posComboNoCommonSuccDegreeSlotData_of_residual_and_lead hlead hres

/-- Challenge-facing reduction from succ-degree root counts to the repaired
succ-degree pair endpoint. -/
theorem succDegreePairTarget_of_rootCount
    (hcount : succDegreeRootCountTarget) :
    succDegreePairTarget :=
  succDegreePairHasCommonInterleaver_nonneg_of_rootCount hcount

/-- Challenge-facing reduction from succ-degree upper-threshold root counts to
the repaired succ-degree pair endpoint. -/
theorem succDegreePairTarget_of_rootCountAbove
    (hcount : succDegreeRootCountAboveTarget) :
    succDegreePairTarget :=
  succDegreePairHasCommonInterleaver_nonneg_of_rootCountAbove hcount

/-- Challenge-facing reduction from common-non-root succ-degree upper root
counts to the repaired succ-degree pair endpoint. -/
theorem succDegreePairTarget_of_nonRoot
    (hcount : succDegreeRootCountAboveNonRootTarget) :
    succDegreePairTarget :=
  succDegreePairHasCommonInterleaver_nonneg_of_nonRoot hcount

/-- Challenge-facing reduction from the succ-degree constant-term branches to
the repaired succ-degree pair endpoint. -/
theorem succDegreePairTarget_of_residual_and_lead
    (hlead : succDegreeRootCountLeadTarget)
    (hres : succDegreeRootCountResidualTarget) :
    succDegreePairTarget :=
  succDegreePairHasCommonInterleaver_nonneg_of_residual_and_lead hlead hres

/-- Challenge-facing degree-zero base case for the succ-degree root-crossing
inequalities. -/
theorem succDegreeRootCrossingPair_of_natDegree_eq_zero
    {f g : ℝ[X]} (hf_deg0 : f.natDegree = 0) :
    (∀ j, 1 ≤ j → j ≤ f.natDegree →
        (rootSeqDesc g).getD j 0 ≤ (rootSeqDesc f).getD (j - 1) 0) ∧
    (∀ j, 1 ≤ j → j < f.natDegree →
        (rootSeqDesc f).getD j 0 ≤ (rootSeqDesc g).getD (j - 1) 0) :=
  succDegreeRootCrossing_of_natDegree_eq_zero hf_deg0

/-- Challenge-facing degree-zero base case for the succ-degree root-count
formulation. -/
theorem succDegreeRootCountPair_of_natDegree_eq_zero
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hdeg : g.natDegree = f.natDegree + 1) (hf_deg0 : f.natDegree = 0) (x : ℝ) :
      ((f.roots.filter (· ≤ x)).card : ℤ) - (g.roots.filter (· ≤ x)).card ≤ 0 ∧
      ((g.roots.filter (· ≤ x)).card : ℤ) - (f.roots.filter (· ≤ x)).card ≤ 2 :=
  succDegreeRootCount_of_natDegree_eq_zero hf hg hdeg hf_deg0 x

/-- Challenge-facing degree-zero base case for the upper-threshold succ-degree
root-count formulation. -/
theorem succDegreeRootCountAbovePair_of_natDegree_eq_zero
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hdeg : g.natDegree = f.natDegree + 1) (hf_deg0 : f.natDegree = 0) (x : ℝ) :
      ((f.roots.filter (x < ·)).card : ℤ) - (g.roots.filter (x < ·)).card ≤ 1 ∧
      ((g.roots.filter (x < ·)).card : ℤ) - (f.roots.filter (x < ·)).card ≤ 1 :=
  succDegreeRootCountAbove_of_natDegree_eq_zero hf hg hdeg hf_deg0 x

/-- Challenge-facing degree-one base case for the upper-threshold succ-degree
root-count formulation in the positive-combination/no-common setting. -/
theorem succDegreeRootCountAbovePair_of_posCombo_natDegree_eq_one
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f) (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g)
    (hdeg : g.natDegree = f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hf : f.Splits) (hf_deg1 : f.natDegree = 1) (x : ℝ) :
      ((f.roots.filter (x < ·)).card : ℤ) - (g.roots.filter (x < ·)).card ≤ 1 ∧
      ((g.roots.filter (x < ·)).card : ℤ) - (f.roots.filter (x < ·)).card ≤ 1 :=
  succDegreeRootCountAbove_of_posCombo_natDegree_eq_one
    hf_pos hg_pos hfnn hgnn hfg hdeg hno hf hf_deg1 x

/-- Challenge-facing degree-one base case for the lower-threshold succ-degree
root-count formulation in the positive-combination/no-common setting. -/
theorem succDegreeRootCountPair_of_posCombo_natDegree_eq_one
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f) (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g)
    (hdeg : g.natDegree = f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hf : f.Splits) (hf_deg1 : f.natDegree = 1) (x : ℝ) :
      ((f.roots.filter (· ≤ x)).card : ℤ) - (g.roots.filter (· ≤ x)).card ≤ 0 ∧
      ((g.roots.filter (· ≤ x)).card : ℤ) - (f.roots.filter (· ≤ x)).card ≤ 2 :=
  succDegreeRootCount_of_posCombo_natDegree_eq_one
    hf_pos hg_pos hfnn hgnn hfg hdeg hno hf hf_deg1 x

/-- Challenge-facing degree-one base case for the succ-degree root-crossing
inequalities in the positive-combination/no-common setting. -/
theorem succDegreeRootCrossingPair_of_posCombo_natDegree_eq_one
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f) (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g)
    (hdeg : g.natDegree = f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hf : f.Splits) (hf_deg1 : f.natDegree = 1) :
    (∀ j, 1 ≤ j → j ≤ f.natDegree →
        (rootSeqDesc g).getD j 0 ≤ (rootSeqDesc f).getD (j - 1) 0) ∧
    (∀ j, 1 ≤ j → j < f.natDegree →
        (rootSeqDesc f).getD j 0 ≤ (rootSeqDesc g).getD (j - 1) 0) :=
  succDegreeRootCrossing_of_posCombo_natDegree_eq_one
    hf_pos hg_pos hfnn hgnn hfg hdeg hno hf hf_deg1

/-- Challenge-facing low-degree base case for the upper-threshold succ-degree
root-count formulation in the positive-combination/no-common setting. -/
theorem succDegreeRootCountAbovePair_of_posCombo_natDegree_le_one
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f) (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g)
    (hdeg : g.natDegree = f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hf : f.Splits) (hf_deg_le_one : f.natDegree ≤ 1) (x : ℝ) :
      ((f.roots.filter (x < ·)).card : ℤ) - (g.roots.filter (x < ·)).card ≤ 1 ∧
      ((g.roots.filter (x < ·)).card : ℤ) - (f.roots.filter (x < ·)).card ≤ 1 :=
  succDegreeRootCountAbove_of_posCombo_natDegree_le_one
    hf_pos hg_pos hfnn hgnn hfg hdeg hno hf hf_deg_le_one x

/-- Challenge-facing low-degree base case for the lower-threshold succ-degree
root-count formulation in the positive-combination/no-common setting. -/
theorem succDegreeRootCountPair_of_posCombo_natDegree_le_one
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f) (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g)
    (hdeg : g.natDegree = f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hf : f.Splits) (hf_deg_le_one : f.natDegree ≤ 1) (x : ℝ) :
      ((f.roots.filter (· ≤ x)).card : ℤ) - (g.roots.filter (· ≤ x)).card ≤ 0 ∧
      ((g.roots.filter (· ≤ x)).card : ℤ) - (f.roots.filter (· ≤ x)).card ≤ 2 :=
  succDegreeRootCount_of_posCombo_natDegree_le_one
    hf_pos hg_pos hfnn hgnn hfg hdeg hno hf hf_deg_le_one x

/-- Challenge-facing low-degree base case for the succ-degree root-crossing
inequalities in the positive-combination/no-common setting. -/
theorem succDegreeRootCrossingPair_of_posCombo_natDegree_le_one
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f) (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g)
    (hdeg : g.natDegree = f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hf : f.Splits) (hf_deg_le_one : f.natDegree ≤ 1) :
    (∀ j, 1 ≤ j → j ≤ f.natDegree →
        (rootSeqDesc g).getD j 0 ≤ (rootSeqDesc f).getD (j - 1) 0) ∧
    (∀ j, 1 ≤ j → j < f.natDegree →
        (rootSeqDesc f).getD j 0 ≤ (rootSeqDesc g).getD (j - 1) 0) :=
  succDegreeRootCrossing_of_posCombo_natDegree_le_one
    hf_pos hg_pos hfnn hgnn hfg hdeg hno hf hf_deg_le_one

/-- Challenge-facing low-degree base case for succ-degree root-slot data in
the positive-combination/no-common setting. -/
theorem succDegreeSlotDataPair_of_posCombo_natDegree_le_one
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f) (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g)
    (hdeg : g.natDegree = f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hf_deg_le_one : f.natDegree ≤ 1) :
    (f ≠ 0 ∧ f.Splits) ∧
      ∀ j, j < f.natDegree + 1 →
        ∀ (hjf : j < (rootSeqDesc f).length + 1)
          (hjg : j < (rootSeqDesc g).length + 1),
          (rootSlotInterval (rootSeqDesc f) ⟨j, hjf⟩ ∩
            rootSlotInterval (rootSeqDesc g) ⟨j, hjg⟩).Nonempty :=
  succDegreeSlotData_of_posCombo_natDegree_le_one
    hf_pos hg_pos hfnn hgnn hfg hdeg hno hf_deg_le_one

/-- Challenge-facing low-degree base case for the repaired succ-degree
common-right-interleaver endpoint in the positive-combination/no-common
setting. -/
theorem succDegreePairHasCommonInterleaver_of_posCombo_natDegree_le_one
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f) (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g)
    (hdeg : g.natDegree = f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hf_deg_le_one : f.natDegree ≤ 1) :
    ∃ h : ℝ[X], Prec f h ∧ Prec g h :=
  posComboNoCommonSuccDegreePairHasCommonInterleaver_of_natDegree_le_one
    hf_pos hg_pos hfnn hgnn hfg hdeg hno hf_deg_le_one

/-- Challenge-facing degree-zero base case for succ-degree root-slot data. -/
theorem succDegreeSlotDataPair_of_natDegree_eq_zero
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hf_deg0 : f.natDegree = 0)
    (hsucc : g.natDegree = f.natDegree + 1) :
    (f ≠ 0 ∧ f.Splits) ∧
      ∀ j, j < f.natDegree + 1 →
        ∀ (hjf : j < (rootSeqDesc f).length + 1)
          (hjg : j < (rootSeqDesc g).length + 1),
          (rootSlotInterval (rootSeqDesc f) ⟨j, hjf⟩ ∩
            rootSlotInterval (rootSeqDesc g) ⟨j, hjg⟩).Nonempty :=
  succDegreeSlotData_of_natDegree_eq_zero
    hf_pos hg_pos hf_deg0 hsucc

/-- Challenge-facing degree-one analytic core for the succ-degree
root-crossing target. -/
theorem succDegreeRootLe_of_posCombo_deg1
    {α β γ : ℝ} (hβγ : γ ≤ β)
    (hsplit : ∀ lam μ : ℝ, 0 < lam → 0 < μ →
      (C lam * (X - C α) + C μ * ((X - C β) * (X - C γ))).Splits) :
    γ ≤ α :=
  root_le_of_posCombo_deg1 hβγ hsplit

/-- Challenge-facing example showing that positive-combination real-rootedness
does not by itself force the stronger fixed succ-degree orientation. -/
theorem succDegree_deg1_positiveCombo_example :
    ∀ lam μ : ℝ, 0 < lam → 0 < μ →
      (C lam * (C 2 * X + C 1) + C μ * ((X + C 1) * (X + C 2))).Splits :=
  posCombo_deg1_all_splits

/-- Challenge-facing counterexample to the fixed succ-degree orientation
shortcut. -/
theorem succDegree_deg1_not_prec_example :
    ¬ Prec (C 2 * X + C 1 : ℝ[X]) ((X + C 1) * (X + C 2)) :=
  not_prec_deg1_example

/-- Challenge-facing degree-zero base case for the repaired succ-degree
pair-interleaver endpoint. -/
theorem succDegreePairHasCommonInterleaver_of_natDegree_eq_zero
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hf_deg0 : f.natDegree = 0)
    (hsucc : g.natDegree = f.natDegree + 1) :
    ∃ h : ℝ[X], Prec f h ∧ Prec g h :=
  posComboNoCommonSuccDegreePairHasCommonInterleaver_of_degree_zero
    hf_pos hg_pos hf_deg0 hsucc

/-- Challenge-facing unconditional succ-degree left-splitting target from the
root-continuity endpoint. -/
theorem succDegreeLeftSplitsTarget_of_rootContinuity :
    succDegreeLeftSplitsTarget :=
  PosComboSuccDegreeLeftSplitsNonnegStatement_of_rootContinuity

/-- Challenge-facing unconditional residual left-splitting target from the
root-continuity endpoint. -/
theorem succDegreeResidualLeftSplitsTarget_of_rootContinuity :
    succDegreeResidualLeftSplitsTarget :=
  PosComboSuccDegreeResidualLeftSplitsNonnegStatement_of_rootContinuity

/-- Challenge-facing reduction from left splitting and root crossing to
succ-degree slot data. -/
theorem succDegreeSlotDataTarget_of_leftSplits_and_rootCrossing
    (hsplit : succDegreeLeftSplitsTarget)
    (hcross : succDegreeRootCrossingTarget) :
    succDegreeSlotDataTarget :=
  posComboNoCommonSuccDegreeSlotData_of_leftSplits_and_rootCrossing hsplit hcross

/-- Challenge-facing reduction from root crossing alone to succ-degree slot
data; root continuity supplies the left-splitting endpoint. -/
theorem succDegreeSlotDataTarget_of_rootCrossing
    (hcross : succDegreeRootCrossingTarget) :
    succDegreeSlotDataTarget :=
  posComboNoCommonSuccDegreeSlotData_of_rootCrossing hcross

/-- Challenge-facing reduction from left splitting and root crossing to the
repaired succ-degree pair endpoint. -/
theorem succDegreePairTarget_of_leftSplits_and_rootCrossing
    (hsplit : succDegreeLeftSplitsTarget)
    (hcross : succDegreeRootCrossingTarget) :
    succDegreePairTarget :=
  succDegreePairHasCommonInterleaver_nonneg_of_leftSplits_and_rootCrossing
    hsplit hcross

/-- Challenge-facing reduction from root crossing alone to the repaired
succ-degree pair endpoint; root continuity supplies the left endpoint. -/
theorem succDegreePairTarget_of_rootCrossing
    (hcross : succDegreeRootCrossingTarget) :
    succDegreePairTarget :=
  succDegreePairHasCommonInterleaver_nonneg_of_rootCrossing hcross

/-- Challenge-facing PF/ASW reduction to the succ-degree left-splitting target. -/
theorem succDegreeLeftSplitsTarget_of_forward_asw
    (hASW : forwardASWTarget) :
    succDegreeLeftSplitsTarget :=
  PosComboSuccDegreeLeftSplitsNonnegStatement_of_forward_asw hASW

/-- Challenge-facing PF/ASW reduction to the residual left-splitting target. -/
theorem succDegreeResidualLeftSplitsTarget_of_forward_asw
    (hASW : forwardASWTarget) :
    succDegreeResidualLeftSplitsTarget :=
  PosComboSuccDegreeResidualLeftSplitsNonnegStatement_of_forward_asw hASW

/-- The zero-aware ASW target is equivalent to the splitting-only target. -/
theorem forwardASWTarget_iff_splitsTarget :
    forwardASWTarget ↔ forwardASWSplitsTarget :=
  aissenSchoenbergWhitneyForwardOrZero_iff_splits

/-- Challenge-facing bridge from splitting-only ASW to the zero-aware ASW
target. -/
theorem forwardASWTarget_of_splitsTarget
    (hASW : forwardASWSplitsTarget) :
    forwardASWTarget :=
  aissenSchoenbergWhitneyForwardOrZero_of_splits hASW

/-- Challenge-facing PF/ASW reduction to the succ-degree left-splitting target,
using only the splitting conjunct of ASW. -/
theorem succDegreeLeftSplitsTarget_of_forward_asw_splits
    (hASW : forwardASWSplitsTarget) :
    succDegreeLeftSplitsTarget :=
  PosComboSuccDegreeLeftSplitsNonnegStatement_of_forward_asw_splits hASW

/-- Challenge-facing PF/ASW reduction to the residual left-splitting target,
using only the splitting conjunct of ASW. -/
theorem succDegreeResidualLeftSplitsTarget_of_forward_asw_splits
    (hASW : forwardASWSplitsTarget) :
    succDegreeResidualLeftSplitsTarget :=
  PosComboSuccDegreeResidualLeftSplitsNonnegStatement_of_forward_asw_splits hASW

/-- Challenge-facing reduction from the residual constant-coefficient branch to
the full succ-degree left-splitting target. -/
theorem succDegreeLeftSplitsTarget_of_residual
    (hres : succDegreeResidualLeftSplitsTarget) :
    succDegreeLeftSplitsTarget :=
  PosComboSuccDegreeLeftSplitsNonnegStatement_of_residual hres

/-- Challenge-facing equivalence between the full succ-degree left-splitting
target and its residual constant-coefficient branch. -/
theorem succDegreeLeftSplitsTarget_iff_residual :
    succDegreeLeftSplitsTarget ↔ succDegreeResidualLeftSplitsTarget :=
  PosComboSuccDegreeLeftSplitsNonnegStatement_iff_residual

/-- Challenge-facing reduction from forward ASW and root crossing to
succ-degree slot data. -/
theorem succDegreeSlotDataTarget_of_forward_asw_and_rootCrossing
    (hASW : forwardASWTarget)
    (hcross : succDegreeRootCrossingTarget) :
    succDegreeSlotDataTarget :=
  posComboNoCommonSuccDegreeSlotData_of_forward_asw_and_rootCrossing
    hASW hcross

/-- Challenge-facing reduction from splitting-only ASW and root crossing to
succ-degree slot data. -/
theorem succDegreeSlotDataTarget_of_forward_asw_splits_and_rootCrossing
    (hASW : forwardASWSplitsTarget)
    (hcross : succDegreeRootCrossingTarget) :
    succDegreeSlotDataTarget :=
  posComboNoCommonSuccDegreeSlotData_of_forward_asw_splits_and_rootCrossing
    hASW hcross

/-- Challenge-facing reduction from forward ASW and root crossing to the
repaired succ-degree pair endpoint. -/
theorem succDegreePairTarget_of_forward_asw_and_rootCrossing
    (hASW : forwardASWTarget)
    (hcross : succDegreeRootCrossingTarget) :
    succDegreePairTarget :=
  succDegreePairHasCommonInterleaver_nonneg_of_forward_asw_and_rootCrossing
    hASW hcross

/-- Challenge-facing reduction from splitting-only ASW and root crossing to the
repaired succ-degree pair endpoint. -/
theorem succDegreePairTarget_of_forward_asw_splits_and_rootCrossing
    (hASW : forwardASWSplitsTarget)
    (hcross : succDegreeRootCrossingTarget) :
    succDegreePairTarget :=
  succDegreePairHasCommonInterleaver_nonneg_of_forward_asw_splits_and_rootCrossing
    hASW hcross

/-- Challenge-facing reduction from the residual branch and root crossing to the
repaired succ-degree pair endpoint. -/
theorem succDegreePairTarget_of_residual_and_rootCrossing
    (hres : succDegreeResidualLeftSplitsTarget)
    (hcross : succDegreeRootCrossingTarget) :
    succDegreePairTarget :=
  succDegreePairTarget_of_leftSplits_and_rootCrossing
    (succDegreeLeftSplitsTarget_of_residual hres) hcross

/-- Challenge-facing reduction from left splitting and fixed orientation to
succ-degree slot data. -/
theorem succDegreeSlotDataTarget_of_leftSplits_and_orientation
    (hsplit : succDegreeLeftSplitsTarget)
    (horient : succDegreeOrientationTarget) :
    succDegreeSlotDataTarget :=
  posComboNoCommonSuccDegreeSlotData_of_leftSplits_and_orientation hsplit horient

/-- Challenge-facing reduction from left splitting and fixed orientation to
the repaired succ-degree pair endpoint. -/
theorem succDegreePairTarget_of_leftSplits_and_orientation
    (hsplit : succDegreeLeftSplitsTarget)
    (horient : succDegreeOrientationTarget) :
    succDegreePairTarget :=
  succDegreePairHasCommonInterleaver_nonneg_of_leftSplits_and_orientation
    hsplit horient

/-- Challenge-facing reduction from forward ASW and fixed orientation to
succ-degree slot data. -/
theorem succDegreeSlotDataTarget_of_forward_asw_and_orientation
    (hASW : forwardASWTarget)
    (horient : succDegreeOrientationTarget) :
    succDegreeSlotDataTarget :=
  posComboNoCommonSuccDegreeSlotData_of_forward_asw_and_orientation
    hASW horient

/-- Challenge-facing reduction from splitting-only ASW and fixed orientation to
succ-degree slot data. -/
theorem succDegreeSlotDataTarget_of_forward_asw_splits_and_orientation
    (hASW : forwardASWSplitsTarget)
    (horient : succDegreeOrientationTarget) :
    succDegreeSlotDataTarget :=
  posComboNoCommonSuccDegreeSlotData_of_forward_asw_splits_and_orientation
    hASW horient

/-- Challenge-facing reduction from forward ASW and fixed orientation to the
repaired succ-degree pair endpoint. -/
theorem succDegreePairTarget_of_forward_asw_and_orientation
    (hASW : forwardASWTarget)
    (horient : succDegreeOrientationTarget) :
    succDegreePairTarget :=
  succDegreePairHasCommonInterleaver_nonneg_of_forward_asw_and_orientation
    hASW horient

/-- Challenge-facing reduction from splitting-only ASW and fixed orientation to
the repaired succ-degree pair endpoint. -/
theorem succDegreePairTarget_of_forward_asw_splits_and_orientation
    (hASW : forwardASWSplitsTarget)
    (horient : succDegreeOrientationTarget) :
    succDegreePairTarget :=
  succDegreePairHasCommonInterleaver_nonneg_of_forward_asw_splits_and_orientation
    hASW horient

/-- Challenge-facing reduction from the stronger fixed orientation to the
repaired succ-degree pair endpoint. -/
theorem succDegreePairTarget_of_orientation
    (horient : succDegreeOrientationTarget) :
    succDegreePairTarget :=
  posComboNoCommonSuccDegreePairHasCommonInterleaver_of_orientation_nonneg
    horient

/-- Challenge-facing reduction from the affine-family bridge to the repaired
succ-degree pair endpoint. -/
theorem succDegreePairTarget_of_affineFamily
    (haff : affineFamilyTarget) :
    succDegreePairTarget :=
  posComboNoCommonSuccDegreePairHasCommonInterleaver_of_affineFamily haff

/-- Challenge-facing reduction from boundary-right-pair orientation to the
affine-family bridge. -/
theorem affineFamilyTarget_of_boundaryRight
    (hboundary : boundaryRightPairOrientationTarget) :
    affineFamilyTarget :=
  posComboNoCommonAffineFamily_of_boundaryRightPairOrientation hboundary

/-- Challenge-facing no-common left-endpoint reduction from the affine-family
bridge.  This is the endpoint part of `succDegreePairTarget_of_affineFamily`;
the remaining input is producing the affine family from positive
compatibility. -/
theorem succDegreeNoCommonLeftSplitsTarget_of_affineFamily
    (haff : affineFamilyTarget)
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g)
    (hsucc : g.natDegree = f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    f.Splits :=
  posComboNoCommonSuccDegreeLeftSplits_of_affineFamily
    haff hf_pos hg_pos hfnn hgnn hfg hsucc hno

/-- Challenge-facing no-common left-endpoint reduction from boundary-right
pair orientation. -/
theorem succDegreeNoCommonLeftSplitsTarget_of_boundaryRight
    (hboundary : boundaryRightPairOrientationTarget)
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g)
    (hsucc : g.natDegree = f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    f.Splits :=
  posComboNoCommonSuccDegreeLeftSplits_of_boundaryRightPairOrientation
    hboundary hf_pos hg_pos hfnn hgnn hfg hsucc hno

/-- Challenge-facing reduction from the boundary-right-pair orientation
statement to the repaired succ-degree pair endpoint. -/
theorem succDegreePairTarget_of_boundaryRight
    (hboundary : boundaryRightPairOrientationTarget) :
    succDegreePairTarget :=
  succDegreePairHasCommonInterleaver_nonneg_of_boundaryRightPairOrientation
    hboundary

/-- Full roadmap reduction for the common-left target. -/
theorem commonLeftInterleaverTarget_of_pairwiseLeftBridge
    (htwo : CompatiblePairHasCommonLeftInterleaverStatement)
    (hglobal : _root_.RealRooted.CommonLeftInterleaverFamilyUpgradeStatement) :
    commonLeftInterleaverTarget :=
  RealRooted.chudnovskySeymour_pairwiseCompatible_iff_commonLeftInterleaver_of_pairwiseLeftBridge
    htwo hglobal

/-- Direct roadmap reduction for the common-left target after the finite-family
common-left upgrade has been internalized. -/
theorem commonLeftInterleaverTarget_of_pairwiseLeftBridge_direct
    (htwo : CompatiblePairHasCommonLeftInterleaverStatement) :
    commonLeftInterleaverTarget :=
  chudnovskySeymour_pairwiseCompatible_iff_commonLeftInterleaver_of_pairwiseLeftBridge_direct
    htwo

/-- Full roadmap reduction for the common-right target. -/
theorem commonInterleaverTarget_of_pairBridge
    (htwo : CompatiblePairHasCommonInterleaverStatement) :
    commonInterleaverTarget :=
  RealRooted.chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_of_pairBridge htwo

/-- Challenge-facing pairwise upgrade from lower-threshold root-count
formulations alone. -/
theorem pairwiseHasCommonInterleaver_of_pairwiseCompatible_of_rootCount
    {fs : List ℝ[X]}
    (hsame : sameDegreeRootCountTarget)
    (hsucc : succDegreeRootCountTarget)
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hpair : PairwiseCompatible fs) :
    PairwiseHasCommonInterleaver fs :=
  RealRooted.pairwiseHasCommonInterleaver_of_pairwiseCompatible_of_rootCount
    hsame hsucc hpos hpair

/-- Challenge-facing pairwise upgrade from same-degree lower-threshold root
counts and succ-degree upper-threshold root counts. -/
theorem pairwiseHasCommonInterleaver_of_pairwiseCompatible_of_rootCountAbove
    {fs : List ℝ[X]}
    (hsame : sameDegreeRootCountTarget)
    (hsucc : succDegreeRootCountAboveTarget)
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hpair : PairwiseCompatible fs) :
    PairwiseHasCommonInterleaver fs :=
  RealRooted.pairwiseHasCommonInterleaver_of_pairwiseCompatible_of_rootCountAbove
    hsame hsucc hpos hpair

/-- Challenge-facing pairwise upgrade from same-degree upper-threshold root
counts and succ-degree lower-threshold root counts. -/
theorem pairwiseHasCommonInterleaver_of_pairwiseCompatible_of_sameRootCountAbove
    {fs : List ℝ[X]}
    (hsame : sameDegreeRootCountAboveTarget)
    (hsucc : succDegreeRootCountTarget)
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hpair : PairwiseCompatible fs) :
    PairwiseHasCommonInterleaver fs :=
  RealRooted.pairwiseHasCommonInterleaver_of_pairwiseCompatible_of_sameRootCountAbove
    hsame hsucc hpos hpair

/-- Challenge-facing pairwise upgrade from upper-threshold root-count
formulations in both branches. -/
theorem pairwiseHasCommonInterleaver_of_pairwiseCompatible_of_rootCountAboveBoth
    {fs : List ℝ[X]}
    (hsame : sameDegreeRootCountAboveTarget)
    (hsucc : succDegreeRootCountAboveTarget)
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hpair : PairwiseCompatible fs) :
    PairwiseHasCommonInterleaver fs :=
  RealRooted.pairwiseHasCommonInterleaver_of_pairwiseCompatible_of_rootCountAboveBoth
    hsame hsucc hpos hpair

/-- Challenge-facing full roadmap reduction from the root-crossing
formulations alone; root continuity supplies the succ-degree left endpoint. -/
theorem commonInterleaverTarget_of_rootCrossing
    (hsame : sameDegreeRootCrossingTarget)
    (hsucc : succDegreeRootCrossingTarget) :
    commonInterleaverTarget :=
  chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_of_rootCrossing_direct
    hsame hsucc

/-- Challenge-facing full roadmap reduction from lower-threshold root-count
formulations alone. -/
theorem commonInterleaverTarget_of_rootCount
    (hsame : sameDegreeRootCountTarget)
    (hsucc : succDegreeRootCountTarget) :
    commonInterleaverTarget :=
  commonInterleaverTarget_of_pairBridge
    (compatiblePairHasCommonInterleaver_of_rootCount hsame hsucc)

/-- Challenge-facing full roadmap reduction from same-degree lower-threshold
root counts and succ-degree upper-threshold root counts. -/
theorem commonInterleaverTarget_of_rootCountAbove
    (hsame : sameDegreeRootCountTarget)
    (hsucc : succDegreeRootCountAboveTarget) :
    commonInterleaverTarget :=
  commonInterleaverTarget_of_pairBridge
    (compatiblePairHasCommonInterleaver_of_rootCountAbove hsame hsucc)

/-- Challenge-facing full roadmap reduction from same-degree upper-threshold
root counts and succ-degree lower-threshold root counts. -/
theorem commonInterleaverTarget_of_sameRootCountAbove
    (hsame : sameDegreeRootCountAboveTarget)
    (hsucc : succDegreeRootCountTarget) :
    commonInterleaverTarget :=
  commonInterleaverTarget_of_pairBridge
    (compatiblePairHasCommonInterleaver_of_sameRootCountAbove hsame hsucc)

/-- Challenge-facing full roadmap reduction from upper-threshold root-count
formulations in both the same-degree and succ-degree branches. -/
theorem commonInterleaverTarget_of_rootCountAboveBoth
    (hsame : sameDegreeRootCountAboveTarget)
    (hsucc : succDegreeRootCountAboveTarget) :
    commonInterleaverTarget :=
  commonInterleaverTarget_of_pairBridge
    (compatiblePairHasCommonInterleaver_of_rootCountAboveBoth hsame hsucc)

/-- Challenge-facing full roadmap reduction from the root-crossing formulations,
with the succ-degree left endpoint supplied by forward ASW. -/
theorem commonInterleaverTarget_of_rootCrossing_and_forward_asw
    (hsame : sameDegreeRootCrossingTarget)
    (hASW : forwardASWTarget)
    (hsucc : succDegreeRootCrossingTarget) :
    commonInterleaverTarget :=
  chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_of_rootCrossing_and_forward_asw
    hsame hASW hsucc

/-- Challenge-facing full roadmap reduction from the root-crossing formulations,
with the succ-degree left endpoint supplied by the splitting-only ASW target. -/
theorem commonInterleaverTarget_of_rootCrossing_and_forward_asw_splits
    (hsame : sameDegreeRootCrossingTarget)
    (hASW : forwardASWSplitsTarget)
    (hsucc : succDegreeRootCrossingTarget) :
  commonInterleaverTarget :=
  chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_of_rootCrossing_and_forwardASWSplits
    hsame hASW hsucc

/-- Challenge-facing full roadmap reduction from same-degree root-crossing and
the affine-family bridge for the succ-degree branch. -/
theorem commonInterleaverTarget_of_sameDegreeRootCrossing_and_affineFamily
    (hsame : sameDegreeRootCrossingTarget)
    (haff : affineFamilyTarget) :
    commonInterleaverTarget :=
  chudnovskySeymour_commonInterleaver_of_sameDegreeCrossing_affineFamily
    hsame haff

/-- Challenge-facing four-way package from the root-crossing formulations
alone; root continuity supplies the succ-degree left endpoint. -/
theorem fourWay_of_rootCrossing
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hsame : sameDegreeRootCrossingTarget)
    (hsucc : succDegreeRootCrossingTarget) :
    fourWayPackage fs :=
  chudnovskySeymour_fourWay_of_rootCrossing
    hrr hpos hsame hsucc

/-- Challenge-facing four-way package from lower-threshold root-count
formulations alone. -/
theorem fourWay_of_rootCount
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hsame : sameDegreeRootCountTarget)
    (hsucc : succDegreeRootCountTarget) :
    fourWayPackage fs :=
  fourWay_of_rootCrossing hrr hpos
    (sameDegreeRootCrossingTarget_of_rootCount hsame)
    (succDegreeRootCrossingTarget_of_rootCount hsucc)

/-- Challenge-facing four-way package from same-degree lower-threshold root
counts and succ-degree upper-threshold root counts. -/
theorem fourWay_of_rootCountAbove
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hsame : sameDegreeRootCountTarget)
    (hsucc : succDegreeRootCountAboveTarget) :
    fourWayPackage fs :=
  fourWay_of_rootCrossing hrr hpos
    (sameDegreeRootCrossingTarget_of_rootCount hsame)
    (succDegreeRootCrossingTarget_of_rootCountAbove hsucc)

/-- Challenge-facing four-way package from same-degree upper-threshold root
counts and succ-degree lower-threshold root counts. -/
theorem fourWay_of_sameRootCountAbove
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hsame : sameDegreeRootCountAboveTarget)
    (hsucc : succDegreeRootCountTarget) :
    fourWayPackage fs :=
  fourWay_of_rootCrossing hrr hpos
    (sameDegreeRootCrossingTarget_of_rootCountAbove hsame)
    (succDegreeRootCrossingTarget_of_rootCount hsucc)

/-- Challenge-facing four-way package from upper-threshold root-count
formulations in both branches. -/
theorem fourWay_of_rootCountAboveBoth
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hsame : sameDegreeRootCountAboveTarget)
    (hsucc : succDegreeRootCountAboveTarget) :
    fourWayPackage fs :=
  fourWay_of_rootCrossing hrr hpos
    (sameDegreeRootCrossingTarget_of_rootCountAbove hsame)
    (succDegreeRootCrossingTarget_of_rootCountAbove hsucc)

/-- Challenge-facing four-way package from the root-crossing formulations,
with the succ-degree left endpoint supplied by the splitting-only ASW target. -/
theorem fourWay_of_rootCrossing_and_forward_asw_splits
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hsame : sameDegreeRootCrossingTarget)
    (hASW : forwardASWSplitsTarget)
    (hsucc : succDegreeRootCrossingTarget) :
    fourWayPackage fs :=
  chudnovskySeymour_fourWay_of_rootCrossing_and_forward_asw_splits
    hrr hpos hsame hASW hsucc

/-- Challenge-facing reduction for the nonnegative four-way target from
root-crossing alone. -/
theorem fourWayNonnegCoeffsTarget_of_rootCrossing
    (hsame : sameDegreeRootCrossingTarget)
    (hsucc : succDegreeRootCrossingTarget) :
    fourWayNonnegCoeffsTarget :=
  chudnovskySeymour_fourWay_of_rootCrossing_nonneg hsame hsucc

/-- Challenge-facing reduction for the nonnegative four-way target from
lower-threshold root-count formulations alone. -/
theorem fourWayNonnegCoeffsTarget_of_rootCount
    (hsame : sameDegreeRootCountTarget)
    (hsucc : succDegreeRootCountTarget) :
    fourWayNonnegCoeffsTarget :=
  fourWayNonnegCoeffsTarget_of_rootCrossing
    (sameDegreeRootCrossingTarget_of_rootCount hsame)
    (succDegreeRootCrossingTarget_of_rootCount hsucc)

/-- Challenge-facing reduction for the nonnegative four-way target from
same-degree lower-threshold root counts and succ-degree upper-threshold root
counts. -/
theorem fourWayNonnegCoeffsTarget_of_rootCountAbove
    (hsame : sameDegreeRootCountTarget)
    (hsucc : succDegreeRootCountAboveTarget) :
    fourWayNonnegCoeffsTarget :=
  fourWayNonnegCoeffsTarget_of_rootCrossing
    (sameDegreeRootCrossingTarget_of_rootCount hsame)
    (succDegreeRootCrossingTarget_of_rootCountAbove hsucc)

/-- Challenge-facing reduction for the nonnegative four-way target from
same-degree upper-threshold root counts and succ-degree lower-threshold root
counts. -/
theorem fourWayNonnegCoeffsTarget_of_sameRootCountAbove
    (hsame : sameDegreeRootCountAboveTarget)
    (hsucc : succDegreeRootCountTarget) :
    fourWayNonnegCoeffsTarget :=
  fourWayNonnegCoeffsTarget_of_rootCrossing
    (sameDegreeRootCrossingTarget_of_rootCountAbove hsame)
    (succDegreeRootCrossingTarget_of_rootCount hsucc)

/-- Challenge-facing reduction for the nonnegative four-way target from
upper-threshold root-count formulations in both branches. -/
theorem fourWayNonnegCoeffsTarget_of_rootCountAboveBoth
    (hsame : sameDegreeRootCountAboveTarget)
    (hsucc : succDegreeRootCountAboveTarget) :
    fourWayNonnegCoeffsTarget :=
  fourWayNonnegCoeffsTarget_of_rootCrossing
    (sameDegreeRootCrossingTarget_of_rootCountAbove hsame)
    (succDegreeRootCrossingTarget_of_rootCountAbove hsucc)

/-- Challenge-facing reduction for the nonnegative four-way target from
root-crossing plus splitting-only ASW. -/
theorem fourWayNonnegCoeffsTarget_of_rootCrossing_and_forward_asw_splits
    (hsame : sameDegreeRootCrossingTarget)
    (hASW : forwardASWSplitsTarget)
    (hsucc : succDegreeRootCrossingTarget) :
    fourWayNonnegCoeffsTarget :=
  chudnovskySeymour_fourWay_of_rootCrossing_forwardASWSplits_nonneg
    hsame hASW hsucc

/-- Challenge-facing reduction for the nonnegative four-way target from
same-degree root-crossing and the affine-family bridge. -/
theorem fourWayNonnegCoeffsTarget_of_sameDegreeRootCrossing_and_affineFamily
    (hsame : sameDegreeRootCrossingTarget)
    (haff : affineFamilyTarget) :
    fourWayNonnegCoeffsTarget :=
  chudnovskySeymour_fourWay_of_sameDegreeRootCrossing_and_affineFamily_nonneg
    hsame haff

/-- Challenge-facing reduction for the nonnegative common-right target from
root-crossing alone. -/
theorem commonInterleaverNonnegCoeffsTarget_of_rootCrossing
    (hsame : sameDegreeRootCrossingTarget)
    (hsucc : succDegreeRootCrossingTarget) :
    commonInterleaverNonnegCoeffsTarget :=
  chudnovskySeymour_commonInterleaver_of_rootCrossing_nonneg hsame hsucc

/-- Challenge-facing reduction for the nonnegative common-right target from
lower-threshold root-count formulations alone. -/
theorem commonInterleaverNonnegCoeffsTarget_of_rootCount
    (hsame : sameDegreeRootCountTarget)
    (hsucc : succDegreeRootCountTarget) :
    commonInterleaverNonnegCoeffsTarget :=
  commonInterleaverNonnegCoeffsTarget_of_rootCrossing
    (sameDegreeRootCrossingTarget_of_rootCount hsame)
    (succDegreeRootCrossingTarget_of_rootCount hsucc)

/-- Challenge-facing reduction for the nonnegative common-right target from
same-degree lower-threshold root counts and succ-degree upper-threshold root
counts. -/
theorem commonInterleaverNonnegCoeffsTarget_of_rootCountAbove
    (hsame : sameDegreeRootCountTarget)
    (hsucc : succDegreeRootCountAboveTarget) :
    commonInterleaverNonnegCoeffsTarget :=
  commonInterleaverNonnegCoeffsTarget_of_rootCrossing
    (sameDegreeRootCrossingTarget_of_rootCount hsame)
    (succDegreeRootCrossingTarget_of_rootCountAbove hsucc)

/-- Challenge-facing reduction for the nonnegative common-right target from
same-degree upper-threshold root counts and succ-degree lower-threshold root
counts. -/
theorem commonInterleaverNonnegCoeffsTarget_of_sameRootCountAbove
    (hsame : sameDegreeRootCountAboveTarget)
    (hsucc : succDegreeRootCountTarget) :
    commonInterleaverNonnegCoeffsTarget :=
  commonInterleaverNonnegCoeffsTarget_of_rootCrossing
    (sameDegreeRootCrossingTarget_of_rootCountAbove hsame)
    (succDegreeRootCrossingTarget_of_rootCount hsucc)

/-- Challenge-facing reduction for the nonnegative common-right target from
upper-threshold root-count formulations in both branches. -/
theorem commonInterleaverNonnegCoeffsTarget_of_rootCountAboveBoth
    (hsame : sameDegreeRootCountAboveTarget)
    (hsucc : succDegreeRootCountAboveTarget) :
    commonInterleaverNonnegCoeffsTarget :=
  commonInterleaverNonnegCoeffsTarget_of_rootCrossing
    (sameDegreeRootCrossingTarget_of_rootCountAbove hsame)
    (succDegreeRootCrossingTarget_of_rootCountAbove hsucc)

/-- Challenge-facing reduction for the nonnegative common-right target from
root-crossing plus splitting-only ASW. -/
theorem commonInterleaverNonnegCoeffsTarget_of_rootCrossing_and_forward_asw_splits
    (hsame : sameDegreeRootCrossingTarget)
    (hASW : forwardASWSplitsTarget)
    (hsucc : succDegreeRootCrossingTarget) :
    commonInterleaverNonnegCoeffsTarget :=
  chudnovskySeymour_commonInterleaver_of_rootCrossing_forwardASWSplits_nonneg
    hsame hASW hsucc

/-- Challenge-facing reduction for the nonnegative common-right target from
same-degree root-crossing and the affine-family bridge. -/
theorem commonInterleaverNonnegCoeffsTarget_of_sameDegreeRootCrossing_and_affineFamily
    (hsame : sameDegreeRootCrossingTarget)
    (haff : affineFamilyTarget) :
    commonInterleaverNonnegCoeffsTarget :=
  chudnovskySeymour_commonInterleaver_of_sameDegreeRootCrossing_and_affineFamily_nonneg
    hsame haff

/-- Challenge-facing reduction for the nonnegative finite-family compatibility
target from root-crossing alone. -/
theorem familyCompatibleNonnegCoeffsTarget_of_rootCrossing
    (hsame : sameDegreeRootCrossingTarget)
    (hsucc : succDegreeRootCrossingTarget) :
    familyCompatibleNonnegCoeffsTarget :=
  chudnovskySeymour_familyCompatible_of_rootCrossing_nonneg hsame hsucc

/-- Challenge-facing reduction for the nonnegative finite-family compatibility
target from lower-threshold root-count formulations alone. -/
theorem familyCompatibleNonnegCoeffsTarget_of_rootCount
    (hsame : sameDegreeRootCountTarget)
    (hsucc : succDegreeRootCountTarget) :
    familyCompatibleNonnegCoeffsTarget :=
  familyCompatibleNonnegCoeffsTarget_of_rootCrossing
    (sameDegreeRootCrossingTarget_of_rootCount hsame)
    (succDegreeRootCrossingTarget_of_rootCount hsucc)

/-- Challenge-facing reduction for the nonnegative finite-family compatibility
target from same-degree lower-threshold root counts and succ-degree
upper-threshold root counts. -/
theorem familyCompatibleNonnegCoeffsTarget_of_rootCountAbove
    (hsame : sameDegreeRootCountTarget)
    (hsucc : succDegreeRootCountAboveTarget) :
    familyCompatibleNonnegCoeffsTarget :=
  familyCompatibleNonnegCoeffsTarget_of_rootCrossing
    (sameDegreeRootCrossingTarget_of_rootCount hsame)
    (succDegreeRootCrossingTarget_of_rootCountAbove hsucc)

/-- Challenge-facing reduction for the nonnegative finite-family compatibility
target from same-degree upper-threshold root counts and succ-degree
lower-threshold root counts. -/
theorem familyCompatibleNonnegCoeffsTarget_of_sameRootCountAbove
    (hsame : sameDegreeRootCountAboveTarget)
    (hsucc : succDegreeRootCountTarget) :
    familyCompatibleNonnegCoeffsTarget :=
  familyCompatibleNonnegCoeffsTarget_of_rootCrossing
    (sameDegreeRootCrossingTarget_of_rootCountAbove hsame)
    (succDegreeRootCrossingTarget_of_rootCount hsucc)

/-- Challenge-facing reduction for the nonnegative finite-family compatibility
target from upper-threshold root-count formulations in both branches. -/
theorem familyCompatibleNonnegCoeffsTarget_of_rootCountAboveBoth
    (hsame : sameDegreeRootCountAboveTarget)
    (hsucc : succDegreeRootCountAboveTarget) :
    familyCompatibleNonnegCoeffsTarget :=
  familyCompatibleNonnegCoeffsTarget_of_rootCrossing
    (sameDegreeRootCrossingTarget_of_rootCountAbove hsame)
    (succDegreeRootCrossingTarget_of_rootCountAbove hsucc)

/-- Challenge-facing reduction for the nonnegative finite-family compatibility
target from root-crossing plus splitting-only ASW. -/
theorem familyCompatibleNonnegCoeffsTarget_of_rootCrossing_and_forward_asw_splits
    (hsame : sameDegreeRootCrossingTarget)
    (hASW : forwardASWSplitsTarget)
    (hsucc : succDegreeRootCrossingTarget) :
    familyCompatibleNonnegCoeffsTarget :=
  chudnovskySeymour_familyCompatible_of_rootCrossing_forwardASWSplits_nonneg
    hsame hASW hsucc

/-- Challenge-facing reduction for the nonnegative finite-family compatibility
target from same-degree root-crossing and the affine-family bridge. -/
theorem familyCompatibleNonnegCoeffsTarget_of_sameDegreeRootCrossing_and_affineFamily
    (hsame : sameDegreeRootCrossingTarget)
    (haff : affineFamilyTarget) :
    familyCompatibleNonnegCoeffsTarget :=
  chudnovskySeymour_familyCompatible_of_sameDegreeRootCrossing_and_affineFamily_nonneg
    hsame haff

/-- Challenge-facing reduction for the nonnegative-coefficient common-right
target from the repaired same-degree/succ-degree no-common pair bridges. -/
theorem commonInterleaverNonnegCoeffsTarget_of_pairDegreeSplit
    (hsame : PosComboNoCommonSameDegreePairHasCommonInterleaverNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement) :
    commonInterleaverNonnegCoeffsTarget :=
  chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_of_pairDegreeSplit_nonneg
    hsame hsucc

/-- Challenge-facing reduction for the nonnegative-coefficient common-right
target from the honest degree-split package. -/
theorem commonInterleaverNonnegCoeffsTarget_of_degreeSplit
    (hsame : PosComboNoCommonSameDegreeOrientationAlternativeNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement) :
    commonInterleaverNonnegCoeffsTarget :=
  chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_of_degreeSplit_nonneg
    hsame hsucc

/-- Challenge-facing reduction for the nonnegative-coefficient common-right
target from the boundary-right-pair orientation statement. -/
theorem commonInterleaverNonnegCoeffsTarget_of_boundaryRight
    (hboundary : boundaryRightPairOrientationTarget) :
    commonInterleaverNonnegCoeffsTarget :=
  chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_of_boundaryRight_nonneg
    hboundary

/-- Challenge-facing projection from the nonnegative four-way package target
to the nonnegative common-right interleaver target. -/
theorem commonInterleaverNonnegCoeffsTarget_of_fourWay
    (hfour : fourWayNonnegCoeffsTarget) :
    commonInterleaverNonnegCoeffsTarget :=
  chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_of_fourWay_nonneg
    hfour

/-- Challenge-facing projection from the nonnegative-coefficient common-right
interleaver target to the finite-family compatibility target. -/
theorem familyCompatibleNonnegCoeffsTarget_of_commonInterleaverTarget
    (hcommon : commonInterleaverNonnegCoeffsTarget) :
    familyCompatibleNonnegCoeffsTarget :=
  chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_of_commonInterleaver_nonneg
    hcommon

/-- Challenge-facing projection from the nonnegative four-way package target
to the nonnegative finite-family compatibility target. -/
theorem familyCompatibleNonnegCoeffsTarget_of_fourWay
    (hfour : fourWayNonnegCoeffsTarget) :
    familyCompatibleNonnegCoeffsTarget :=
  familyCompatibleNonnegCoeffsTarget_of_commonInterleaverTarget
    (commonInterleaverNonnegCoeffsTarget_of_fourWay hfour)

/-- Challenge-facing reduction for the nonnegative-coefficient finite-family
compatibility target from the repaired same-degree/succ-degree no-common pair
bridges. -/
theorem familyCompatibleNonnegCoeffsTarget_of_pairDegreeSplit
    (hsame : PosComboNoCommonSameDegreePairHasCommonInterleaverNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement) :
    familyCompatibleNonnegCoeffsTarget :=
  familyCompatibleNonnegCoeffsTarget_of_commonInterleaverTarget
    (commonInterleaverNonnegCoeffsTarget_of_pairDegreeSplit hsame hsucc)

/-- Challenge-facing reduction for the nonnegative-coefficient finite-family
compatibility target from the honest degree-split package. -/
theorem familyCompatibleNonnegCoeffsTarget_of_degreeSplit
    (hsame : PosComboNoCommonSameDegreeOrientationAlternativeNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement) :
    familyCompatibleNonnegCoeffsTarget :=
  familyCompatibleNonnegCoeffsTarget_of_commonInterleaverTarget
    (commonInterleaverNonnegCoeffsTarget_of_degreeSplit hsame hsucc)

/-- Challenge-facing reduction for the nonnegative-coefficient finite-family
compatibility target from the boundary-right-pair orientation statement. -/
theorem familyCompatibleNonnegCoeffsTarget_of_boundaryRight
    (hboundary : boundaryRightPairOrientationTarget) :
    familyCompatibleNonnegCoeffsTarget :=
  familyCompatibleNonnegCoeffsTarget_of_commonInterleaverTarget
    (commonInterleaverNonnegCoeffsTarget_of_boundaryRight hboundary)

/-- Challenge-facing reduction for the nonnegative four-way package target
from the repaired same-degree/succ-degree no-common pair bridges. -/
theorem fourWayNonnegCoeffsTarget_of_pairDegreeSplit
    (hsame : PosComboNoCommonSameDegreePairHasCommonInterleaverNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement) :
    fourWayNonnegCoeffsTarget :=
  chudnovskySeymour_fourWay_of_pairDegreeSplit_nonneg hsame hsucc

/-- Challenge-facing reduction for the nonnegative four-way package target
from the honest degree-split package. -/
theorem fourWayNonnegCoeffsTarget_of_degreeSplit
    (hsame : PosComboNoCommonSameDegreeOrientationAlternativeNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement) :
    fourWayNonnegCoeffsTarget :=
  chudnovskySeymour_fourWay_of_degreeSplit_nonneg hsame hsucc

/-- Challenge-facing reduction for the nonnegative four-way package target
from the boundary-right-pair orientation statement. -/
theorem fourWayNonnegCoeffsTarget_of_boundaryRight
    (hboundary : boundaryRightPairOrientationTarget) :
    fourWayNonnegCoeffsTarget :=
  chudnovskySeymour_fourWay_of_boundaryRight_nonneg hboundary

/-- Challenge-facing four-way package from the natural two-polynomial bridge. -/
theorem fourWay_of_pairBridge
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (htwo : CompatiblePairHasCommonInterleaverStatement) :
    fourWayPackage fs :=
  chudnovskySeymour_fourWay_of_pairBridgePos hrr hpos htwo

/-- Solved low-degree four-way Chudnovsky--Seymour package. -/
theorem fourWay_of_natDegree_le_one {fs : List ℝ[X]}
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hdeg : ∀ f ∈ fs, f.natDegree ≤ 1) :
    fourWayPackage fs :=
  chudnovskySeymour_fourWay_of_natDegree_le_one
    (fs := fs) hpos hdeg

/-- Solved low-degree pairwise/common-interleaver equivalence. -/
theorem pairwiseCompatible_iff_commonInterleaver_of_natDegree_le_one
    {fs : List ℝ[X]}
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hdeg : ∀ f ∈ fs, f.natDegree ≤ 1) :
    PairwiseCompatible fs ↔ HasCommonInterleaver fs :=
  RealRooted.pairwiseCompatible_iff_hasCommonInterleaver_of_natDegree_le_one
    hpos hdeg

/-- Solved low-degree pairwise/full-family compatibility equivalence. -/
theorem pairwiseCompatible_iff_familyCompatible_of_natDegree_le_one
    {fs : List ℝ[X]}
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hdeg : ∀ f ∈ fs, f.natDegree ≤ 1) :
    PairwiseCompatible fs ↔ FamilyCompatible fs :=
  RealRooted.pairwiseCompatible_iff_familyCompatible_of_natDegree_le_one
    hpos hdeg

/-- Challenge-facing reduction for the left-oriented common-interleaver target. -/
theorem pairwiseCompatible_iff_commonLeftInterleaver_of_pairwiseLeftBridge
    {fs : List ℝ[X]}
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (htwo : CompatiblePairHasCommonLeftInterleaverStatement)
    (hglobal : PairwiseHasCommonLeftInterleaver fs → HasCommonLeftInterleaver fs) :
    PairwiseCompatible fs ↔ HasCommonLeftInterleaver fs :=
  RealRooted.pairwiseCompatible_iff_commonLeftInterleaver_of_pairwiseLeftBridge
    hpos htwo hglobal

/-- Challenge-facing direct left-oriented finite-family reduction after the
common-left upgrade: only the two-polynomial common-left bridge remains. -/
theorem pairwiseCompatible_iff_commonLeftInterleaver_of_pairwiseLeftBridge_direct
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, f.Splits)
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (htwo : CompatiblePairHasCommonLeftInterleaverStatement) :
    PairwiseCompatible fs ↔ HasCommonLeftInterleaver fs :=
  RealRooted.pairwiseCompatible_iff_commonLeftInterleaver_of_pairwiseLeftBridge_direct
    hrr hpos htwo

end ChudnovskySeymour
end Challenges
end RealRooted
