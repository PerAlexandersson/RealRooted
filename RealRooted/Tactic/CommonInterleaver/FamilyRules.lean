import RealRooted.Tactic.CommonInterleaver.AnalyticRules
import RealRooted.Tactic.CommonInterleaver.FamilySyntax

/-!
# Family common-interleaver tactic rules

Routing helpers and macro expansions for Chudnovsky--Seymour four-way
certificates and pairwise-to-family compatibility upgrades.
-/

open Polynomial

namespace RealRooted
namespace Tactic

private theorem pairwiseCommonInterleaver_boundaryRight_nonnegShift
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hboundary : PosComboNoCommonBoundaryRightPairOrientationStatement) :
    PairwiseCompatible fs ↔ HasCommonInterleaver fs :=
  pairwiseCompatible_iff_hasCommonInterleaver_of_fourWay <|
    chudnovskySeymour_fourWay_of_boundaryRightPairOrientation_via_nonnegShift
      (fs := fs) hrr hpos hboundary

private theorem pairwiseCommonInterleaver_boundaryRight_nonnegCoeffs
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hnn : ∀ f ∈ fs, HasNonnegCoeffs f)
    (hboundary : PosComboNoCommonBoundaryRightPairOrientationStatement) :
    PairwiseCompatible fs ↔ HasCommonInterleaver fs :=
  pairwiseCompatible_iff_hasCommonInterleaver_of_affineFamilyBridge_and_nonnegCoeffs
    (fs := fs) hrr hpos hnn
    (posComboNoCommonAffineFamily_of_boundaryRightPairOrientation hboundary)

private theorem pairwiseCommonInterleaver_posComboBridge
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hbridge : PosComboPairHasCommonInterleaverStatement) :
    PairwiseCompatible fs ↔ HasCommonInterleaver fs :=
  pairwiseCompatible_iff_hasCommonInterleaver_of_fourWay <|
    chudnovskySeymour_fourWay_of_posComboBridge
      (fs := fs) hrr hpos hbridge

private theorem pairwiseCommonInterleaver_noCommonOrientation_degreeClose
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (horient : PosComboNoCommonOrientationStatement)
    (hdegClose : PosComboNatDegreeCloseStatement) :
    PairwiseCompatible fs ↔ HasCommonInterleaver fs :=
  pairwiseCompatible_iff_hasCommonInterleaver_of_fourWay <|
    chudnovskySeymour_fourWay_of_noCommonOrientation_and_degreeClose
      (fs := fs) hrr hpos horient hdegClose

private theorem pairwiseFamilyCompatible_posComboBridge
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hbridge : PosComboPairHasCommonInterleaverStatement) :
    PairwiseCompatible fs ↔ FamilyCompatible fs :=
  pairwiseCompatible_iff_familyCompatible_of_commonInterleaver_forward hpos <|
    (pairwiseCommonInterleaver_posComboBridge
      (fs := fs) hrr hpos hbridge).1

private theorem pairwiseFamilyCompatible_noCommonOrientation_degreeClose
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (horient : PosComboNoCommonOrientationStatement)
    (hdegClose : PosComboNatDegreeCloseStatement) :
    PairwiseCompatible fs ↔ FamilyCompatible fs :=
  pairwiseCompatible_iff_familyCompatible_of_commonInterleaver_forward hpos <|
    (pairwiseCommonInterleaver_noCommonOrientation_degreeClose
      (fs := fs) hrr hpos horient hdegClose).1

macro_rules
  | `(tactic|
      rr_pairwise_common_interleaver_degree_split_nonnegShift using
        same_degree := $hsame:term,
        succ_degree := $hsucc:term,
        member_pos_lc := $hpos:term,
        pairwise_compatible := $hpair:term) =>
      `(tactic|
        exact pairwiseHasCommonInterleaver_of_pairwiseCompatible_of_pairDegreeSplit_via_nonnegShift
          $hsame $hsucc $hpos $hpair)
  | `(tactic|
      rr_pairwise_common_interleaver_rootCrossing using
        same_degree := $hsame:term,
        succ_degree := $hsucc:term,
        member_pos_lc := $hpos:term,
        pairwise_compatible := $hpair:term) =>
      `(tactic|
        exact pairwiseHasCommonInterleaver_of_pairwiseCompatible_of_rootCrossing
          $hsame $hsucc $hpos $hpair)
  | `(tactic|
      rr_pairwise_common_interleaver_rootCount using
        same_degree := $hsame:term,
        succ_degree := $hsucc:term,
        member_pos_lc := $hpos:term,
        pairwise_compatible := $hpair:term) =>
      `(tactic|
        exact pairwiseHasCommonInterleaver_of_pairwiseCompatible_of_rootCount
          $hsame $hsucc $hpos $hpair)
  | `(tactic|
      rr_pairwise_common_interleaver_rootCountAbove using
        same_degree := $hsame:term,
        succ_degree := $hsucc:term,
        member_pos_lc := $hpos:term,
        pairwise_compatible := $hpair:term) =>
      `(tactic|
        exact pairwiseHasCommonInterleaver_of_pairwiseCompatible_of_rootCountAboveBoth
          $hsame $hsucc $hpos $hpair)
  | `(tactic|
      rr_pairwise_common_interleaver_rootCountNonRoot using
        same_degree := $hsame:term,
        succ_degree := $hsucc:term,
        member_pos_lc := $hpos:term,
        pairwise_compatible := $hpair:term) =>
      `(tactic|
        exact pairwiseHasCommonInterleaver_of_pairwiseCompatible_of_rootCountNonRoot
          $hsame $hsucc $hpos $hpair)
  | `(tactic|
      rr_pairwise_common_interleaver_rootCountAboveNonRoot using
        same_degree := $hsame:term,
        succ_degree := $hsucc:term,
        member_pos_lc := $hpos:term,
        pairwise_compatible := $hpair:term) =>
      `(tactic|
        exact pairwiseHasCommonInterleaver_of_pairwiseCompatible_of_rootCountAboveBothNonRoot
          $hsame $hsucc $hpos $hpair)
  | `(tactic|
      rr_chudnovskySeymour_fourWay_rootCrossing using
        member_realrooted := $hrr:term,
        member_pos_lc := $hpos:term,
        same_degree := $hsame:term,
        succ_degree := $hsucc:term) =>
      `(tactic|
        exact chudnovskySeymour_fourWay_of_rootCrossing
          $hrr $hpos $hsame $hsucc)
  | `(tactic|
      rr_chudnovskySeymour_fourWay_rootCount using
        member_realrooted := $hrr:term,
        member_pos_lc := $hpos:term,
        same_degree := $hsame:term,
        succ_degree := $hsucc:term) =>
      `(tactic|
        exact chudnovskySeymour_fourWay_of_rootCrossing
          $hrr $hpos
          (RealRooted.posComboNoCommonSameDegreeRootCrossing_of_rootCount $hsame)
          (RealRooted.posComboNoCommonSuccDegreeRootCrossing_of_rootCount $hsucc))
  | `(tactic|
      rr_chudnovskySeymour_fourWay_rootCountAbove using
        member_realrooted := $hrr:term,
        member_pos_lc := $hpos:term,
        same_degree := $hsame:term,
        succ_degree := $hsucc:term) =>
      `(tactic|
        exact chudnovskySeymour_fourWay_of_rootCrossing
          $hrr $hpos
          (RealRooted.posComboNoCommonSameDegreeRootCrossing_of_rootCountAbove $hsame)
          (RealRooted.posComboNoCommonSuccDegreeRootCrossing_of_rootCountAbove $hsucc))
  | `(tactic|
      rr_chudnovskySeymour_fourWay_rootCountNonRoot using
        member_realrooted := $hrr:term,
        member_pos_lc := $hpos:term,
        same_degree := $hsame:term,
        succ_degree := $hsucc:term) =>
      `(tactic|
        exact chudnovskySeymour_fourWay_of_rootCrossing
          $hrr $hpos
          (RealRooted.posComboNoCommonSameDegreeRootCrossing_of_rootCountNonRoot
            $hsame)
          (RealRooted.posComboNoCommonSuccDegreeRootCrossing_of_rootCountNonRoot
            $hsucc))
  | `(tactic|
      rr_chudnovskySeymour_fourWay_rootCountAboveNonRoot using
        member_realrooted := $hrr:term,
        member_pos_lc := $hpos:term,
        same_degree := $hsame:term,
        succ_degree := $hsucc:term) =>
      `(tactic|
        exact chudnovskySeymour_fourWay_of_rootCrossing
          $hrr $hpos
          (RealRooted.posComboNoCommonSameDegreeRootCrossing_of_rootCountAboveNonRoot
            $hsame)
          (RealRooted.posComboNoCommonSuccDegreeRootCrossing_of_rootCountAboveNonRoot
            $hsucc))
  | `(tactic|
      rr_chudnovskySeymour_fourWay_degreeSplit_nonnegShift using
        member_realrooted := $hrr:term,
        member_pos_lc := $hpos:term,
        same_degree := $hsame:term,
        succ_degree := $hsucc:term) =>
      `(tactic|
        exact chudnovskySeymour_fourWay_of_pairDegreeSplit_via_nonnegShift
          $hrr $hpos $hsame $hsucc)
  | `(tactic|
      rr_chudnovskySeymour_fourWay_slotData_nonnegShift using
        member_realrooted := $hrr:term,
        member_pos_lc := $hpos:term,
        same_degree := $hsame:term,
        succ_degree := $hsucc:term) =>
      `(tactic|
        exact chudnovskySeymour_fourWay_of_slotData_via_nonnegShift
          $hrr $hpos $hsame $hsucc)
  | `(tactic|
      rr_chudnovskySeymour_fourWay_affineFamily_nonnegShift using
        member_realrooted := $hrr:term,
        member_pos_lc := $hpos:term,
        same_degree := $hsame:term,
        affine_family := $haff:term) =>
      `(tactic|
        exact
          chudnovskySeymour_fourWay_of_sameDegreeAlternative_and_affineFamily_via_nonnegShift
            $hrr $hpos $hsame $haff)
  | `(tactic|
      rr_chudnovskySeymour_fourWay_boundaryRight_nonnegShift using
        member_realrooted := $hrr:term,
        member_pos_lc := $hpos:term,
        boundary_right := $hboundary:term) =>
      `(tactic|
        exact
          chudnovskySeymour_fourWay_of_boundaryRightPairOrientation_via_nonnegShift
            $hrr $hpos $hboundary)
  | `(tactic|
      rr_chudnovskySeymour_fourWay_sameDegreePair_affineFamily_nonneg using
        member_realrooted := $hrr:term,
        member_pos_lc := $hpos:term,
        member_nonneg_coeffs := $hnn:term,
        same_degree := $hsame:term,
        affine_family := $haff:term) =>
      `(tactic|
        exact chudnovskySeymour_fourWay_of_sameDegreePair_and_affineFamily_nonneg
          $hrr $hpos $hnn $hsame $haff)
  | `(tactic|
      rr_chudnovskySeymour_fourWay_allCombo_nonnegCoeffs using
        member_realrooted := $hrr:term,
        member_pos_lc := $hpos:term,
        member_nonneg_coeffs := $hnn:term,
        all_combo := $hall:term) =>
      `(tactic|
        exact chudnovskySeymour_fourWay_of_allComboBridge_and_nonnegCoeffs
          $hrr $hpos $hnn $hall)
  | `(tactic|
      rr_chudnovskySeymour_fourWay_affineFamily_nonnegCoeffs using
        member_realrooted := $hrr:term,
        member_pos_lc := $hpos:term,
        member_nonneg_coeffs := $hnn:term,
        affine_family := $haff:term) =>
      `(tactic|
        exact chudnovskySeymour_fourWay_of_affineFamilyBridge_and_nonnegCoeffs
          $hrr $hpos $hnn $haff)
  | `(tactic|
      rr_chudnovskySeymour_fourWay_boundaryRight_nonnegCoeffs using
        member_realrooted := $hrr:term,
        member_pos_lc := $hpos:term,
        member_nonneg_coeffs := $hnn:term,
        boundary_right := $hboundary:term) =>
      `(tactic|
        exact
          chudnovskySeymour_fourWay_of_boundaryRightPairOrientation_and_nonnegCoeffs
            $hrr $hpos $hnn $hboundary)
  | `(tactic|
      rr_chudnovskySeymour_fourWay_posComboBridge using
        member_realrooted := $hrr:term,
        member_pos_lc := $hpos:term,
        pos_combo_bridge := $hbridge:term) =>
      `(tactic|
        exact chudnovskySeymour_fourWay_of_posComboBridge
          $hrr $hpos $hbridge)
  | `(tactic|
      rr_chudnovskySeymour_fourWay_noCommonOrientation_degreeClose using
        member_realrooted := $hrr:term,
        member_pos_lc := $hpos:term,
        orientation := $horient:term,
        degree_close := $hdegClose:term) =>
      `(tactic|
        exact chudnovskySeymour_fourWay_of_noCommonOrientation_and_degreeClose
          $hrr $hpos $horient $hdegClose)
  | `(tactic|
      rr_chudnovskySeymour_fourWay_noCommonOrientation_nonnegCoeffs using
        member_realrooted := $hrr:term,
        member_pos_lc := $hpos:term,
        member_nonneg_coeffs := $hnn:term,
        orientation := $horient:term) =>
      `(tactic|
        exact chudnovskySeymour_fourWay_of_noCommonOrientation_and_nonnegCoeffs
          $hrr $hpos $hnn $horient)
  | `(tactic|
      rr_chudnovskySeymour_fourWay_pairDegreeSplit_nonnegCoeffs using
        member_realrooted := $hrr:term,
        member_pos_lc := $hpos:term,
        member_nonneg_coeffs := $hnn:term,
        same_degree := $hsame:term,
        succ_degree := $hsucc:term) =>
      `(tactic|
        exact chudnovskySeymour_fourWay_of_pairDegreeSplit_and_nonnegCoeffs
          $hrr $hpos $hnn $hsame $hsucc)
  | `(tactic|
      rr_chudnovskySeymour_fourWay_degreeSplit_nonnegCoeffs using
        member_realrooted := $hrr:term,
        member_pos_lc := $hpos:term,
        member_nonneg_coeffs := $hnn:term,
        same_degree := $hsame:term,
        succ_degree := $hsucc:term) =>
      `(tactic|
        exact chudnovskySeymour_fourWay_of_degreeSplit_and_nonnegCoeffs
          $hrr $hpos $hnn $hsame $hsucc)
  | `(tactic|
      rr_chudnovskySeymour_fourWay_degree_le_one using
        member_pos_lc := $hpos:term,
        member_degree_le_one := $hdeg:term) =>
      `(tactic|
        exact chudnovskySeymour_fourWay_of_natDegree_le_one
          $hpos $hdeg)
  | `(tactic|
      rr_chudnovskySeymour_fourWay_degree_le_two using
        member_realrooted := $hrr:term,
        member_pos_lc := $hpos:term,
        member_degree_le_two := $hdeg:term) =>
      `(tactic|
        exact chudnovskySeymour_fourWay_of_natDegree_le_two
          $hrr $hpos $hdeg)
  | `(tactic|
      rr_pairwiseCompatible_iff_commonInterleaver_rootCrossing using
        member_realrooted := $hrr:term,
        member_pos_lc := $hpos:term,
        same_degree := $hsame:term,
        succ_degree := $hsucc:term) =>
      `(tactic|
        exact pairwiseCompatible_iff_hasCommonInterleaver_of_rootCrossing
          $hrr $hpos $hsame $hsucc)
  | `(tactic|
      rr_pairwiseCompatible_iff_commonInterleaver_rootCount using
        member_realrooted := $hrr:term,
        member_pos_lc := $hpos:term,
        same_degree := $hsame:term,
        succ_degree := $hsucc:term) =>
      `(tactic|
        exact pairwiseCompatible_iff_hasCommonInterleaver_of_rootCrossing
          $hrr $hpos
          (RealRooted.posComboNoCommonSameDegreeRootCrossing_of_rootCount $hsame)
          (RealRooted.posComboNoCommonSuccDegreeRootCrossing_of_rootCount $hsucc))
  | `(tactic|
      rr_pairwiseCompatible_iff_commonInterleaver_rootCountAbove using
        member_realrooted := $hrr:term,
        member_pos_lc := $hpos:term,
        same_degree := $hsame:term,
        succ_degree := $hsucc:term) =>
      `(tactic|
        exact pairwiseCompatible_iff_hasCommonInterleaver_of_rootCrossing
          $hrr $hpos
          (RealRooted.posComboNoCommonSameDegreeRootCrossing_of_rootCountAbove $hsame)
          (RealRooted.posComboNoCommonSuccDegreeRootCrossing_of_rootCountAbove $hsucc))
  | `(tactic|
      rr_pairwiseCompatible_iff_commonInterleaver_rootCountNonRoot using
        member_realrooted := $hrr:term,
        member_pos_lc := $hpos:term,
        same_degree := $hsame:term,
        succ_degree := $hsucc:term) =>
      `(tactic|
        exact pairwiseCompatible_iff_hasCommonInterleaver_of_rootCrossing
          $hrr $hpos
          (RealRooted.posComboNoCommonSameDegreeRootCrossing_of_rootCountNonRoot
            $hsame)
          (RealRooted.posComboNoCommonSuccDegreeRootCrossing_of_rootCountNonRoot
            $hsucc))
  | `(tactic|
      rr_pairwiseCompatible_iff_commonInterleaver_rootCountAboveNonRoot using
        member_realrooted := $hrr:term,
        member_pos_lc := $hpos:term,
        same_degree := $hsame:term,
        succ_degree := $hsucc:term) =>
      `(tactic|
        exact pairwiseCompatible_iff_hasCommonInterleaver_of_rootCrossing
          $hrr $hpos
          (RealRooted.posComboNoCommonSameDegreeRootCrossing_of_rootCountAboveNonRoot
            $hsame)
          (RealRooted.posComboNoCommonSuccDegreeRootCrossing_of_rootCountAboveNonRoot
            $hsucc))
  | `(tactic|
      rr_pairwiseCompatible_iff_commonInterleaver_degreeSplit_nonnegShift using
        member_realrooted := $hrr:term,
        member_pos_lc := $hpos:term,
        same_degree := $hsame:term,
        succ_degree := $hsucc:term) =>
      `(tactic|
        exact pairwiseCompatible_iff_hasCommonInterleaver_of_pairDegreeSplit_via_nonnegShift
          $hrr $hpos $hsame $hsucc)
  | `(tactic|
      rr_pairwiseCompatible_iff_commonInterleaver_slotData_nonnegShift using
        member_realrooted := $hrr:term,
        member_pos_lc := $hpos:term,
        same_degree := $hsame:term,
        succ_degree := $hsucc:term) =>
      `(tactic|
        exact pairwiseCompatible_iff_hasCommonInterleaver_of_slotData_via_nonnegShift
          $hrr $hpos $hsame $hsucc)
  | `(tactic|
      rr_pairwiseCompatible_iff_commonInterleaver_affineFamily_nonnegShift using
        member_realrooted := $hrr:term,
        member_pos_lc := $hpos:term,
        same_degree := $hsame:term,
        affine_family := $haff:term) =>
      `(tactic|
        exact pairwiseCompatible_iff_hasCommonInterleaver_via_nonnegShift
          $hrr $hpos $hsame $haff)
  | `(tactic|
      rr_pairwiseCompatible_iff_commonInterleaver_boundaryRight_nonnegShift using
        member_realrooted := $hrr:term,
        member_pos_lc := $hpos:term,
        boundary_right := $hboundary:term) =>
      `(tactic|
        exact pairwiseCommonInterleaver_boundaryRight_nonnegShift
          $hrr $hpos $hboundary)
  | `(tactic|
      rr_pairwiseCompatible_iff_commonInterleaver_sameDegreePair_affineFamily_nonneg
        using
        member_realrooted := $hrr:term,
        member_pos_lc := $hpos:term,
        member_nonneg_coeffs := $hnn:term,
        same_degree := $hsame:term,
        affine_family := $haff:term) =>
      `(tactic|
        exact
          pairwiseCompatible_iff_hasCommonInterleaver_of_sameDegreePair_and_affineFamily_nonneg
            $hrr $hpos $hnn $hsame $haff)
  | `(tactic|
      rr_pairwiseCompatible_iff_commonInterleaver_allCombo_nonnegCoeffs using
        member_realrooted := $hrr:term,
        member_pos_lc := $hpos:term,
        member_nonneg_coeffs := $hnn:term,
        all_combo := $hall:term) =>
      `(tactic|
        exact
          pairwiseCompatible_iff_hasCommonInterleaver_of_allComboBridge_and_nonnegCoeffs
            $hrr $hpos $hnn $hall)
  | `(tactic|
      rr_pairwiseCompatible_iff_commonInterleaver_affineFamily_nonnegCoeffs using
        member_realrooted := $hrr:term,
        member_pos_lc := $hpos:term,
        member_nonneg_coeffs := $hnn:term,
        affine_family := $haff:term) =>
      `(tactic|
        exact
          pairwiseCompatible_iff_hasCommonInterleaver_of_affineFamilyBridge_and_nonnegCoeffs
            $hrr $hpos $hnn $haff)
  | `(tactic|
      rr_pairwiseCompatible_iff_commonInterleaver_boundaryRight_nonnegCoeffs using
        member_realrooted := $hrr:term,
        member_pos_lc := $hpos:term,
        member_nonneg_coeffs := $hnn:term,
        boundary_right := $hboundary:term) =>
      `(tactic|
        exact pairwiseCommonInterleaver_boundaryRight_nonnegCoeffs
          $hrr $hpos $hnn $hboundary)
  | `(tactic|
      rr_pairwiseCompatible_iff_commonInterleaver_posComboBridge using
        member_realrooted := $hrr:term,
        member_pos_lc := $hpos:term,
        pos_combo_bridge := $hbridge:term) =>
      `(tactic|
        exact pairwiseCommonInterleaver_posComboBridge
          $hrr $hpos $hbridge)
  | `(tactic|
      rr_pairwiseCompatible_iff_commonInterleaver_noCommonOrientation_degreeClose
        using
        member_realrooted := $hrr:term,
        member_pos_lc := $hpos:term,
        orientation := $horient:term,
        degree_close := $hdegClose:term) =>
      `(tactic|
        exact pairwiseCommonInterleaver_noCommonOrientation_degreeClose
          $hrr $hpos $horient $hdegClose)
  | `(tactic|
      rr_pairwiseCompatible_iff_commonInterleaver_noCommonOrientation_nonnegCoeffs
        using
        member_realrooted := $hrr:term,
        member_pos_lc := $hpos:term,
        member_nonneg_coeffs := $hnn:term,
        orientation := $horient:term) =>
      `(tactic|
        exact
          pairwiseCompatible_iff_hasCommonInterleaver_of_noCommonOrientation_and_nonnegCoeffs
            $hrr $hpos $hnn $horient)
  | `(tactic|
      rr_pairwiseCompatible_iff_commonInterleaver_pairDegreeSplit_nonnegCoeffs
        using
        member_realrooted := $hrr:term,
        member_pos_lc := $hpos:term,
        member_nonneg_coeffs := $hnn:term,
        same_degree := $hsame:term,
        succ_degree := $hsucc:term) =>
      `(tactic|
        exact
          pairwiseCompatible_iff_hasCommonInterleaver_of_pairDegreeSplit_and_nonnegCoeffs
            $hrr $hpos $hnn $hsame $hsucc)
  | `(tactic|
      rr_pairwiseCompatible_iff_commonInterleaver_degreeSplit_nonnegCoeffs using
        member_realrooted := $hrr:term,
        member_pos_lc := $hpos:term,
        member_nonneg_coeffs := $hnn:term,
        same_degree := $hsame:term,
        succ_degree := $hsucc:term) =>
      `(tactic|
        exact
          pairwiseCompatible_iff_hasCommonInterleaver_of_degreeSplit_and_nonnegCoeffs
            $hrr $hpos $hnn $hsame $hsucc)
  | `(tactic|
      rr_chudnovskySeymour_pairwiseCompatible_iff_familyCompatible using
        member_realrooted := $hrr:term,
        member_pos_lc := $hpos:term) =>
      `(tactic|
        exact RealRooted.chudnovskySeymour_pairwiseCompatible_iff_familyCompatible
          $hrr $hpos)
  | `(tactic|
      rr_chudnovskySeymour_pairwiseCompatible_iff_commonLeftInterleaver using
        member_realrooted := $hrr:term,
        member_pos_lc := $hpos:term) =>
      `(tactic|
        exact
          RealRooted.chudnovskySeymour_pairwiseCompatible_iff_commonLeftInterleaver
            $hrr $hpos)
  | `(tactic|
      rr_chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver using
        member_realrooted := $hrr:term,
        member_pos_lc := $hpos:term) =>
      `(tactic|
        exact
          RealRooted.chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_of_pairBridge
            $hrr $hpos)
  | `(tactic|
      rr_pairwiseCompatible_iff_familyCompatible_rootCrossing using
        member_realrooted := $hrr:term,
        member_pos_lc := $hpos:term,
        same_degree := $hsame:term,
        succ_degree := $hsucc:term) =>
      `(tactic|
        exact pairwiseCompatible_iff_familyCompatible_of_rootCrossing
          $hrr $hpos $hsame $hsucc)
  | `(tactic|
      rr_pairwiseCompatible_iff_familyCompatible_rootCount using
        member_realrooted := $hrr:term,
        member_pos_lc := $hpos:term,
        same_degree := $hsame:term,
        succ_degree := $hsucc:term) =>
      `(tactic|
        exact pairwiseCompatible_iff_familyCompatible_of_rootCrossing
          $hrr $hpos
          (RealRooted.posComboNoCommonSameDegreeRootCrossing_of_rootCount $hsame)
          (RealRooted.posComboNoCommonSuccDegreeRootCrossing_of_rootCount $hsucc))
  | `(tactic|
      rr_pairwiseCompatible_iff_familyCompatible_rootCountAbove using
        member_realrooted := $hrr:term,
        member_pos_lc := $hpos:term,
        same_degree := $hsame:term,
        succ_degree := $hsucc:term) =>
      `(tactic|
        exact pairwiseCompatible_iff_familyCompatible_of_rootCrossing
          $hrr $hpos
          (RealRooted.posComboNoCommonSameDegreeRootCrossing_of_rootCountAbove $hsame)
          (RealRooted.posComboNoCommonSuccDegreeRootCrossing_of_rootCountAbove $hsucc))
  | `(tactic|
      rr_pairwiseCompatible_iff_familyCompatible_rootCountNonRoot using
        member_realrooted := $hrr:term,
        member_pos_lc := $hpos:term,
        same_degree := $hsame:term,
        succ_degree := $hsucc:term) =>
      `(tactic|
        exact pairwiseCompatible_iff_familyCompatible_of_rootCrossing
          $hrr $hpos
          (RealRooted.posComboNoCommonSameDegreeRootCrossing_of_rootCountNonRoot
            $hsame)
          (RealRooted.posComboNoCommonSuccDegreeRootCrossing_of_rootCountNonRoot
            $hsucc))
  | `(tactic|
      rr_pairwiseCompatible_iff_familyCompatible_rootCountAboveNonRoot using
        member_realrooted := $hrr:term,
        member_pos_lc := $hpos:term,
        same_degree := $hsame:term,
        succ_degree := $hsucc:term) =>
      `(tactic|
        exact pairwiseCompatible_iff_familyCompatible_of_rootCrossing
          $hrr $hpos
          (RealRooted.posComboNoCommonSameDegreeRootCrossing_of_rootCountAboveNonRoot
            $hsame)
          (RealRooted.posComboNoCommonSuccDegreeRootCrossing_of_rootCountAboveNonRoot
            $hsucc))
  | `(tactic|
      rr_pairwiseCompatible_iff_familyCompatible_degreeSplit_nonnegShift using
        member_realrooted := $hrr:term,
        member_pos_lc := $hpos:term,
        same_degree := $hsame:term,
        succ_degree := $hsucc:term) =>
      `(tactic|
        exact pairwiseCompatible_iff_familyCompatible_of_pairDegreeSplit_via_nonnegShift
          $hrr $hpos $hsame $hsucc)
  | `(tactic|
      rr_pairwiseCompatible_iff_familyCompatible_slotData_nonnegShift using
        member_realrooted := $hrr:term,
        member_pos_lc := $hpos:term,
        same_degree := $hsame:term,
        succ_degree := $hsucc:term) =>
      `(tactic|
        exact pairwiseCompatible_iff_familyCompatible_of_slotData_via_nonnegShift
          $hrr $hpos $hsame $hsucc)
  | `(tactic|
      rr_pairwiseCompatible_iff_familyCompatible_affineFamily_nonnegShift using
        member_realrooted := $hrr:term,
        member_pos_lc := $hpos:term,
        same_degree := $hsame:term,
        affine_family := $haff:term) =>
      `(tactic|
        exact pairwiseCompatible_iff_familyCompatible_via_nonnegShift
          $hrr $hpos $hsame $haff)
  | `(tactic|
      rr_pairwiseCompatible_iff_familyCompatible_boundaryRight_nonnegShift using
        member_realrooted := $hrr:term,
        member_pos_lc := $hpos:term,
        boundary_right := $hboundary:term) =>
      `(tactic|
        exact
          pairwiseCompatible_iff_familyCompatible_of_boundaryRightPairOrientation_via_nonnegShift
            $hrr $hpos $hboundary)
  | `(tactic|
      rr_pairwiseCompatible_iff_familyCompatible_sameDegreePair_affineFamily_nonneg
        using
        member_realrooted := $hrr:term,
        member_pos_lc := $hpos:term,
        member_nonneg_coeffs := $hnn:term,
        same_degree := $hsame:term,
        affine_family := $haff:term) =>
      `(tactic|
        exact
          pairwiseCompatible_iff_familyCompatible_of_sameDegreePair_and_affineFamily_nonneg
            $hrr $hpos $hnn $hsame $haff)
  | `(tactic|
      rr_pairwiseCompatible_iff_familyCompatible_allCombo_nonnegCoeffs using
        member_realrooted := $hrr:term,
        member_pos_lc := $hpos:term,
        member_nonneg_coeffs := $hnn:term,
        all_combo := $hall:term) =>
      `(tactic|
        exact
          pairwiseCompatible_iff_familyCompatible_of_allComboBridge_and_nonnegCoeffs
            $hrr $hpos $hnn $hall)
  | `(tactic|
      rr_pairwiseCompatible_iff_familyCompatible_affineFamily_nonnegCoeffs using
        member_realrooted := $hrr:term,
        member_pos_lc := $hpos:term,
        member_nonneg_coeffs := $hnn:term,
        affine_family := $haff:term) =>
      `(tactic|
        exact
          pairwiseCompatible_iff_familyCompatible_of_affineFamilyBridge_and_nonnegCoeffs
            $hrr $hpos $hnn $haff)
  | `(tactic|
      rr_pairwiseCompatible_iff_familyCompatible_boundaryRight_nonnegCoeffs using
        member_realrooted := $hrr:term,
        member_pos_lc := $hpos:term,
        member_nonneg_coeffs := $hnn:term,
        boundary_right := $hboundary:term) =>
      `(tactic|
        exact
          pairwiseCompatible_iff_familyCompatible_of_boundaryRightPairOrientation_and_nonnegCoeffs
            $hrr $hpos $hnn $hboundary)
  | `(tactic|
      rr_pairwiseCompatible_iff_familyCompatible_posComboBridge using
        member_realrooted := $hrr:term,
        member_pos_lc := $hpos:term,
        pos_combo_bridge := $hbridge:term) =>
      `(tactic|
        exact pairwiseFamilyCompatible_posComboBridge
          $hrr $hpos $hbridge)
  | `(tactic|
      rr_pairwiseCompatible_iff_familyCompatible_noCommonOrientation_degreeClose
        using
        member_realrooted := $hrr:term,
        member_pos_lc := $hpos:term,
        orientation := $horient:term,
        degree_close := $hdegClose:term) =>
      `(tactic|
        exact pairwiseFamilyCompatible_noCommonOrientation_degreeClose
          $hrr $hpos $horient $hdegClose)
  | `(tactic|
      rr_pairwiseCompatible_iff_familyCompatible_noCommonOrientation_nonnegCoeffs
        using
        member_realrooted := $hrr:term,
        member_pos_lc := $hpos:term,
        member_nonneg_coeffs := $hnn:term,
        orientation := $horient:term) =>
      `(tactic|
        exact
          pairwiseCompatible_iff_familyCompatible_of_noCommonOrientation_and_nonnegCoeffs
            $hrr $hpos $hnn $horient)
  | `(tactic|
      rr_pairwiseCompatible_iff_familyCompatible_pairDegreeSplit_nonnegCoeffs
        using
        member_realrooted := $hrr:term,
        member_pos_lc := $hpos:term,
        member_nonneg_coeffs := $hnn:term,
        same_degree := $hsame:term,
        succ_degree := $hsucc:term) =>
      `(tactic|
        exact
          pairwiseCompatible_iff_familyCompatible_of_pairDegreeSplit_and_nonnegCoeffs
            $hrr $hpos $hnn $hsame $hsucc)
  | `(tactic|
      rr_pairwiseCompatible_iff_familyCompatible_degreeSplit_nonnegCoeffs using
        member_realrooted := $hrr:term,
        member_pos_lc := $hpos:term,
        member_nonneg_coeffs := $hnn:term,
        same_degree := $hsame:term,
        succ_degree := $hsucc:term) =>
      `(tactic|
        exact
          pairwiseCompatible_iff_familyCompatible_of_degreeSplit_and_nonnegCoeffs
            $hrr $hpos $hnn $hsame $hsucc)

end Tactic
end RealRooted
