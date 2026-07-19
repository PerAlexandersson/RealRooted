import RealRooted.Tactic.CommonInterleaver

open Polynomial

namespace RealRooted
namespace Tactic

example {f g : ℝ[X]} (h : Compatible f g) :
    Compatible g f := by
  rr_compatible_comm using compatible := h

example {f g : ℝ[X]} {r : ℝ} (h : Compatible f g) :
    Compatible (f.comp (X + C r)) (g.comp (X + C r)) := by
  rr_compatible_comp_X_add_C using compatible := h, shift := r

example {f g : ℝ[X]} {N : ℕ}
    (h : Compatible f g)
    (hfN : f.natDegree ≤ N)
    (hgN : g.natDegree ≤ N) :
    Compatible (reflect N f) (reflect N g) := by
  rr_compatible_reflect using
    compatible := h,
    left_degree_bound := hfN,
    right_degree_bound := hgN

example {f g : ℝ[X]} {N : ℕ}
    (hfN : f.natDegree ≤ N)
    (hgN : g.natDegree ≤ N) :
    Compatible (reflect N f) (reflect N g) ↔ Compatible f g := by
  rr_compatible_reflect_iff using
    left_degree_bound := hfN,
    right_degree_bound := hgN

example {f g : ℝ[X]} (h : Compatible f g) :
    Compatible f.derivative g.derivative := by
  rr_compatible_derivative using compatible := h

example {f g : ℝ[X]}
    (h : Compatible f g)
    (hf_pos : HasPosLeadingCoeff f) :
    (f ≠ 0 ∧ f.Splits) := by
  rr_compatible_left_realrooted using compatible := h, left_pos_lc := hf_pos

example {f g : ℝ[X]}
    (h : Compatible f g)
    (hg_pos : HasPosLeadingCoeff g) :
    (g ≠ 0 ∧ g.Splits) := by
  rr_compatible_right_realrooted using compatible := h, right_pos_lc := hg_pos

example {f g : ℝ[X]}
    (h : Compatible f g)
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g) :
    g.natDegree ≤ f.natDegree + 1 := by
  rr_compatible_right_degree_le_succ using
    compatible := h,
    left_pos_lc := hf_pos,
    right_pos_lc := hg_pos

example {f g : ℝ[X]}
    (h : Compatible f g)
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g) :
    f.natDegree ≤ g.natDegree + 1 ∧
      g.natDegree ≤ f.natDegree + 1 := by
  rr_compatible_degree_close using
    compatible := h,
    left_pos_lc := hf_pos,
    right_pos_lc := hg_pos

example {f g : ℝ[X]}
    (h : Compatible f g)
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g) :
    PosComboRealRooted f g := by
  rr_compatible_to_pos_combo using
    compatible := h,
    left_pos_lc := hf_pos,
    right_pos_lc := hg_pos

example {f g : ℝ[X]}
    (hfg : PosComboRealRooted f g)
    (hf : f ≠ 0 ∧ f.Splits)
    (hg : g ≠ 0 ∧ g.Splits) :
    Compatible f g := by
  rr_compatible_of_pos_combo using
    pos_combo := hfg,
    left_realrooted := hf,
    right_realrooted := hg

example {f g : ℝ[X]}
    (hfg : PosComboRealRooted f g)
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hdeg : g.natDegree = f.natDegree) :
    Compatible f g := by
  rr_compatible_of_pos_combo_same_degree using
    pos_combo := hfg,
    left_pos_lc := hf_pos,
    right_pos_lc := hg_pos,
    same_degree := hdeg

example {f g : ℝ[X]}
    (hfg : PosComboRealRooted f g)
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hdeg : g.natDegree = f.natDegree + 1)
    (hf_splits : f.Splits) :
    Compatible f g := by
  rr_compatible_of_pos_combo_succ_degree using
    pos_combo := hfg,
    left_pos_lc := hf_pos,
    right_pos_lc := hg_pos,
    succ_degree := hdeg,
    left_splits := hf_splits

example {f g h : ℝ[X]}
    (hhf : Prec h f)
    (hhg : Prec h g)
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g) :
    Compatible f g := by
  rr_compatible_of_common_left using
    common_to_left := hhf,
    common_to_right := hhg,
    left_pos_lc := hf_pos,
    right_pos_lc := hg_pos

example {f g h : ℝ[X]}
    (hfh : Prec f h)
    (hgh : Prec g h)
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g) :
    Compatible f g := by
  rr_compatible_of_common_right using
    left_to_common := hfh,
    right_to_common := hgh,
    left_pos_lc := hf_pos,
    right_pos_lc := hg_pos

example {f g : ℝ[X]} {r : ℝ} (hfg : PosComboRealRooted f g) :
    PosComboRealRooted (f.comp (X + C r)) (g.comp (X + C r)) := by
  rr_pos_combo_comp_X_add_C using pos_combo := hfg, shift := r

example {fs : List ℝ[X]}
    (hcommon : HasCommonLeftInterleaver fs)
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f) :
    PairwiseCompatible fs := by
  rr_pairwise_compatible_of_common_left using
    common_left := hcommon,
    member_pos_lc := hpos

example {fs : List ℝ[X]}
    (hpair : PairwiseHasCommonLeftInterleaver fs)
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f) :
    PairwiseCompatible fs := by
  rr_pairwise_compatible_of_pairwise_common_left using
    pairwise_common_left := hpair,
    member_pos_lc := hpos

example {fs : List ℝ[X]}
    (hcommon : HasCommonInterleaver fs)
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f) :
    PairwiseCompatible fs := by
  rr_pairwise_compatible_of_common_right using
    common_right := hcommon,
    member_pos_lc := hpos

example {fs : List ℝ[X]}
    (hpair : PairwiseHasCommonInterleaver fs)
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f) :
    PairwiseCompatible fs := by
  rr_pairwise_compatible_of_pairwise_common_right using
    pairwise_common_right := hpair,
    member_pos_lc := hpos

example {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, f.Splits)
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hpair : PairwiseHasCommonInterleaver fs) :
    HasCommonInterleaver fs := by
  rr_common_interleaver_of_pairwise using
    member_splits := hrr,
    member_pos_lc := hpos,
    pairwise_common := hpair

example {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, f.Splits)
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hpair : PairwiseHasCommonLeftInterleaver fs) :
    HasCommonLeftInterleaver fs := by
  rr_common_left_interleaver_of_pairwise using
    member_splits := hrr,
    member_pos_lc := hpos,
    pairwise_common_left := hpair

example :
    CommonInterleaverFamilyUpgradeStatement := by
  rr_common_interleaver_family_upgrade

example :
    CommonLeftInterleaverFamilyUpgradeStatement := by
  rr_common_left_interleaver_family_upgrade

example {fs : List ℝ[X]}
    (hcommon : HasCommonInterleaver fs)
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hne : fs ≠ []) :
    (fs.sum ≠ 0 ∧ fs.sum.Splits) := by
  rr_common_interleaver_sum_realrooted using
    common_right := hcommon,
    member_pos_lc := hpos,
    nonempty := hne

example {fs : List ℝ[X]}
    (hcommon : HasCommonLeftInterleaver fs)
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hne : fs ≠ []) :
    (fs.sum ≠ 0 ∧ fs.sum.Splits) := by
  rr_common_left_interleaver_sum_realrooted using
    common_left := hcommon,
    member_pos_lc := hpos,
    nonempty := hne

example :
    PosComboNoCommonSameDegreeRootCountAboveNonRootNonnegStatement := by
  rr_sameDegree_rootCountAbove_nonRoot_analytic

example :
    PosComboNoCommonSameDegreePairHasCommonInterleaverNonnegStatement := by
  rr_sameDegree_pair_common_interleaver_analytic

example :
    PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement := by
  rr_succDegree_pair_common_interleaver_local_lower

example
    (hle2 : CompatibleSuccDegreeRootCountAboveLeTwoStatement)
    (hgap : CompatibleSuccDegreeRootCountAboveNoGapTwoStatement) :
    CompatibleSuccDegreeRootCountAboveNonRootStatement := by
  rr_compatibleSuccDegree_rootCountAbove_nonRoot_of_leTwo_noGapTwo using
    le_two := hle2,
    no_gap_two := hgap

example
    (hcount : CompatibleSuccDegreeRootCountAboveNonRootStatement) :
    PosComboNoCommonSuccDegreeRootCountAboveNonRootNonnegStatement := by
  rr_posComboSuccDegree_rootCountAbove_nonRoot_of_compatible using
    root_count := hcount

example
    (hcount : CompatibleSuccDegreeRootCountAboveNonRootStatement) :
    CompatibleSuccDegreeClosedSegmentCountEqStatement := by
  rr_compatibleSuccDegree_closedSegmentCountEq_of_nonRoot using
    root_count := hcount

example
    (hcount : CompatibleSuccDegreeRootCountAboveNonRootStatement) :
    CompatibleSuccDegreeRootCountAboveLeTwoStatement := by
  rr_compatibleSuccDegree_rootCountAbove_leTwo_of_nonRoot using
    root_count := hcount

example
    (hgap : CompatibleSuccDegreeRootCountAboveNoGapTwoStatement) :
    CompatibleSuccDegreeRootCountAboveNonRootStatement := by
  rr_compatibleSuccDegree_rootCountAbove_nonRoot_of_noGapTwo using
    no_gap_two := hgap

example
    (hgap : CompatibleSuccDegreeClosedSegmentNoGapTwoStatement) :
    CompatibleSuccDegreeRootCountAboveNonRootStatement := by
  rr_compatibleSuccDegree_rootCountAbove_nonRoot_of_closedSegment using
    no_gap_two := hgap

example
    (hcount : CompatibleSuccDegreeClosedSegmentCountEqStatement) :
    CompatibleSuccDegreeRootCountAboveNonRootStatement := by
  rr_compatibleSuccDegree_rootCountAbove_nonRoot_of_countEq using
    count_eq := hcount

example :
    CompatibleSuccDegreeClosedSegmentCountEqStatement ↔
      CompatibleSuccDegreeRootCountAboveNonRootStatement := by
  rr_compatibleSuccDegree_closedSegmentCountEq_iff_nonRoot

example
    (hgap : CompatibleSuccDegreeRightFamilyNoGapTwoStatement) :
    CompatibleSuccDegreeRootCountAboveNonRootStatement := by
  rr_compatibleSuccDegree_rootCountAbove_nonRoot_of_rightFamily using
    no_gap_two := hgap

example
    (hgap : CompatibleSuccDegreeEndpointSignNoGapTwoStatement) :
    CompatibleSuccDegreeRootCountAboveNonRootStatement := by
  rr_compatibleSuccDegree_rootCountAbove_nonRoot_of_endpointSign using
    no_gap_two := hgap

example
    (hgap : CompatibleSuccDegreeEndpointSignLowerNoGapStatement) :
    CompatibleSuccDegreeRootCountAboveNonRootStatement := by
  rr_compatibleSuccDegree_rootCountAbove_nonRoot_of_endpointSignLower using
    no_gap := hgap

example
    (hcount : CompatibleSuccDegreeEndpointSignLowerCountEqStatement) :
    CompatibleSuccDegreeRootCountAboveNonRootStatement := by
  rr_compatibleSuccDegree_rootCountAbove_nonRoot_of_lowerCountEq using
    count_eq := hcount

example
    (hcount : CompatibleSuccDegreeClosedSegmentCountEqStatement) :
    PosComboNoCommonSuccDegreeRootCountAboveNonRootNonnegStatement := by
  rr_posComboSuccDegree_rootCountAbove_nonRoot_of_countEq using
    count_eq := hcount

example
    (hgap : CompatibleSuccDegreeClosedSegmentNoGapTwoStatement) :
    PosComboNoCommonSuccDegreeRootCountAboveNonRootNonnegStatement := by
  rr_posComboSuccDegree_rootCountAbove_nonRoot_of_closedSegment using
    no_gap_two := hgap

example
    (hgap : CompatibleSuccDegreeRightFamilyNoGapTwoStatement) :
    PosComboNoCommonSuccDegreeRootCountAboveNonRootNonnegStatement := by
  rr_posComboSuccDegree_rootCountAbove_nonRoot_of_rightFamily using
    no_gap_two := hgap

example
    (hgap : CompatibleSuccDegreeEndpointSignNoGapTwoStatement) :
    PosComboNoCommonSuccDegreeRootCountAboveNonRootNonnegStatement := by
  rr_posComboSuccDegree_rootCountAbove_nonRoot_of_endpointSign using
    no_gap_two := hgap

example
    (hgap : CompatibleSuccDegreeEndpointSignLowerNoGapStatement) :
    PosComboNoCommonSuccDegreeRootCountAboveNonRootNonnegStatement := by
  rr_posComboSuccDegree_rootCountAbove_nonRoot_of_endpointSignLower using
    no_gap := hgap

example
    (hcount : CompatibleSuccDegreeEndpointSignLowerCountEqStatement) :
    PosComboNoCommonSuccDegreeRootCountAboveNonRootNonnegStatement := by
  rr_posComboSuccDegree_rootCountAbove_nonRoot_of_lowerCountEq using
    count_eq := hcount

example
    (hcross : PosComboNoCommonSuccDegreeRootCrossingNonnegStatement) :
    PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement := by
  rr_succDegree_pair_common_interleaver_rootCrossing using
    root_crossing := hcross

example
    (hcount : PosComboNoCommonSuccDegreeRootCountNonnegStatement) :
    PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement := by
  rr_succDegree_pair_common_interleaver_rootCount using
    root_count := hcount

example
    (hcount : PosComboNoCommonSuccDegreeRootCountAboveNonnegStatement) :
    PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement := by
  rr_succDegree_pair_common_interleaver_rootCountAbove using
    root_count_above := hcount

example
    (hcount : PosComboNoCommonSuccDegreeRootCountNonRootNonnegStatement) :
    PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement := by
  rr_succDegree_pair_common_interleaver_rootCountNonRoot using
    root_count := hcount

example
    (hcount : PosComboNoCommonSuccDegreeRootCountAboveNonRootNonnegStatement) :
    PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement := by
  rr_succDegree_pair_common_interleaver_rootCountAboveNonRoot using
    root_count_above := hcount

example
    (hcount : CompatibleSuccDegreeClosedSegmentCountEqStatement) :
    PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement := by
  rr_succDegree_pair_common_interleaver_closedSegmentCountEq using
    count_eq := hcount

example
    (hgap : CompatibleSuccDegreeClosedSegmentNoGapTwoStatement) :
    PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement := by
  rr_succDegree_pair_common_interleaver_closedSegmentNoGapTwo using
    no_gap_two := hgap

example
    (hgap : CompatibleSuccDegreeRightFamilyNoGapTwoStatement) :
    PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement := by
  rr_succDegree_pair_common_interleaver_rightFamilyNoGapTwo using
    no_gap_two := hgap

example
    (hgap : CompatibleSuccDegreeEndpointSignNoGapTwoStatement) :
    PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement := by
  rr_succDegree_pair_common_interleaver_endpointSignNoGapTwo using
    no_gap_two := hgap

example
    (hgap : CompatibleSuccDegreeEndpointSignLowerNoGapStatement) :
    PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement := by
  rr_succDegree_pair_common_interleaver_endpointSignLowerNoGap using
    no_gap := hgap

example
    (hcount : CompatibleSuccDegreeEndpointSignLowerCountEqStatement) :
    PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement := by
  rr_succDegree_pair_common_interleaver_endpointSignLowerCountEq using
    count_eq := hcount

example
    (horient :
      ∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        g.natDegree = f.natDegree + 1 →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        f.Splits →
        f.coeff 0 ≠ 0 →
        g.coeff 0 = 0 →
        Prec f g) :
    PosComboNoCommonSuccDegreeRootCountLeadRightZeroDivXPrecStatement := by
  rr_succDegree_rootCountLeadRightZero_divXPrec_of_prec using
    orientation := horient

example
    (hdivX : PosComboNoCommonSuccDegreeRootCountLeadRightZeroDivXPrecStatement) :
    PosComboNoCommonSuccDegreeRootCountLeadRightZeroNonnegStatement := by
  rr_succDegree_rootCountLeadRightZero_of_divXPrec using
    divX_prec := hdivX

example
    (hboth : PosComboNoCommonSuccDegreeRootCountLeadBothNonzeroNonnegStatement)
    (hright : PosComboNoCommonSuccDegreeRootCountLeadRightZeroNonnegStatement) :
    PosComboNoCommonSuccDegreeRootCountLeadNonnegStatement := by
  rr_succDegree_rootCountLead_of_bothNonzero_and_rightZero using
    both_nonzero := hboth,
    right_zero := hright

example
    (hboth : PosComboNoCommonSuccDegreeRootCountLeadBothNonzeroNonnegStatement)
    (hdivX : PosComboNoCommonSuccDegreeRootCountLeadRightZeroDivXPrecStatement) :
    PosComboNoCommonSuccDegreeRootCountLeadNonnegStatement := by
  rr_succDegree_rootCountLead_of_bothNonzero_and_divXPrec using
    both_nonzero := hboth,
    divX_prec := hdivX

example
    (horient : PosComboNoCommonSuccDegreeRootCountResidualPrecStatement) :
    PosComboNoCommonSuccDegreeRootCountResidualNonnegStatement := by
  rr_succDegree_rootCountResidual_of_prec using
    orientation := horient

example
    (hlead : PosComboNoCommonSuccDegreeRootCountLeadNonnegStatement)
    (hres : PosComboNoCommonSuccDegreeRootCountResidualNonnegStatement) :
    PosComboNoCommonSuccDegreeRootCountNonnegStatement := by
  rr_succDegree_rootCount_of_residual_and_lead using
    lead := hlead,
    residual := hres

example
    (hlead : PosComboNoCommonSuccDegreeRootCountLeadNonnegStatement)
    (hres : PosComboNoCommonSuccDegreeRootCountResidualNonnegStatement) :
    PosComboNoCommonSuccDegreeRootCountAboveNonnegStatement := by
  rr_succDegree_rootCountAbove_of_residual_and_lead using
    lead := hlead,
    residual := hres

example
    (hlead : PosComboNoCommonSuccDegreeRootCountLeadNonnegStatement)
    (hres : PosComboNoCommonSuccDegreeRootCountResidualNonnegStatement) :
    PosComboNoCommonSuccDegreeRootCrossingNonnegStatement := by
  rr_succDegree_rootCrossing_of_residual_and_lead using
    lead := hlead,
    residual := hres

example
    (hlead : PosComboNoCommonSuccDegreeRootCountLeadNonnegStatement)
    (hres : PosComboNoCommonSuccDegreeRootCountResidualNonnegStatement) :
    PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement := by
  rr_succDegree_pair_common_interleaver_residual_and_lead using
    lead := hlead,
    residual := hres

example
    (hboth : PosComboNoCommonSuccDegreeRootCountLeadBothNonzeroNonnegStatement)
    (hdivX : PosComboNoCommonSuccDegreeRootCountLeadRightZeroDivXPrecStatement)
    (hres : PosComboNoCommonSuccDegreeRootCountResidualNonnegStatement) :
    PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement := by
  rr_succDegree_pair_common_interleaver_residual_bothNonzero_divXPrec using
    both_nonzero := hboth,
    divX_prec := hdivX,
    residual := hres

example
    (hres : PosComboNoCommonSuccDegreeRootCountResidualPrecStatement)
    (hboth : PosComboNoCommonSuccDegreeRootCountLeadBothNonzeroNonnegStatement)
    (hdivX : PosComboNoCommonSuccDegreeRootCountLeadRightZeroDivXPrecStatement) :
    PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement := by
  rr_succDegree_pair_common_interleaver_residualPrec_bothNonzero_divXPrec using
    residual_prec := hres,
    both_nonzero := hboth,
    divX_prec := hdivX

example
    (hsame : PosComboNoCommonSameDegreePairHasCommonInterleaverNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement) :
    CompatiblePairHasCommonInterleaverStatement := by
  rr_compatible_pair_common_interleaver_degree_split_nonnegShift using
    same_degree := hsame,
    succ_degree := hsucc

example
    (hsame : PosComboNoCommonSameDegreeRootCrossingNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreeRootCrossingNonnegStatement) :
    CompatiblePairHasCommonInterleaverStatement := by
  rr_compatible_pair_common_interleaver_rootCrossing using
    same_degree := hsame,
    succ_degree := hsucc

example
    (hsame : PosComboNoCommonSameDegreeRootCountNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreeRootCountNonnegStatement) :
    CompatiblePairHasCommonInterleaverStatement := by
  rr_compatible_pair_common_interleaver_rootCount using
    same_degree := hsame,
    succ_degree := hsucc

example
    (hsame : PosComboNoCommonSameDegreeRootCountAboveNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreeRootCountAboveNonnegStatement) :
    CompatiblePairHasCommonInterleaverStatement := by
  rr_compatible_pair_common_interleaver_rootCountAbove using
    same_degree := hsame,
    succ_degree := hsucc

example
    (hsame : PosComboNoCommonSameDegreeRootCountNonRootNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreeRootCountNonRootNonnegStatement) :
    CompatiblePairHasCommonInterleaverStatement := by
  rr_compatible_pair_common_interleaver_rootCountNonRoot using
    same_degree := hsame,
    succ_degree := hsucc

example
    (hsame : PosComboNoCommonSameDegreeRootCountAboveNonRootNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreeRootCountAboveNonRootNonnegStatement) :
    CompatiblePairHasCommonInterleaverStatement := by
  rr_compatible_pair_common_interleaver_rootCountAboveNonRoot using
    same_degree := hsame,
    succ_degree := hsucc

example :
    CompatiblePairHasCommonInterleaverStatement := by
  rr_chudnovskySeymour_compatible_pair_common_interleaver_statement

example :
    CompatiblePairHasCommonLeftInterleaverPosStatement := by
  rr_chudnovskySeymour_compatible_pair_common_left_interleaver_statement

example {f g : ℝ[X]}
    (hf : HasPosLeadingCoeff f) (hg : HasPosLeadingCoeff g)
    (hcomp : Compatible f g) :
    ∃ k : ℝ[X], Prec f k ∧ Prec g k := by
  rr_chudnovskySeymour_compatible_pair_common_interleaver using
    left_pos_lc := hf,
    right_pos_lc := hg,
    compatible := hcomp

example {f g : ℝ[X]}
    (hf : HasPosLeadingCoeff f) (hg : HasPosLeadingCoeff g)
    (hcomp : Compatible f g) :
    ∃ k : ℝ[X], Prec k f ∧ Prec k g := by
  rr_chudnovskySeymour_compatible_pair_common_left_interleaver using
    left_pos_lc := hf,
    right_pos_lc := hg,
    compatible := hcomp

example {fs : List ℝ[X]}
    (hsame : PosComboNoCommonSameDegreePairHasCommonInterleaverNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement)
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hpair : PairwiseCompatible fs) :
    PairwiseHasCommonInterleaver fs := by
  rr_pairwise_common_interleaver_degree_split_nonnegShift using
    same_degree := hsame,
    succ_degree := hsucc,
    member_pos_lc := hpos,
    pairwise_compatible := hpair

example {fs : List ℝ[X]}
    (hsame : PosComboNoCommonSameDegreeRootCrossingNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreeRootCrossingNonnegStatement)
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hpair : PairwiseCompatible fs) :
    PairwiseHasCommonInterleaver fs := by
  rr_pairwise_common_interleaver_rootCrossing using
    same_degree := hsame,
    succ_degree := hsucc,
    member_pos_lc := hpos,
    pairwise_compatible := hpair

example {fs : List ℝ[X]}
    (hsame : PosComboNoCommonSameDegreeRootCountNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreeRootCountNonnegStatement)
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hpair : PairwiseCompatible fs) :
    PairwiseHasCommonInterleaver fs := by
  rr_pairwise_common_interleaver_rootCount using
    same_degree := hsame,
    succ_degree := hsucc,
    member_pos_lc := hpos,
    pairwise_compatible := hpair

example {fs : List ℝ[X]}
    (hsame : PosComboNoCommonSameDegreeRootCountAboveNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreeRootCountAboveNonnegStatement)
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hpair : PairwiseCompatible fs) :
    PairwiseHasCommonInterleaver fs := by
  rr_pairwise_common_interleaver_rootCountAbove using
    same_degree := hsame,
    succ_degree := hsucc,
    member_pos_lc := hpos,
    pairwise_compatible := hpair

example {fs : List ℝ[X]}
    (hsame : PosComboNoCommonSameDegreeRootCountNonRootNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreeRootCountNonRootNonnegStatement)
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hpair : PairwiseCompatible fs) :
    PairwiseHasCommonInterleaver fs := by
  rr_pairwise_common_interleaver_rootCountNonRoot using
    same_degree := hsame,
    succ_degree := hsucc,
    member_pos_lc := hpos,
    pairwise_compatible := hpair

example {fs : List ℝ[X]}
    (hsame : PosComboNoCommonSameDegreeRootCountAboveNonRootNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreeRootCountAboveNonRootNonnegStatement)
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hpair : PairwiseCompatible fs) :
    PairwiseHasCommonInterleaver fs := by
  rr_pairwise_common_interleaver_rootCountAboveNonRoot using
    same_degree := hsame,
    succ_degree := hsucc,
    member_pos_lc := hpos,
    pairwise_compatible := hpair

example {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hsame : PosComboNoCommonSameDegreeRootCrossingNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreeRootCrossingNonnegStatement) :
    ChudnovskySeymourFourWayPackage fs := by
  rr_chudnovskySeymour_fourWay_rootCrossing using
    member_realrooted := hrr,
    member_pos_lc := hpos,
    same_degree := hsame,
    succ_degree := hsucc

example {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hsame : PosComboNoCommonSameDegreeRootCountNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreeRootCountNonnegStatement) :
    ChudnovskySeymourFourWayPackage fs := by
  rr_chudnovskySeymour_fourWay_rootCount using
    member_realrooted := hrr,
    member_pos_lc := hpos,
    same_degree := hsame,
    succ_degree := hsucc

example {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hsame : PosComboNoCommonSameDegreeRootCountAboveNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreeRootCountAboveNonnegStatement) :
    ChudnovskySeymourFourWayPackage fs := by
  rr_chudnovskySeymour_fourWay_rootCountAbove using
    member_realrooted := hrr,
    member_pos_lc := hpos,
    same_degree := hsame,
    succ_degree := hsucc

example {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hsame : PosComboNoCommonSameDegreeRootCountNonRootNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreeRootCountNonRootNonnegStatement) :
    ChudnovskySeymourFourWayPackage fs := by
  rr_chudnovskySeymour_fourWay_rootCountNonRoot using
    member_realrooted := hrr,
    member_pos_lc := hpos,
    same_degree := hsame,
    succ_degree := hsucc

example {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hsame : PosComboNoCommonSameDegreeRootCountAboveNonRootNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreeRootCountAboveNonRootNonnegStatement) :
    ChudnovskySeymourFourWayPackage fs := by
  rr_chudnovskySeymour_fourWay_rootCountAboveNonRoot using
    member_realrooted := hrr,
    member_pos_lc := hpos,
    same_degree := hsame,
    succ_degree := hsucc

example {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hsame : PosComboNoCommonSameDegreePairHasCommonInterleaverNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement) :
    ChudnovskySeymourFourWayPackage fs := by
  rr_chudnovskySeymour_fourWay_degreeSplit_nonnegShift using
    member_realrooted := hrr,
    member_pos_lc := hpos,
    same_degree := hsame,
    succ_degree := hsucc

example {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hsame : PosComboNoCommonSameDegreeSlotDataNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreeSlotDataNonnegStatement) :
    ChudnovskySeymourFourWayPackage fs := by
  rr_chudnovskySeymour_fourWay_slotData_nonnegShift using
    member_realrooted := hrr,
    member_pos_lc := hpos,
    same_degree := hsame,
    succ_degree := hsucc

example {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hsame : PosComboNoCommonSameDegreeOrientationAlternativeNonnegStatement)
    (haff : PosComboNoCommonAffineFamilyStatement) :
    ChudnovskySeymourFourWayPackage fs := by
  rr_chudnovskySeymour_fourWay_affineFamily_nonnegShift using
    member_realrooted := hrr,
    member_pos_lc := hpos,
    same_degree := hsame,
    affine_family := haff

example {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hboundary : PosComboNoCommonBoundaryRightPairOrientationStatement) :
    ChudnovskySeymourFourWayPackage fs := by
  rr_chudnovskySeymour_fourWay_boundaryRight_nonnegShift using
    member_realrooted := hrr,
    member_pos_lc := hpos,
    boundary_right := hboundary

example {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hnn : ∀ f ∈ fs, HasNonnegCoeffs f)
    (hsame : PosComboNoCommonSameDegreePairHasCommonInterleaverNonnegStatement)
    (haff : PosComboNoCommonAffineFamilyStatement) :
    ChudnovskySeymourFourWayPackage fs := by
  rr_chudnovskySeymour_fourWay_sameDegreePair_affineFamily_nonneg using
    member_realrooted := hrr,
    member_pos_lc := hpos,
    member_nonneg_coeffs := hnn,
    same_degree := hsame,
    affine_family := haff

example {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hnn : ∀ f ∈ fs, HasNonnegCoeffs f)
    (hall : PosComboNoCommonToAllComboBridgeStatement) :
    ChudnovskySeymourFourWayPackage fs := by
  rr_chudnovskySeymour_fourWay_allCombo_nonnegCoeffs using
    member_realrooted := hrr,
    member_pos_lc := hpos,
    member_nonneg_coeffs := hnn,
    all_combo := hall

example {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hnn : ∀ f ∈ fs, HasNonnegCoeffs f)
    (haff : PosComboNoCommonAffineFamilyStatement) :
    ChudnovskySeymourFourWayPackage fs := by
  rr_chudnovskySeymour_fourWay_affineFamily_nonnegCoeffs using
    member_realrooted := hrr,
    member_pos_lc := hpos,
    member_nonneg_coeffs := hnn,
    affine_family := haff

example {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hnn : ∀ f ∈ fs, HasNonnegCoeffs f)
    (hboundary : PosComboNoCommonBoundaryRightPairOrientationStatement) :
    ChudnovskySeymourFourWayPackage fs := by
  rr_chudnovskySeymour_fourWay_boundaryRight_nonnegCoeffs using
    member_realrooted := hrr,
    member_pos_lc := hpos,
    member_nonneg_coeffs := hnn,
    boundary_right := hboundary

example {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hbridge : PosComboPairHasCommonInterleaverStatement) :
    ChudnovskySeymourFourWayPackage fs := by
  rr_chudnovskySeymour_fourWay_posComboBridge using
    member_realrooted := hrr,
    member_pos_lc := hpos,
    pos_combo_bridge := hbridge

example {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (horient : PosComboNoCommonOrientationStatement)
    (hdeg : PosComboNatDegreeCloseStatement) :
    ChudnovskySeymourFourWayPackage fs := by
  rr_chudnovskySeymour_fourWay_noCommonOrientation_degreeClose using
    member_realrooted := hrr,
    member_pos_lc := hpos,
    orientation := horient,
    degree_close := hdeg

example {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hnn : ∀ f ∈ fs, HasNonnegCoeffs f)
    (horient : PosComboNoCommonOrientationStatement) :
    ChudnovskySeymourFourWayPackage fs := by
  rr_chudnovskySeymour_fourWay_noCommonOrientation_nonnegCoeffs using
    member_realrooted := hrr,
    member_pos_lc := hpos,
    member_nonneg_coeffs := hnn,
    orientation := horient

example {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hnn : ∀ f ∈ fs, HasNonnegCoeffs f)
    (hsame : PosComboNoCommonSameDegreePairHasCommonInterleaverNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement) :
    ChudnovskySeymourFourWayPackage fs := by
  rr_chudnovskySeymour_fourWay_pairDegreeSplit_nonnegCoeffs using
    member_realrooted := hrr,
    member_pos_lc := hpos,
    member_nonneg_coeffs := hnn,
    same_degree := hsame,
    succ_degree := hsucc

example {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hnn : ∀ f ∈ fs, HasNonnegCoeffs f)
    (hsame : PosComboNoCommonSameDegreeOrientationAlternativeNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement) :
    ChudnovskySeymourFourWayPackage fs := by
  rr_chudnovskySeymour_fourWay_degreeSplit_nonnegCoeffs using
    member_realrooted := hrr,
    member_pos_lc := hpos,
    member_nonneg_coeffs := hnn,
    same_degree := hsame,
    succ_degree := hsucc

example {fs : List ℝ[X]}
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hdeg : ∀ f ∈ fs, f.natDegree ≤ 1) :
    ChudnovskySeymourFourWayPackage fs := by
  rr_chudnovskySeymour_fourWay_degree_le_one using
    member_pos_lc := hpos,
    member_degree_le_one := hdeg

example {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hdeg : ∀ f ∈ fs, f.natDegree ≤ 2) :
    ChudnovskySeymourFourWayPackage fs := by
  rr_chudnovskySeymour_fourWay_degree_le_two using
    member_realrooted := hrr,
    member_pos_lc := hpos,
    member_degree_le_two := hdeg

example {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hsame : PosComboNoCommonSameDegreeRootCrossingNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreeRootCrossingNonnegStatement) :
    PairwiseCompatible fs ↔ HasCommonInterleaver fs := by
  rr_pairwiseCompatible_iff_commonInterleaver_rootCrossing using
    member_realrooted := hrr,
    member_pos_lc := hpos,
    same_degree := hsame,
    succ_degree := hsucc

example {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hsame : PosComboNoCommonSameDegreeRootCountNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreeRootCountNonnegStatement) :
    PairwiseCompatible fs ↔ HasCommonInterleaver fs := by
  rr_pairwiseCompatible_iff_commonInterleaver_rootCount using
    member_realrooted := hrr,
    member_pos_lc := hpos,
    same_degree := hsame,
    succ_degree := hsucc

example {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hsame : PosComboNoCommonSameDegreeRootCountAboveNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreeRootCountAboveNonnegStatement) :
    PairwiseCompatible fs ↔ HasCommonInterleaver fs := by
  rr_pairwiseCompatible_iff_commonInterleaver_rootCountAbove using
    member_realrooted := hrr,
    member_pos_lc := hpos,
    same_degree := hsame,
    succ_degree := hsucc

example {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hsame : PosComboNoCommonSameDegreeRootCountNonRootNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreeRootCountNonRootNonnegStatement) :
    PairwiseCompatible fs ↔ HasCommonInterleaver fs := by
  rr_pairwiseCompatible_iff_commonInterleaver_rootCountNonRoot using
    member_realrooted := hrr,
    member_pos_lc := hpos,
    same_degree := hsame,
    succ_degree := hsucc

example {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hsame : PosComboNoCommonSameDegreeRootCountAboveNonRootNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreeRootCountAboveNonRootNonnegStatement) :
    PairwiseCompatible fs ↔ HasCommonInterleaver fs := by
  rr_pairwiseCompatible_iff_commonInterleaver_rootCountAboveNonRoot using
    member_realrooted := hrr,
    member_pos_lc := hpos,
    same_degree := hsame,
    succ_degree := hsucc

example {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hsame : PosComboNoCommonSameDegreePairHasCommonInterleaverNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement) :
    PairwiseCompatible fs ↔ HasCommonInterleaver fs := by
  rr_pairwiseCompatible_iff_commonInterleaver_degreeSplit_nonnegShift using
    member_realrooted := hrr,
    member_pos_lc := hpos,
    same_degree := hsame,
    succ_degree := hsucc

example {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hsame : PosComboNoCommonSameDegreeSlotDataNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreeSlotDataNonnegStatement) :
    PairwiseCompatible fs ↔ HasCommonInterleaver fs := by
  rr_pairwiseCompatible_iff_commonInterleaver_slotData_nonnegShift using
    member_realrooted := hrr,
    member_pos_lc := hpos,
    same_degree := hsame,
    succ_degree := hsucc

example {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hsame : PosComboNoCommonSameDegreeOrientationAlternativeNonnegStatement)
    (haff : PosComboNoCommonAffineFamilyStatement) :
    PairwiseCompatible fs ↔ HasCommonInterleaver fs := by
  rr_pairwiseCompatible_iff_commonInterleaver_affineFamily_nonnegShift using
    member_realrooted := hrr,
    member_pos_lc := hpos,
    same_degree := hsame,
    affine_family := haff

example {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hboundary : PosComboNoCommonBoundaryRightPairOrientationStatement) :
    PairwiseCompatible fs ↔ HasCommonInterleaver fs := by
  rr_pairwiseCompatible_iff_commonInterleaver_boundaryRight_nonnegShift using
    member_realrooted := hrr,
    member_pos_lc := hpos,
    boundary_right := hboundary

example {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hnn : ∀ f ∈ fs, HasNonnegCoeffs f)
    (hsame : PosComboNoCommonSameDegreePairHasCommonInterleaverNonnegStatement)
    (haff : PosComboNoCommonAffineFamilyStatement) :
    PairwiseCompatible fs ↔ HasCommonInterleaver fs := by
  rr_pairwiseCompatible_iff_commonInterleaver_sameDegreePair_affineFamily_nonneg
    using
    member_realrooted := hrr,
    member_pos_lc := hpos,
    member_nonneg_coeffs := hnn,
    same_degree := hsame,
    affine_family := haff

example {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hnn : ∀ f ∈ fs, HasNonnegCoeffs f)
    (hall : PosComboNoCommonToAllComboBridgeStatement) :
    PairwiseCompatible fs ↔ HasCommonInterleaver fs := by
  rr_pairwiseCompatible_iff_commonInterleaver_allCombo_nonnegCoeffs using
    member_realrooted := hrr,
    member_pos_lc := hpos,
    member_nonneg_coeffs := hnn,
    all_combo := hall

example {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hnn : ∀ f ∈ fs, HasNonnegCoeffs f)
    (haff : PosComboNoCommonAffineFamilyStatement) :
    PairwiseCompatible fs ↔ HasCommonInterleaver fs := by
  rr_pairwiseCompatible_iff_commonInterleaver_affineFamily_nonnegCoeffs using
    member_realrooted := hrr,
    member_pos_lc := hpos,
    member_nonneg_coeffs := hnn,
    affine_family := haff

example {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hnn : ∀ f ∈ fs, HasNonnegCoeffs f)
    (hboundary : PosComboNoCommonBoundaryRightPairOrientationStatement) :
    PairwiseCompatible fs ↔ HasCommonInterleaver fs := by
  rr_pairwiseCompatible_iff_commonInterleaver_boundaryRight_nonnegCoeffs using
    member_realrooted := hrr,
    member_pos_lc := hpos,
    member_nonneg_coeffs := hnn,
    boundary_right := hboundary

example {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hbridge : PosComboPairHasCommonInterleaverStatement) :
    PairwiseCompatible fs ↔ HasCommonInterleaver fs := by
  rr_pairwiseCompatible_iff_commonInterleaver_posComboBridge using
    member_realrooted := hrr,
    member_pos_lc := hpos,
    pos_combo_bridge := hbridge

example {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (horient : PosComboNoCommonOrientationStatement)
    (hdeg : PosComboNatDegreeCloseStatement) :
    PairwiseCompatible fs ↔ HasCommonInterleaver fs := by
  rr_pairwiseCompatible_iff_commonInterleaver_noCommonOrientation_degreeClose
    using
    member_realrooted := hrr,
    member_pos_lc := hpos,
    orientation := horient,
    degree_close := hdeg

example {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hnn : ∀ f ∈ fs, HasNonnegCoeffs f)
    (horient : PosComboNoCommonOrientationStatement) :
    PairwiseCompatible fs ↔ HasCommonInterleaver fs := by
  rr_pairwiseCompatible_iff_commonInterleaver_noCommonOrientation_nonnegCoeffs
    using
    member_realrooted := hrr,
    member_pos_lc := hpos,
    member_nonneg_coeffs := hnn,
    orientation := horient

example {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hnn : ∀ f ∈ fs, HasNonnegCoeffs f)
    (hsame : PosComboNoCommonSameDegreePairHasCommonInterleaverNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement) :
    PairwiseCompatible fs ↔ HasCommonInterleaver fs := by
  rr_pairwiseCompatible_iff_commonInterleaver_pairDegreeSplit_nonnegCoeffs
    using
    member_realrooted := hrr,
    member_pos_lc := hpos,
    member_nonneg_coeffs := hnn,
    same_degree := hsame,
    succ_degree := hsucc

example {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hnn : ∀ f ∈ fs, HasNonnegCoeffs f)
    (hsame : PosComboNoCommonSameDegreeOrientationAlternativeNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement) :
    PairwiseCompatible fs ↔ HasCommonInterleaver fs := by
  rr_pairwiseCompatible_iff_commonInterleaver_degreeSplit_nonnegCoeffs using
    member_realrooted := hrr,
    member_pos_lc := hpos,
    member_nonneg_coeffs := hnn,
    same_degree := hsame,
    succ_degree := hsucc

example {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f) :
    PairwiseCompatible fs ↔ HasCommonLeftInterleaver fs := by
  rr_chudnovskySeymour_pairwiseCompatible_iff_commonLeftInterleaver using
    member_realrooted := hrr,
    member_pos_lc := hpos

example {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f) :
    PairwiseCompatible fs ↔ HasCommonInterleaver fs := by
  rr_chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver using
    member_realrooted := hrr,
    member_pos_lc := hpos

example {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f) :
    PairwiseCompatible fs ↔ FamilyCompatible fs := by
  rr_chudnovskySeymour_pairwiseCompatible_iff_familyCompatible using
    member_realrooted := hrr,
    member_pos_lc := hpos

example {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hsame : PosComboNoCommonSameDegreeRootCrossingNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreeRootCrossingNonnegStatement) :
    PairwiseCompatible fs ↔ FamilyCompatible fs := by
  rr_pairwiseCompatible_iff_familyCompatible_rootCrossing using
    member_realrooted := hrr,
    member_pos_lc := hpos,
    same_degree := hsame,
    succ_degree := hsucc

example {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hsame : PosComboNoCommonSameDegreeRootCountNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreeRootCountNonnegStatement) :
    PairwiseCompatible fs ↔ FamilyCompatible fs := by
  rr_pairwiseCompatible_iff_familyCompatible_rootCount using
    member_realrooted := hrr,
    member_pos_lc := hpos,
    same_degree := hsame,
    succ_degree := hsucc

example {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hsame : PosComboNoCommonSameDegreeRootCountAboveNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreeRootCountAboveNonnegStatement) :
    PairwiseCompatible fs ↔ FamilyCompatible fs := by
  rr_pairwiseCompatible_iff_familyCompatible_rootCountAbove using
    member_realrooted := hrr,
    member_pos_lc := hpos,
    same_degree := hsame,
    succ_degree := hsucc

example {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hsame : PosComboNoCommonSameDegreeRootCountNonRootNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreeRootCountNonRootNonnegStatement) :
    PairwiseCompatible fs ↔ FamilyCompatible fs := by
  rr_pairwiseCompatible_iff_familyCompatible_rootCountNonRoot using
    member_realrooted := hrr,
    member_pos_lc := hpos,
    same_degree := hsame,
    succ_degree := hsucc

example {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hsame : PosComboNoCommonSameDegreeRootCountAboveNonRootNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreeRootCountAboveNonRootNonnegStatement) :
    PairwiseCompatible fs ↔ FamilyCompatible fs := by
  rr_pairwiseCompatible_iff_familyCompatible_rootCountAboveNonRoot using
    member_realrooted := hrr,
    member_pos_lc := hpos,
    same_degree := hsame,
    succ_degree := hsucc

example {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hsame : PosComboNoCommonSameDegreePairHasCommonInterleaverNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement) :
    PairwiseCompatible fs ↔ FamilyCompatible fs := by
  rr_pairwiseCompatible_iff_familyCompatible_degreeSplit_nonnegShift using
    member_realrooted := hrr,
    member_pos_lc := hpos,
    same_degree := hsame,
    succ_degree := hsucc

example {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hsame : PosComboNoCommonSameDegreeSlotDataNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreeSlotDataNonnegStatement) :
    PairwiseCompatible fs ↔ FamilyCompatible fs := by
  rr_pairwiseCompatible_iff_familyCompatible_slotData_nonnegShift using
    member_realrooted := hrr,
    member_pos_lc := hpos,
    same_degree := hsame,
    succ_degree := hsucc

example {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hsame : PosComboNoCommonSameDegreeOrientationAlternativeNonnegStatement)
    (haff : PosComboNoCommonAffineFamilyStatement) :
    PairwiseCompatible fs ↔ FamilyCompatible fs := by
  rr_pairwiseCompatible_iff_familyCompatible_affineFamily_nonnegShift using
    member_realrooted := hrr,
    member_pos_lc := hpos,
    same_degree := hsame,
    affine_family := haff

example {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hboundary : PosComboNoCommonBoundaryRightPairOrientationStatement) :
    PairwiseCompatible fs ↔ FamilyCompatible fs := by
  rr_pairwiseCompatible_iff_familyCompatible_boundaryRight_nonnegShift using
    member_realrooted := hrr,
    member_pos_lc := hpos,
    boundary_right := hboundary

example {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hnn : ∀ f ∈ fs, HasNonnegCoeffs f)
    (hsame : PosComboNoCommonSameDegreePairHasCommonInterleaverNonnegStatement)
    (haff : PosComboNoCommonAffineFamilyStatement) :
    PairwiseCompatible fs ↔ FamilyCompatible fs := by
  rr_pairwiseCompatible_iff_familyCompatible_sameDegreePair_affineFamily_nonneg
    using
    member_realrooted := hrr,
    member_pos_lc := hpos,
    member_nonneg_coeffs := hnn,
    same_degree := hsame,
    affine_family := haff

example {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hnn : ∀ f ∈ fs, HasNonnegCoeffs f)
    (hall : PosComboNoCommonToAllComboBridgeStatement) :
    PairwiseCompatible fs ↔ FamilyCompatible fs := by
  rr_pairwiseCompatible_iff_familyCompatible_allCombo_nonnegCoeffs using
    member_realrooted := hrr,
    member_pos_lc := hpos,
    member_nonneg_coeffs := hnn,
    all_combo := hall

example {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hnn : ∀ f ∈ fs, HasNonnegCoeffs f)
    (haff : PosComboNoCommonAffineFamilyStatement) :
    PairwiseCompatible fs ↔ FamilyCompatible fs := by
  rr_pairwiseCompatible_iff_familyCompatible_affineFamily_nonnegCoeffs using
    member_realrooted := hrr,
    member_pos_lc := hpos,
    member_nonneg_coeffs := hnn,
    affine_family := haff

example {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hnn : ∀ f ∈ fs, HasNonnegCoeffs f)
    (hboundary : PosComboNoCommonBoundaryRightPairOrientationStatement) :
    PairwiseCompatible fs ↔ FamilyCompatible fs := by
  rr_pairwiseCompatible_iff_familyCompatible_boundaryRight_nonnegCoeffs using
    member_realrooted := hrr,
    member_pos_lc := hpos,
    member_nonneg_coeffs := hnn,
    boundary_right := hboundary

example {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hbridge : PosComboPairHasCommonInterleaverStatement) :
    PairwiseCompatible fs ↔ FamilyCompatible fs := by
  rr_pairwiseCompatible_iff_familyCompatible_posComboBridge using
    member_realrooted := hrr,
    member_pos_lc := hpos,
    pos_combo_bridge := hbridge

example {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (horient : PosComboNoCommonOrientationStatement)
    (hdeg : PosComboNatDegreeCloseStatement) :
    PairwiseCompatible fs ↔ FamilyCompatible fs := by
  rr_pairwiseCompatible_iff_familyCompatible_noCommonOrientation_degreeClose
    using
    member_realrooted := hrr,
    member_pos_lc := hpos,
    orientation := horient,
    degree_close := hdeg

example {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hnn : ∀ f ∈ fs, HasNonnegCoeffs f)
    (horient : PosComboNoCommonOrientationStatement) :
    PairwiseCompatible fs ↔ FamilyCompatible fs := by
  rr_pairwiseCompatible_iff_familyCompatible_noCommonOrientation_nonnegCoeffs
    using
    member_realrooted := hrr,
    member_pos_lc := hpos,
    member_nonneg_coeffs := hnn,
    orientation := horient

example {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hnn : ∀ f ∈ fs, HasNonnegCoeffs f)
    (hsame : PosComboNoCommonSameDegreePairHasCommonInterleaverNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement) :
    PairwiseCompatible fs ↔ FamilyCompatible fs := by
  rr_pairwiseCompatible_iff_familyCompatible_pairDegreeSplit_nonnegCoeffs
    using
    member_realrooted := hrr,
    member_pos_lc := hpos,
    member_nonneg_coeffs := hnn,
    same_degree := hsame,
    succ_degree := hsucc

example {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hnn : ∀ f ∈ fs, HasNonnegCoeffs f)
    (hsame : PosComboNoCommonSameDegreeOrientationAlternativeNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement) :
    PairwiseCompatible fs ↔ FamilyCompatible fs := by
  rr_pairwiseCompatible_iff_familyCompatible_degreeSplit_nonnegCoeffs using
    member_realrooted := hrr,
    member_pos_lc := hpos,
    member_nonneg_coeffs := hnn,
    same_degree := hsame,
    succ_degree := hsucc

example {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hf_split : f.Splits)
    (hg_split : g.Splits)
    (hfg : PosComboRealRooted f g)
    (hfdeg : f.natDegree ≤ 2)
    (hgdeg : g.natDegree ≤ 2) :
    ∃ h : ℝ[X], Prec f h ∧ Prec g h := by
  rr_posCombo_pair_common_interleaver_degree_le_two using
    left_pos_lc := hf_pos,
    right_pos_lc := hg_pos,
    left_splits := hf_split,
    right_splits := hg_split,
    pos_combo := hfg,
    left_degree_le_two := hfdeg,
    right_degree_le_two := hgdeg

example {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfg : Compatible f g)
    (hfdeg : f.natDegree ≤ 2)
    (hgdeg : g.natDegree ≤ 2) :
    ∃ h : ℝ[X], Prec f h ∧ Prec g h := by
  rr_compatible_pair_common_interleaver_degree_le_two using
    left_pos_lc := hf_pos,
    right_pos_lc := hg_pos,
    compatible := hfg,
    left_degree_le_two := hfdeg,
    right_degree_le_two := hgdeg

example {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfdeg : f.natDegree ≤ 1)
    (hgdeg : g.natDegree ≤ 1) :
    ∃ h : ℝ[X], Prec f h ∧ Prec g h := by
  rr_pair_common_interleaver_degree_le_one using
    left_pos_lc := hf_pos,
    right_pos_lc := hg_pos,
    left_degree_le_one := hfdeg,
    right_degree_le_one := hgdeg

example {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfdeg : f.natDegree ≤ 1)
    (hgdeg : g.natDegree ≤ 1) :
    ∃ h : ℝ[X], Prec h f ∧ Prec h g := by
  rr_pair_common_left_interleaver_degree_le_one using
    left_pos_lc := hf_pos,
    right_pos_lc := hg_pos,
    left_degree_le_one := hfdeg,
    right_degree_le_one := hgdeg

example {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfg : Compatible f g)
    (hfdeg : f.natDegree ≤ 1)
    (hgdeg : g.natDegree ≤ 1) :
    ∃ h : ℝ[X], Prec f h ∧ Prec g h := by
  rr_compatible_pair_common_interleaver_degree_le_one using
    left_pos_lc := hf_pos,
    right_pos_lc := hg_pos,
    compatible := hfg,
    left_degree_le_one := hfdeg,
    right_degree_le_one := hgdeg

example {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfg : Compatible f g)
    (hfdeg : f.natDegree ≤ 1)
    (hgdeg : g.natDegree ≤ 1) :
    ∃ h : ℝ[X], Prec h f ∧ Prec h g := by
  rr_compatible_pair_common_left_interleaver_degree_le_one using
    left_pos_lc := hf_pos,
    right_pos_lc := hg_pos,
    compatible := hfg,
    left_degree_le_one := hfdeg,
    right_degree_le_one := hgdeg

example {fs : List ℝ[X]}
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hdeg : ∀ f ∈ fs, f.natDegree ≤ 1) :
    PairwiseHasCommonInterleaver fs := by
  rr_pairwise_common_interleaver_degree_le_one using
    member_pos_lc := hpos,
    member_degree_le_one := hdeg

example {fs : List ℝ[X]}
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hdeg : ∀ f ∈ fs, f.natDegree ≤ 2)
    (hpair : PairwiseCompatible fs) :
    PairwiseHasCommonInterleaver fs := by
  rr_pairwise_common_interleaver_degree_le_two using
    member_pos_lc := hpos,
    member_degree_le_two := hdeg,
    pairwise_compatible := hpair

example {fs : List ℝ[X]}
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hdeg : ∀ f ∈ fs, f.natDegree ≤ 1) :
    PairwiseCompatible fs ↔ PairwiseHasCommonInterleaver fs := by
  rr_pairwiseCompatible_iff_pairwiseCommon_degree_le_one using
    member_pos_lc := hpos,
    member_degree_le_one := hdeg

example {fs : List ℝ[X]}
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hdeg : ∀ f ∈ fs, f.natDegree ≤ 2) :
    PairwiseCompatible fs ↔ PairwiseHasCommonInterleaver fs := by
  rr_pairwiseCompatible_iff_pairwiseCommon_degree_le_two using
    member_pos_lc := hpos,
    member_degree_le_two := hdeg

example {fs : List ℝ[X]}
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hdeg : ∀ f ∈ fs, f.natDegree ≤ 1) :
    PairwiseHasCommonInterleaver fs ↔ HasCommonInterleaver fs := by
  rr_pairwiseCommon_iff_commonInterleaver_degree_le_one using
    member_pos_lc := hpos,
    member_degree_le_one := hdeg

example {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hdeg : ∀ f ∈ fs, f.natDegree ≤ 2) :
    PairwiseHasCommonInterleaver fs ↔ HasCommonInterleaver fs := by
  rr_pairwiseCommon_iff_commonInterleaver_degree_le_two using
    member_realrooted := hrr,
    member_pos_lc := hpos,
    member_degree_le_two := hdeg

example {fs : List ℝ[X]}
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hdeg : ∀ f ∈ fs, f.natDegree ≤ 1) :
    HasCommonInterleaver fs ↔ FamilyCompatible fs := by
  rr_commonInterleaver_iff_familyCompatible_degree_le_one using
    member_pos_lc := hpos,
    member_degree_le_one := hdeg

example {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hdeg : ∀ f ∈ fs, f.natDegree ≤ 2) :
    HasCommonInterleaver fs ↔ FamilyCompatible fs := by
  rr_commonInterleaver_iff_familyCompatible_degree_le_two using
    member_realrooted := hrr,
    member_pos_lc := hpos,
    member_degree_le_two := hdeg

example {fs : List ℝ[X]}
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hdeg : ∀ f ∈ fs, f.natDegree ≤ 1) :
    PairwiseCompatible fs ↔ HasCommonInterleaver fs := by
  rr_pairwiseCompatible_iff_commonInterleaver_degree_le_one using
    member_pos_lc := hpos,
    member_degree_le_one := hdeg

example {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hdeg : ∀ f ∈ fs, f.natDegree ≤ 2) :
    PairwiseCompatible fs ↔ HasCommonInterleaver fs := by
  rr_pairwiseCompatible_iff_commonInterleaver_degree_le_two using
    member_realrooted := hrr,
    member_pos_lc := hpos,
    member_degree_le_two := hdeg

example {fs : List ℝ[X]}
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hdeg : ∀ f ∈ fs, f.natDegree ≤ 1) :
    PairwiseCompatible fs ↔ HasCommonLeftInterleaver fs := by
  rr_pairwiseCompatible_iff_commonLeft_degree_le_one using
    member_pos_lc := hpos,
    member_degree_le_one := hdeg

example {fs : List ℝ[X]}
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hdeg : ∀ f ∈ fs, f.natDegree ≤ 1) :
    PairwiseCompatible fs ↔ FamilyCompatible fs := by
  rr_pairwiseCompatible_iff_familyCompatible_degree_le_one using
    member_pos_lc := hpos,
    member_degree_le_one := hdeg

example {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hdeg : ∀ f ∈ fs, f.natDegree ≤ 2) :
    PairwiseCompatible fs ↔ FamilyCompatible fs := by
  rr_pairwiseCompatible_iff_familyCompatible_degree_le_two using
    member_realrooted := hrr,
    member_pos_lc := hpos,
    member_degree_le_two := hdeg

example {f g : ℝ[X]}
    (hbelow : CubicInteriorTwoBelowStatement)
    (habove : CubicInteriorTwoAboveStatement)
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g)
    (hdeg : g.natDegree = f.natDegree)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hfdeg : f.natDegree ≤ 3) :
    ∃ h : ℝ[X], Prec f h ∧ Prec g h := by
  rr_sameDegree_pair_common_interleaver_cubicInterior using
    below_certificate := hbelow,
    above_certificate := habove,
    left_pos_lc := hf_pos,
    right_pos_lc := hg_pos,
    left_nonneg_coeffs := hfnn,
    right_nonneg_coeffs := hgnn,
    pos_combo := hfg,
    same_degree := hdeg,
    no_common_roots := hno,
    left_degree_le_three := hfdeg

example {f g : ℝ[X]}
    (hbelow : CubicInteriorTwoBelowStatement)
    (habove : CubicInteriorTwoAboveStatement)
    (hsucc : PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement)
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g)
    (hdeg_lo : f.natDegree ≤ g.natDegree)
    (hdeg_hi : g.natDegree ≤ f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hgdeg : g.natDegree ≤ 3) :
    ∃ h : ℝ[X], Prec f h ∧ Prec g h := by
  rr_noCommon_pair_common_interleaver_degree_le_three using
    below_certificate := hbelow,
    above_certificate := habove,
    succ_degree_endpoint := hsucc,
    left_pos_lc := hf_pos,
    right_pos_lc := hg_pos,
    left_nonneg_coeffs := hfnn,
    right_nonneg_coeffs := hgnn,
    pos_combo := hfg,
    left_degree_le_right := hdeg_lo,
    right_degree_le_succ_left := hdeg_hi,
    no_common_roots := hno,
    right_degree_le_three := hgdeg

end Tactic
end RealRooted
