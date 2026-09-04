import RealRooted.CommonInterleaver.PairBridge.SuccDegree

/-!
# Pair bridge assembly: succ-degree slot data

Slot-data constructors and common-interleaver wrappers built from the
succ-degree root-count and root-crossing core.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- **Decomposition of milestone B2 into its two honest remaining pieces.**

The succ-degree slot-data statement follows from left-endpoint real-rootedness
of `f` (`PosComboSuccDegreeLeftSplitsNonnegStatement`) together with the
descending-root crossing inequalities
(`PosComboNoCommonSuccDegreeRootCrossingNonnegStatement`); the combinatorial
step is discharged by `rootSlotInterval_inter_nonempty_of_crossing`. Via
`posComboNoCommonSuccDegreeSlotData_iff_pairHasCommonInterleaver` this reduces
the corrected common-right-interleaver target for milestone B2 (#42) to these
two analytic statements. -/
theorem posComboNoCommonSuccDegreeSlotData_of_leftSplits_and_rootCrossing
    (hsplit : PosComboSuccDegreeLeftSplitsNonnegStatement)
    (hcross : PosComboNoCommonSuccDegreeRootCrossingNonnegStatement) :
    PosComboNoCommonSuccDegreeSlotDataNonnegStatement := by
  intro f g hf_pos hg_pos hfnn hgnn hfg hsucc hno
  have hf_split : f.Splits := hsplit hf_pos hg_pos hfnn hgnn hfg hsucc
  have hg_split : g.Splits :=
    (hfg.isRealRooted_right_of_succDegree hf_pos hg_pos hsucc).2
  refine ⟨⟨HasPosLeadingCoeff.ne_zero hf_pos, hf_split⟩, ?_⟩
  obtain ⟨hc1, hc2⟩ := hcross hf_pos hg_pos hfnn hgnn hfg hsucc hno hf_split
  have hlenf : (rootSeqDesc f).length = f.natDegree := rootSeqDesc_length hf_split
  have hleng : (rootSeqDesc g).length = g.natDegree := rootSeqDesc_length hg_split
  intro j _ hjf hjg
  exact
    rootSlotInterval_inter_nonempty_of_crossing (rootSeqDesc f) (rootSeqDesc g)
      rootSeqDesc_pairwise rootSeqDesc_pairwise
      (by rw [hleng, hlenf, hsucc])
      (fun k hk1 hk2 => hc1 k hk1 (by rw [hlenf] at hk2; exact hk2))
      (fun k hk1 hk2 => hc2 k hk1 (by rw [hlenf] at hk2; exact hk2))
      j hjf hjg

/-- The corrected succ-degree pair-interleaver endpoint follows directly from
left-endpoint real-rootedness and the succ-degree descending-root crossing
inequalities. -/
theorem succDegreePairHasCommonInterleaver_nonneg_of_leftSplits_and_rootCrossing
    (hsplit : PosComboSuccDegreeLeftSplitsNonnegStatement)
    (hcross : PosComboNoCommonSuccDegreeRootCrossingNonnegStatement) :
    PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement :=
  succDegreePairHasCommonInterleaver_nonneg_of_slotData
    (posComboNoCommonSuccDegreeSlotData_of_leftSplits_and_rootCrossing hsplit hcross)

/-- Succ-degree slot data from the unconditional root-continuity left endpoint
and the descending-root crossing inequalities. -/
theorem posComboNoCommonSuccDegreeSlotData_of_rootCrossing
    (hcross : PosComboNoCommonSuccDegreeRootCrossingNonnegStatement) :
    PosComboNoCommonSuccDegreeSlotDataNonnegStatement :=
  posComboNoCommonSuccDegreeSlotData_of_leftSplits_and_rootCrossing
    PosComboSuccDegreeLeftSplitsNonnegStatement_of_rootContinuity hcross

/-- The corrected succ-degree pair-interleaver endpoint follows from the
succ-degree descending-root crossing inequalities alone; root continuity
supplies the left endpoint. -/
theorem succDegreePairHasCommonInterleaver_nonneg_of_rootCrossing
    (hcross : PosComboNoCommonSuccDegreeRootCrossingNonnegStatement) :
    PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement :=
  succDegreePairHasCommonInterleaver_nonneg_of_slotData
    (posComboNoCommonSuccDegreeSlotData_of_rootCrossing hcross)

/-- Succ-degree slot data from the lower-threshold root-count formulation. -/
theorem posComboNoCommonSuccDegreeSlotData_of_rootCount
    (hcount : PosComboNoCommonSuccDegreeRootCountNonnegStatement) :
    PosComboNoCommonSuccDegreeSlotDataNonnegStatement :=
  posComboNoCommonSuccDegreeSlotData_of_rootCrossing
    (posComboNoCommonSuccDegreeRootCrossing_of_rootCount hcount)

/-- The corrected succ-degree pair-interleaver endpoint follows directly from
the lower-threshold root-count formulation. -/
theorem succDegreePairHasCommonInterleaver_nonneg_of_rootCount
    (hcount : PosComboNoCommonSuccDegreeRootCountNonnegStatement) :
    PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement :=
  succDegreePairHasCommonInterleaver_nonneg_of_rootCrossing
    (posComboNoCommonSuccDegreeRootCrossing_of_rootCount hcount)

/-- Succ-degree slot data from the upper-threshold root-count formulation. -/
theorem posComboNoCommonSuccDegreeSlotData_of_rootCountAbove
    (hcount : PosComboNoCommonSuccDegreeRootCountAboveNonnegStatement) :
    PosComboNoCommonSuccDegreeSlotDataNonnegStatement :=
  posComboNoCommonSuccDegreeSlotData_of_rootCrossing
    (posComboNoCommonSuccDegreeRootCrossing_of_rootCountAbove hcount)

/-- The corrected succ-degree pair-interleaver endpoint follows directly from
the upper-threshold root-count formulation. -/
theorem succDegreePairHasCommonInterleaver_nonneg_of_rootCountAbove
    (hcount : PosComboNoCommonSuccDegreeRootCountAboveNonnegStatement) :
    PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement :=
  succDegreePairHasCommonInterleaver_nonneg_of_rootCrossing
    (posComboNoCommonSuccDegreeRootCrossing_of_rootCountAbove hcount)

/-- Succ-degree slot data from the common-non-root upper-threshold root-count
formulation. -/
theorem posComboNoCommonSuccDegreeSlotData_of_nonRoot
    (hcount : PosComboNoCommonSuccDegreeRootCountAboveNonRootNonnegStatement) :
    PosComboNoCommonSuccDegreeSlotDataNonnegStatement :=
  posComboNoCommonSuccDegreeSlotData_of_rootCountAbove
    (posComboNoCommonSuccDegreeRootCountAbove_of_nonRoot hcount)

/-- Succ-degree slot data from the common-non-root upper-threshold root-count
formulation, with an explicit name for the `rootCountAboveNonRoot` leaf. -/
theorem posComboNoCommonSuccDegreeSlotData_of_rootCountAboveNonRoot
    (hcount : PosComboNoCommonSuccDegreeRootCountAboveNonRootNonnegStatement) :
    PosComboNoCommonSuccDegreeSlotDataNonnegStatement :=
  posComboNoCommonSuccDegreeSlotData_of_nonRoot hcount

/-- The repaired succ-degree pair-interleaver endpoint follows from the
common-non-root upper-threshold root-count formulation. -/
theorem succDegreePairHasCommonInterleaver_nonneg_of_nonRoot
    (hcount : PosComboNoCommonSuccDegreeRootCountAboveNonRootNonnegStatement) :
    PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement :=
  succDegreePairHasCommonInterleaver_nonneg_of_rootCountAbove
    (posComboNoCommonSuccDegreeRootCountAbove_of_nonRoot hcount)

/-- The repaired succ-degree pair-interleaver endpoint follows from the
common-non-root upper-threshold root-count formulation, with an explicit name
for the `rootCountAboveNonRoot` leaf. -/
theorem succDegreePairHasCommonInterleaver_nonneg_of_rootCountAboveNonRoot
    (hcount : PosComboNoCommonSuccDegreeRootCountAboveNonRootNonnegStatement) :
    PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement :=
  succDegreePairHasCommonInterleaver_nonneg_of_nonRoot hcount

/-- Closed-segment endpoint count equality supplies the repaired succ-degree
#42 pair-interleaver endpoint. -/
theorem succDegreePairHasCommonInterleaver_nonneg_of_closedSegmentCountEq
    (hcount : CompatibleSuccDegreeClosedSegmentCountEqStatement) :
    PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement :=
  succDegreePairHasCommonInterleaver_nonneg_of_rootCountAboveNonRoot
    (posComboNoCommonSuccDegreeRootCountAboveNonRoot_of_closedSegmentCountEq hcount)

/-- Closed-segment no-gap-two supplies the repaired succ-degree #42
pair-interleaver endpoint. -/
theorem succDegreePairHasCommonInterleaver_nonneg_of_closedSegmentNoGapTwo
    (hclosed : CompatibleSuccDegreeClosedSegmentNoGapTwoStatement) :
    PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement :=
  succDegreePairHasCommonInterleaver_nonneg_of_rootCountAboveNonRoot
    (posComboNoCommonSuccDegreeRootCountAboveNonRoot_of_closedSegmentNoGapTwo hclosed)

/-- Right-pencil no-gap-two supplies the repaired succ-degree #42
pair-interleaver endpoint. -/
theorem succDegreePairHasCommonInterleaver_nonneg_of_rightFamilyNoGapTwo
    (hright : CompatibleSuccDegreeRightFamilyNoGapTwoStatement) :
    PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement :=
  succDegreePairHasCommonInterleaver_nonneg_of_rootCountAboveNonRoot
    (posComboNoCommonSuccDegreeRootCountAboveNonRoot_of_rightFamilyNoGapTwo hright)

/-- Endpoint-sign no-gap-two supplies the repaired succ-degree #42
pair-interleaver endpoint. -/
theorem succDegreePairHasCommonInterleaver_nonneg_of_endpointSignNoGapTwo
    (hsign : CompatibleSuccDegreeEndpointSignNoGapTwoStatement) :
    PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement :=
  succDegreePairHasCommonInterleaver_nonneg_of_rootCountAboveNonRoot
    (posComboNoCommonSuccDegreeRootCountAboveNonRoot_of_endpointSignNoGapTwo hsign)

/-- Lower endpoint-sign no-gap supplies the repaired succ-degree #42
pair-interleaver endpoint. -/
theorem succDegreePairHasCommonInterleaver_nonneg_of_endpointSignLower
    (hlower : CompatibleSuccDegreeEndpointSignLowerNoGapStatement) :
    PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement :=
  succDegreePairHasCommonInterleaver_nonneg_of_rootCountAboveNonRoot
    (posComboNoCommonSuccDegreeRootCountAboveNonRoot_of_endpointSignLower hlower)

/-- Exact lower-count endpoint comparison supplies the repaired succ-degree
#42 pair-interleaver endpoint. -/
theorem succDegreePairHasCommonInterleaver_nonneg_of_lowerCountEq
    (hcount : CompatibleSuccDegreeEndpointSignLowerCountEqStatement) :
    PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement :=
  succDegreePairHasCommonInterleaver_nonneg_of_rootCountAboveNonRoot
    (posComboNoCommonSuccDegreeRootCountAboveNonRoot_of_lowerCountEq hcount)

/-- Succ-degree slot data from the lower common-non-root root-count
formulation. -/
theorem posComboNoCommonSuccDegreeSlotData_of_rootCountNonRoot
    (hcount : PosComboNoCommonSuccDegreeRootCountNonRootNonnegStatement) :
    PosComboNoCommonSuccDegreeSlotDataNonnegStatement :=
  posComboNoCommonSuccDegreeSlotData_of_rootCount
    (posComboNoCommonSuccDegreeRootCount_of_rootCountNonRoot hcount)

/-- The repaired succ-degree pair-interleaver endpoint follows from the lower
common-non-root root-count formulation. -/
theorem succDegreePairHasCommonInterleaver_nonneg_of_rootCountNonRoot
    (hcount : PosComboNoCommonSuccDegreeRootCountNonRootNonnegStatement) :
    PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement :=
  succDegreePairHasCommonInterleaver_nonneg_of_rootCount
    (posComboNoCommonSuccDegreeRootCount_of_rootCountNonRoot hcount)

/-- Succ-degree slot data from the two lower-threshold constant-term
root-count branches. -/
theorem posComboNoCommonSuccDegreeSlotData_of_residual_and_lead
    (hlead : PosComboNoCommonSuccDegreeRootCountLeadNonnegStatement)
    (hres : PosComboNoCommonSuccDegreeRootCountResidualNonnegStatement) :
    PosComboNoCommonSuccDegreeSlotDataNonnegStatement :=
  posComboNoCommonSuccDegreeSlotData_of_rootCount
    (posComboNoCommonSuccDegreeRootCount_of_residual_and_lead hlead hres)

/-- The repaired succ-degree pair-interleaver endpoint follows from the two
lower-threshold constant-term root-count branches. -/
theorem succDegreePairHasCommonInterleaver_nonneg_of_residual_and_lead
    (hlead : PosComboNoCommonSuccDegreeRootCountLeadNonnegStatement)
    (hres : PosComboNoCommonSuccDegreeRootCountResidualNonnegStatement) :
    PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement :=
  succDegreePairHasCommonInterleaver_nonneg_of_rootCount
    (posComboNoCommonSuccDegreeRootCount_of_residual_and_lead hlead hres)

/-- The repaired succ-degree pair-interleaver endpoint follows from the
residual branch, the both-nonzero lead branch, and the right-zero `divX`
orientation target. -/
theorem succDegreePairHasCommonInterleaver_nonneg_of_residual_bothNonzero_divX_prec
    (hboth : PosComboNoCommonSuccDegreeRootCountLeadBothNonzeroNonnegStatement)
    (hdivX : PosComboNoCommonSuccDegreeRootCountLeadRightZeroDivXPrecStatement)
    (hres : PosComboNoCommonSuccDegreeRootCountResidualNonnegStatement) :
    PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement :=
  succDegreePairHasCommonInterleaver_nonneg_of_rootCount
    (posComboNoCommonSuccDegreeRootCount_of_residual_bothNonzero_divX_prec
      hboth hdivX hres)

/-- The repaired succ-degree pair-interleaver endpoint follows from the
residual orientation target, the both-nonzero lead branch, and the right-zero
`divX` orientation target. -/
theorem
    succDegreePairHasCommonInterleaver_nonneg_of_residualPrec_bothNonzero_divX_prec
    (hresPrec : PosComboNoCommonSuccDegreeRootCountResidualPrecStatement)
    (hboth : PosComboNoCommonSuccDegreeRootCountLeadBothNonzeroNonnegStatement)
    (hdivX : PosComboNoCommonSuccDegreeRootCountLeadRightZeroDivXPrecStatement) :
    PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement :=
  succDegreePairHasCommonInterleaver_nonneg_of_rootCount
    (posComboNoCommonSuccDegreeRootCount_of_residualPrec_bothNonzero_divX_prec
      hresPrec hboth hdivX)

/-- Succ-degree slot data from the PF/ASW left-endpoint route and the
descending-root crossing inequalities. -/
theorem posComboNoCommonSuccDegreeSlotData_of_forward_asw_and_rootCrossing
    (hASW : aissenSchoenbergWhitneyForwardOrZeroStatement)
    (hcross : PosComboNoCommonSuccDegreeRootCrossingNonnegStatement) :
    PosComboNoCommonSuccDegreeSlotDataNonnegStatement :=
  posComboNoCommonSuccDegreeSlotData_of_leftSplits_and_rootCrossing
    (PosComboSuccDegreeLeftSplitsNonnegStatement_of_forward_asw hASW) hcross

/-- Succ-degree slot data from the proved ASW left endpoint and the
descending-root crossing inequalities. -/
theorem posComboNoCommonSuccDegreeSlotData_of_asw_and_rootCrossing
    (hcross : PosComboNoCommonSuccDegreeRootCrossingNonnegStatement) :
    PosComboNoCommonSuccDegreeSlotDataNonnegStatement :=
  posComboNoCommonSuccDegreeSlotData_of_leftSplits_and_rootCrossing
    PosComboSuccDegreeLeftSplitsNonnegStatement_of_asw hcross

/-- Succ-degree slot data from the splitting-only ASW target and the
root-crossing target. -/
theorem posComboNoCommonSuccDegreeSlotData_of_forward_asw_splits_and_rootCrossing
    (hASW : aissenSchoenbergWhitneyForwardSplitsStatement)
    (hcross : PosComboNoCommonSuccDegreeRootCrossingNonnegStatement) :
    PosComboNoCommonSuccDegreeSlotDataNonnegStatement :=
  posComboNoCommonSuccDegreeSlotData_of_forward_asw_and_rootCrossing
    (aissenSchoenbergWhitneyForwardOrZero_of_splits hASW) hcross

/-- Succ-degree pair interleavers from the PF/ASW left-endpoint route and the
descending-root crossing inequalities. -/
theorem
    succDegreePairHasCommonInterleaver_nonneg_of_forward_asw_and_rootCrossing
    (hASW : aissenSchoenbergWhitneyForwardOrZeroStatement)
    (hcross : PosComboNoCommonSuccDegreeRootCrossingNonnegStatement) :
    PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement :=
  succDegreePairHasCommonInterleaver_nonneg_of_leftSplits_and_rootCrossing
    (PosComboSuccDegreeLeftSplitsNonnegStatement_of_forward_asw hASW) hcross

/-- Succ-degree pair interleavers from the proved ASW left endpoint and the
descending-root crossing inequalities. -/
theorem succDegreePairHasCommonInterleaver_nonneg_of_asw_and_rootCrossing
    (hcross : PosComboNoCommonSuccDegreeRootCrossingNonnegStatement) :
    PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement :=
  succDegreePairHasCommonInterleaver_nonneg_of_leftSplits_and_rootCrossing
    PosComboSuccDegreeLeftSplitsNonnegStatement_of_asw hcross

/-- Succ-degree pair interleavers from the splitting-only ASW target and the
root-crossing target. -/
theorem
    succDegreePairHasCommonInterleaver_nonneg_of_forward_asw_splits_and_rootCrossing
    (hASW : aissenSchoenbergWhitneyForwardSplitsStatement)
    (hcross : PosComboNoCommonSuccDegreeRootCrossingNonnegStatement) :
    PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement :=
  succDegreePairHasCommonInterleaver_nonneg_of_forward_asw_and_rootCrossing
    (aissenSchoenbergWhitneyForwardOrZero_of_splits hASW) hcross

/-- Succ-degree slot data from left-endpoint real-rootedness and the fixed
orientation.  The orientation supplies the root-crossing inequalities. -/
theorem posComboNoCommonSuccDegreeSlotData_of_leftSplits_and_orientation
    (hsplit : PosComboSuccDegreeLeftSplitsNonnegStatement)
    (horient : PosComboNoCommonSuccDegreeOrientationNonnegStatement) :
    PosComboNoCommonSuccDegreeSlotDataNonnegStatement :=
  posComboNoCommonSuccDegreeSlotData_of_leftSplits_and_rootCrossing hsplit
    (posComboNoCommonSuccDegreeRootCrossing_of_orientation horient)

/-- The repaired succ-degree pair-interleaver endpoint follows from
left-endpoint real-rootedness and the fixed orientation. -/
theorem succDegreePairHasCommonInterleaver_nonneg_of_leftSplits_and_orientation
    (hsplit : PosComboSuccDegreeLeftSplitsNonnegStatement)
    (horient : PosComboNoCommonSuccDegreeOrientationNonnegStatement) :
    PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement :=
  succDegreePairHasCommonInterleaver_nonneg_of_leftSplits_and_rootCrossing hsplit
    (posComboNoCommonSuccDegreeRootCrossing_of_orientation horient)

/-- Succ-degree slot data from the PF/ASW left-endpoint route and the fixed
orientation. -/
theorem posComboNoCommonSuccDegreeSlotData_of_forward_asw_and_orientation
    (hASW : aissenSchoenbergWhitneyForwardOrZeroStatement)
    (horient : PosComboNoCommonSuccDegreeOrientationNonnegStatement) :
    PosComboNoCommonSuccDegreeSlotDataNonnegStatement :=
  posComboNoCommonSuccDegreeSlotData_of_forward_asw_and_rootCrossing hASW
    (posComboNoCommonSuccDegreeRootCrossing_of_orientation horient)

/-- Succ-degree slot data from the splitting-only ASW target and the fixed
succ-degree orientation. -/
theorem posComboNoCommonSuccDegreeSlotData_of_forward_asw_splits_and_orientation
    (hASW : aissenSchoenbergWhitneyForwardSplitsStatement)
    (horient : PosComboNoCommonSuccDegreeOrientationNonnegStatement) :
    PosComboNoCommonSuccDegreeSlotDataNonnegStatement :=
  posComboNoCommonSuccDegreeSlotData_of_forward_asw_and_orientation
    (aissenSchoenbergWhitneyForwardOrZero_of_splits hASW) horient

/-- Succ-degree pair interleavers from the PF/ASW left-endpoint route and the
fixed orientation. -/
theorem succDegreePairHasCommonInterleaver_nonneg_of_forward_asw_and_orientation
    (hASW : aissenSchoenbergWhitneyForwardOrZeroStatement)
    (horient : PosComboNoCommonSuccDegreeOrientationNonnegStatement) :
    PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement :=
  succDegreePairHasCommonInterleaver_nonneg_of_forward_asw_and_rootCrossing hASW
    (posComboNoCommonSuccDegreeRootCrossing_of_orientation horient)

/-- Succ-degree pair interleavers from the splitting-only ASW target and the
fixed orientation. -/
theorem succDegreePairHasCommonInterleaver_nonneg_of_forward_asw_splits_and_orientation
    (hASW : aissenSchoenbergWhitneyForwardSplitsStatement)
    (horient : PosComboNoCommonSuccDegreeOrientationNonnegStatement) :
    PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement :=
  succDegreePairHasCommonInterleaver_nonneg_of_forward_asw_and_orientation
    (aissenSchoenbergWhitneyForwardOrZero_of_splits hASW) horient

end RealRooted
