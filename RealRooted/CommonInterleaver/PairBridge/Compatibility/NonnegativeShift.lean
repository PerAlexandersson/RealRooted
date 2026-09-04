import RealRooted.CommonInterleaver.PairBridge.Compatibility

/-!
# Pair bridge assembly: nonnegative shifts

Translation to nonnegative coefficients and the resulting positive-leading
common-interleaver endpoint wrappers.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- A common right interleaver is invariant under translating both inputs. -/
theorem pairHasCommonInterleaver_comp_X_add_C_iff
    {f g : ℝ[X]} (r : ℝ) :
    (∃ h : ℝ[X],
      Prec (f.comp (X + C r)) h ∧
        Prec (g.comp (X + C r)) h) ↔
      ∃ h : ℝ[X], Prec f h ∧ Prec g h := by
  constructor
  · rintro ⟨h, hfh, hgh⟩
    let h' : ℝ[X] := h.comp (X - C r)
    refine ⟨h', ?_, ?_⟩
    · apply (prec_comp_X_add_C_iff (f := f) (g := h') r).1
      simpa [h', Polynomial.comp_assoc, sub_eq_add_neg, add_assoc, add_comm]
        using hfh
    · apply (prec_comp_X_add_C_iff (f := g) (g := h') r).1
      simpa [h', Polynomial.comp_assoc, sub_eq_add_neg, add_assoc, add_comm]
        using hgh
  · rintro ⟨h, hfh, hgh⟩
    exact ⟨h.comp (X + C r), prec_comp_X_add_C hfh r, prec_comp_X_add_C hgh r⟩

private theorem posComboPairHasCommonInterleaver_via_nonnegShift
    {f g : ℝ[X]}
    (_hf_rr_ne : f ≠ 0) (hf_rr_splits : f.Splits)
    (_hg_rr_ne : g ≠ 0) (hg_rr_splits : g.Splits)
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfg : PosComboRealRooted f g)
    (hNonneg :
      ∀ {F G : ℝ[X]},
        HasPosLeadingCoeff F →
        HasPosLeadingCoeff G →
        HasNonnegCoeffs F →
        HasNonnegCoeffs G →
        PosComboRealRooted F G →
        ∃ h : ℝ[X], Prec F h ∧ Prec G h) :
    ∃ h : ℝ[X], Prec f h ∧ Prec g h := by
  obtain ⟨rf, hrf⟩ := exists_root_upper_bound f
  obtain ⟨rg, hrg⟩ := exists_root_upper_bound g
  let r : ℝ := max rf rg
  let f' : ℝ[X] := f.comp (X + C r)
  let g' : ℝ[X] := g.comp (X + C r)
  have hf'_pos : HasPosLeadingCoeff f' := by simpa [f'] using hf_pos.comp_X_add_C r
  have hg'_pos : HasPosLeadingCoeff g' := by simpa [g'] using hg_pos.comp_X_add_C r
  have hfnn : HasNonnegCoeffs f' := by
    refine hasNonnegCoeffs_comp_X_add_C_of_roots_le hf_pos hf_rr_splits ?_
    grind
  have hgnn : HasNonnegCoeffs g' := by
    refine hasNonnegCoeffs_comp_X_add_C_of_roots_le hg_pos hg_rr_splits ?_
    grind
  have hfg' : PosComboRealRooted f' g' := by
    intro α β hα hβ
    simpa [f', g'] using hfg.comp_X_add_C r hα hβ
  apply (pairHasCommonInterleaver_comp_X_add_C_iff (f := f) (g := g) r).1
  simpa [f', g'] using hNonneg hf'_pos hg'_pos hfnn hgnn hfg'

/-- Degree-bounded common-interleaver endpoint for positive-leading split
positive-combination pairs.  Translating both polynomials far enough makes the
shifted coefficients nonnegative without changing their degrees, so the
nonnegative unordered degree-bounded reduction applies to the shifted pair; the
resulting common right interleaver is translated back. -/
theorem posComboPairHasCommonInterleaver_of_natDegree_le_reduction_unordered_via_nonnegShift
    {N : ℕ}
    (hterminal :
      ∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        f.natDegree ≤ g.natDegree →
        g.natDegree ≤ f.natDegree + 1 →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        g.natDegree ≤ N →
        ∃ h : ℝ[X], Prec f h ∧ Prec g h)
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hf_splits : f.Splits)
    (hg_splits : g.Splits)
    (hfg : PosComboRealRooted f g)
    (hfdeg : f.natDegree ≤ N)
    (hgdeg : g.natDegree ≤ N) :
    ∃ h : ℝ[X], Prec f h ∧ Prec g h := by
  obtain ⟨rf, hrf⟩ := exists_root_upper_bound f
  obtain ⟨rg, hrg⟩ := exists_root_upper_bound g
  let r : ℝ := max rf rg
  let f' : ℝ[X] := f.comp (X + C r)
  let g' : ℝ[X] := g.comp (X + C r)
  have hf'_pos : HasPosLeadingCoeff f' := by simpa [f'] using hf_pos.comp_X_add_C r
  have hg'_pos : HasPosLeadingCoeff g' := by simpa [g'] using hg_pos.comp_X_add_C r
  have hfnn : HasNonnegCoeffs f' := by
    refine hasNonnegCoeffs_comp_X_add_C_of_roots_le hf_pos hf_splits ?_
    grind
  have hgnn : HasNonnegCoeffs g' := by
    refine hasNonnegCoeffs_comp_X_add_C_of_roots_le hg_pos hg_splits ?_
    grind
  have hfg' : PosComboRealRooted f' g' := by
    intro α β hα hβ
    simpa [f', g'] using hfg.comp_X_add_C r hα hβ
  have hfdeg' : f'.natDegree ≤ N := by
    have hdeg_eq : f'.natDegree = f.natDegree := by simp [f', Polynomial.natDegree_comp]
    lia
  have hgdeg' : g'.natDegree ≤ N := by
    have hdeg_eq : g'.natDegree = g.natDegree := by simp [g', Polynomial.natDegree_comp]
    lia
  apply (pairHasCommonInterleaver_comp_X_add_C_iff (f := f) (g := g) r).1
  simpa [f', g'] using
    posComboPairHasCommonInterleaver_of_natDegree_le_reduction_unordered
      (N := N) hterminal hf'_pos hg'_pos hfnn hgnn hfg' hfdeg' hgdeg'

/-- Positive-combination degree-`≤ 2` pair endpoint.  Translate both
polynomials far enough to make the shifted roots nonpositive, apply the
nonnegative-coefficient degree-`≤ 2` endpoint, and translate the common right
interleaver back. -/
theorem posComboPairHasCommonInterleaver_of_natDegree_le_two
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hf_splits : f.Splits)
    (hg_splits : g.Splits)
    (hfg : PosComboRealRooted f g)
    (hfdeg : f.natDegree ≤ 2)
    (hgdeg : g.natDegree ≤ 2) :
    ∃ h : ℝ[X], Prec f h ∧ Prec g h :=
  posComboPairHasCommonInterleaver_of_natDegree_le_reduction_unordered_via_nonnegShift
    (N := 2)
    (fun {_f _g} hf_pos hg_pos hfnn hgnn hfg hdeg_lo hdeg_hi hno hgdeg =>
      posComboNoCommonPairHasCommonInterleaver_of_natDegree_le_two
        hf_pos hg_pos hfnn hgnn hfg hdeg_lo hdeg_hi hno hgdeg)
    hf_pos hg_pos hf_splits hg_splits hfg hfdeg hgdeg

/-- Compatibility-level degree-`≤ 2` two-polynomial Chudnovsky--Seymour
endpoint. -/
theorem compatiblePairHasCommonInterleaver_of_natDegree_le_two
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfg : Compatible f g)
    (hfdeg : f.natDegree ≤ 2)
    (hgdeg : g.natDegree ≤ 2) :
    ∃ h : ℝ[X], Prec f h ∧ Prec g h :=
  posComboPairHasCommonInterleaver_of_natDegree_le_two hf_pos hg_pos
    (hfg.isRealRooted_left hf_pos).2
    (hfg.isRealRooted_right hg_pos).2
    (hfg.toPosComboRealRooted hf_pos hg_pos) hfdeg hgdeg

/-- Translation reduces the full positive-leading compatibility bridge to the
repaired nonnegative-coefficient degree-split package.  This is the shifted
version whose same-degree input already has the common-right-interleaver
conclusion, rather than the stronger orientation alternative. -/
theorem posComboPairHasCommonInterleaver_of_pairDegreeSplit_via_nonnegShift
    (hsame : PosComboNoCommonSameDegreePairHasCommonInterleaverNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement)
    {f g : ℝ[X]}
    (_hf_rr_ne : f ≠ 0) (hf_rr_splits : f.Splits)
    (_hg_rr_ne : g ≠ 0) (hg_rr_splits : g.Splits)
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfg : PosComboRealRooted f g) :
    ∃ h : ℝ[X], Prec f h ∧ Prec g h :=
  posComboPairHasCommonInterleaver_via_nonnegShift
    _hf_rr_ne hf_rr_splits _hg_rr_ne hg_rr_splits hf_pos hg_pos hfg
    (fun {F G} hF_pos hG_pos hFnn hGnn hFG =>
      posComboPairHasCommonInterleaver_of_pairDegreeSplit_and_nonnegCoeffs
        hsame hsucc (f := F) (g := G) hF_pos hG_pos hFnn hGnn hFG)

/-- Translation reduces the full positive-leading compatibility bridge to the
nonnegative-coefficient degree-split package: shift both polynomials far enough
to the right so all roots become nonpositive, apply the nonnegative theorem,
then translate the common interleaver back. -/
theorem posComboPairHasCommonInterleaver_of_degreeSplit_via_nonnegShift
    (hsame : PosComboNoCommonSameDegreeOrientationAlternativeNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement)
    {f g : ℝ[X]}
    (_hf_rr_ne : f ≠ 0) (hf_rr_splits : f.Splits)
    (_hg_rr_ne : g ≠ 0) (hg_rr_splits : g.Splits)
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfg : PosComboRealRooted f g) :
    ∃ h : ℝ[X], Prec f h ∧ Prec g h :=
  posComboPairHasCommonInterleaver_of_pairDegreeSplit_via_nonnegShift
    (posComboNoCommonSameDegreePairHasCommonInterleaver_of_orientationAlternative_nonneg hsame)
    hsucc _hf_rr_ne hf_rr_splits _hg_rr_ne hg_rr_splits hf_pos hg_pos hfg

private theorem compatiblePairHasCommonInterleaver_of_realRootedPosComboBridge
    (hbridge :
      ∀ ⦃f g : ℝ[X]⦄,
        f ≠ 0 →
        f.Splits →
        g ≠ 0 →
        g.Splits →
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        PosComboRealRooted f g →
        ∃ h : ℝ[X], Prec f h ∧ Prec g h) :
    CompatiblePairHasCommonInterleaverStatement := by
  intro f g hf_pos hg_pos hfg
  have hf_rr : (f ≠ 0 ∧ f.Splits) := hfg.isRealRooted_left hf_pos
  have hg_rr : (g ≠ 0 ∧ g.Splits) := hfg.isRealRooted_right hg_pos
  exact hbridge hf_rr.1 hf_rr.2 hg_rr.1 hg_rr.2 hf_pos hg_pos
    (hfg.toPosComboRealRooted hf_pos hg_pos)

/-- Shifted compatibility bridge using the repaired same-degree
common-interleaver branch directly. -/
theorem compatiblePairHasCommonInterleaver_of_pairDegreeSplit_via_nonnegShift
    (hsame : PosComboNoCommonSameDegreePairHasCommonInterleaverNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement) :
    CompatiblePairHasCommonInterleaverStatement :=
  compatiblePairHasCommonInterleaver_of_realRootedPosComboBridge
    (fun {_ _} hf_ne hf_splits hg_ne hg_splits hf_pos hg_pos hfg =>
      posComboPairHasCommonInterleaver_of_pairDegreeSplit_via_nonnegShift
        hsame hsucc hf_ne hf_splits hg_ne hg_splits hf_pos hg_pos hfg)

/-- Shifted compatibility bridge from the concrete slot-data endpoints for the
same-degree and succ-degree nonnegative branches. -/
theorem compatiblePairHasCommonInterleaver_of_slotData_via_nonnegShift
    (hsame : PosComboNoCommonSameDegreeSlotDataNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreeSlotDataNonnegStatement) :
    CompatiblePairHasCommonInterleaverStatement :=
  compatiblePairHasCommonInterleaver_of_pairDegreeSplit_via_nonnegShift
    (sameDegreePairHasCommonInterleaver_nonneg_of_slotData hsame)
    (succDegreePairHasCommonInterleaver_nonneg_of_slotData hsucc)

/-- Shifted compatibility bridge from the root-crossing formulations of the
nonnegative same-degree and succ-degree branches.  The succ-degree branch also
needs the left-splitting input that is part of its slot-data decomposition. -/
theorem compatiblePairHasCommonInterleaver_of_rootCrossing_via_nonnegShift
    (hsame : PosComboNoCommonSameDegreeRootCrossingNonnegStatement)
    (hsplit : PosComboSuccDegreeLeftSplitsNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreeRootCrossingNonnegStatement) :
    CompatiblePairHasCommonInterleaverStatement :=
  compatiblePairHasCommonInterleaver_of_pairDegreeSplit_via_nonnegShift
    (sameDegreePairHasCommonInterleaver_nonneg_of_rootCrossing hsame)
    (succDegreePairHasCommonInterleaver_nonneg_of_leftSplits_and_rootCrossing
      hsplit hsucc)

/-- Shifted compatibility bridge from root-crossing formulations alone.  The
succ-degree left endpoint is supplied by the root-continuity theorem. -/
theorem compatiblePairHasCommonInterleaver_of_rootCrossing
    (hsame : PosComboNoCommonSameDegreeRootCrossingNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreeRootCrossingNonnegStatement) :
    CompatiblePairHasCommonInterleaverStatement :=
  compatiblePairHasCommonInterleaver_of_rootCrossing_via_nonnegShift
    hsame PosComboSuccDegreeLeftSplitsNonnegStatement_of_rootContinuity hsucc

/-- Shifted compatibility bridge from lower-threshold root-count
formulations.  The succ-degree left endpoint is supplied by the
root-continuity theorem before shifting. -/
theorem compatiblePairHasCommonInterleaver_of_rootCount
    (hsame : PosComboNoCommonSameDegreeRootCountNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreeRootCountNonnegStatement) :
    CompatiblePairHasCommonInterleaverStatement :=
  compatiblePairHasCommonInterleaver_of_rootCrossing
    (posComboNoCommonSameDegreeRootCrossing_of_rootCount hsame)
    (posComboNoCommonSuccDegreeRootCrossing_of_rootCount hsucc)

/-- Shifted compatibility bridge from same-degree lower-threshold root counts
and succ-degree upper-threshold root counts. -/
theorem compatiblePairHasCommonInterleaver_of_rootCountAbove
    (hsame : PosComboNoCommonSameDegreeRootCountNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreeRootCountAboveNonnegStatement) :
    CompatiblePairHasCommonInterleaverStatement :=
  compatiblePairHasCommonInterleaver_of_rootCrossing
    (posComboNoCommonSameDegreeRootCrossing_of_rootCount hsame)
    (posComboNoCommonSuccDegreeRootCrossing_of_rootCountAbove hsucc)

/-- Shifted compatibility bridge from same-degree upper-threshold root counts
and succ-degree lower-threshold root counts. -/
theorem compatiblePairHasCommonInterleaver_of_sameRootCountAbove
    (hsame : PosComboNoCommonSameDegreeRootCountAboveNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreeRootCountNonnegStatement) :
    CompatiblePairHasCommonInterleaverStatement :=
  compatiblePairHasCommonInterleaver_of_rootCrossing
    (posComboNoCommonSameDegreeRootCrossing_of_rootCountAbove hsame)
    (posComboNoCommonSuccDegreeRootCrossing_of_rootCount hsucc)

/-- Shifted compatibility bridge from upper-threshold root-count formulations
in both the same-degree and succ-degree branches. -/
theorem compatiblePairHasCommonInterleaver_of_rootCountAboveBoth
    (hsame : PosComboNoCommonSameDegreeRootCountAboveNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreeRootCountAboveNonnegStatement) :
    CompatiblePairHasCommonInterleaverStatement :=
  compatiblePairHasCommonInterleaver_of_rootCrossing
    (posComboNoCommonSameDegreeRootCrossing_of_rootCountAbove hsame)
    (posComboNoCommonSuccDegreeRootCrossing_of_rootCountAbove hsucc)

/-- Shifted compatibility bridge from common-non-root lower-threshold root-count
formulations in both branches. -/
theorem compatiblePairHasCommonInterleaver_of_rootCountNonRoot
    (hsame : PosComboNoCommonSameDegreeRootCountNonRootNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreeRootCountNonRootNonnegStatement) :
    CompatiblePairHasCommonInterleaverStatement :=
  compatiblePairHasCommonInterleaver_of_rootCrossing
    (posComboNoCommonSameDegreeRootCrossing_of_rootCountNonRoot hsame)
    (posComboNoCommonSuccDegreeRootCrossing_of_rootCountNonRoot hsucc)

/-- Shifted compatibility bridge from same-degree common-non-root
lower-threshold root counts and succ-degree common-non-root upper-threshold
root counts. -/
theorem compatiblePairHasCommonInterleaver_of_rootCountAboveNonRoot
    (hsame : PosComboNoCommonSameDegreeRootCountNonRootNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreeRootCountAboveNonRootNonnegStatement) :
    CompatiblePairHasCommonInterleaverStatement :=
  compatiblePairHasCommonInterleaver_of_rootCrossing
    (posComboNoCommonSameDegreeRootCrossing_of_rootCountNonRoot hsame)
    (posComboNoCommonSuccDegreeRootCrossing_of_rootCountAboveNonRoot hsucc)

/-- Shifted compatibility bridge from same-degree common-non-root
upper-threshold root counts and succ-degree common-non-root lower-threshold
root counts. -/
theorem compatiblePairHasCommonInterleaver_of_sameRootCountAboveNonRoot
    (hsame : PosComboNoCommonSameDegreeRootCountAboveNonRootNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreeRootCountNonRootNonnegStatement) :
    CompatiblePairHasCommonInterleaverStatement :=
  compatiblePairHasCommonInterleaver_of_rootCrossing
    (posComboNoCommonSameDegreeRootCrossing_of_rootCountAboveNonRoot hsame)
    (posComboNoCommonSuccDegreeRootCrossing_of_rootCountNonRoot hsucc)

/-- Shifted compatibility bridge from common-non-root upper-threshold root-count
formulations in both branches. -/
theorem compatiblePairHasCommonInterleaver_of_rootCountAboveBothNonRoot
    (hsame : PosComboNoCommonSameDegreeRootCountAboveNonRootNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreeRootCountAboveNonRootNonnegStatement) :
    CompatiblePairHasCommonInterleaverStatement :=
  compatiblePairHasCommonInterleaver_of_rootCrossing
    (posComboNoCommonSameDegreeRootCrossing_of_rootCountAboveNonRoot hsame)
    (posComboNoCommonSuccDegreeRootCrossing_of_rootCountAboveNonRoot hsucc)

/-- Shifted compatibility bridge from root-crossing formulations, with the
succ-degree left endpoint supplied by the PF/ASW route. -/
theorem compatiblePairHasCommonInterleaver_of_rootCrossing_and_forward_asw
    (hsame : PosComboNoCommonSameDegreeRootCrossingNonnegStatement)
    (hASW : aissenSchoenbergWhitneyForwardOrZeroStatement)
    (hsucc : PosComboNoCommonSuccDegreeRootCrossingNonnegStatement) :
    CompatiblePairHasCommonInterleaverStatement :=
  compatiblePairHasCommonInterleaver_of_rootCrossing_via_nonnegShift
    hsame (PosComboSuccDegreeLeftSplitsNonnegStatement_of_forward_asw hASW) hsucc

/-- Shifted compatibility bridge from root-crossing formulations, with the
succ-degree left endpoint supplied by the splitting-only ASW target. -/
theorem compatiblePairHasCommonInterleaver_of_rootCrossing_and_forward_asw_splits
    (hsame : PosComboNoCommonSameDegreeRootCrossingNonnegStatement)
    (hASW : aissenSchoenbergWhitneyForwardSplitsStatement)
    (hsucc : PosComboNoCommonSuccDegreeRootCrossingNonnegStatement) :
    CompatiblePairHasCommonInterleaverStatement :=
  compatiblePairHasCommonInterleaver_of_rootCrossing_and_forward_asw
    hsame (aissenSchoenbergWhitneyForwardOrZero_of_splits hASW) hsucc

/-- Translation reduces the full positive-leading compatibility bridge to the
nonnegative-coefficient degree-split package: shift both polynomials far enough
to the right so all roots become nonpositive, apply the nonnegative theorem,
then translate the common interleaver back. -/
theorem compatiblePairHasCommonInterleaver_of_degreeSplit_via_nonnegShift
    (hsame : PosComboNoCommonSameDegreeOrientationAlternativeNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement) :
    CompatiblePairHasCommonInterleaverStatement :=
  compatiblePairHasCommonInterleaver_of_pairDegreeSplit_via_nonnegShift
    (posComboNoCommonSameDegreePairHasCommonInterleaver_of_orientationAlternative_nonneg hsame)
    hsucc

/-- Shifted positive-leading compatibility bridge with the succ-degree branch
discharged by the affine-family bridge.  This leaves only the same-degree
orientation alternative as an external hypothesis. -/
theorem compatiblePairHasCommonInterleaver_of_sameDegreeAlternative_and_affineFamily_via_nonnegShift
    (hsame : PosComboNoCommonSameDegreeOrientationAlternativeNonnegStatement)
    (haffBridge : PosComboNoCommonAffineFamilyStatement) :
    CompatiblePairHasCommonInterleaverStatement :=
  compatiblePairHasCommonInterleaver_of_degreeSplit_via_nonnegShift
    hsame
    (posComboNoCommonSuccDegreePairHasCommonInterleaver_of_affineFamily haffBridge)

/-- Shifted positive-leading compatibility bridge with the succ-degree branch
discharged by the affine-family bridge and the same-degree branch stated in the
repaired common-right-interleaver form. -/
theorem compatiblePairHasCommonInterleaver_of_sameDegreePair_and_affineFamily_via_nonnegShift
    (hsame : PosComboNoCommonSameDegreePairHasCommonInterleaverNonnegStatement)
    (haffBridge : PosComboNoCommonAffineFamilyStatement) :
    CompatiblePairHasCommonInterleaverStatement :=
  compatiblePairHasCommonInterleaver_of_pairDegreeSplit_via_nonnegShift
    hsame
    (posComboNoCommonSuccDegreePairHasCommonInterleaver_of_affineFamily haffBridge)

/-- The stronger boundary-right-pair orientation hypothesis already finishes
the positive-leading positive-combination bridge after the nonnegative shift
reduction, provided the summands are individually real-rooted. -/
theorem posComboPairHasCommonInterleaver_of_boundaryRightPairOrientation_via_nonnegShift
    (hboundary : PosComboNoCommonBoundaryRightPairOrientationStatement)
    {f g : ℝ[X]}
    (hf_rr_ne : f ≠ 0) (hf_rr_splits : f.Splits) (hg_rr_ne : g ≠ 0) (hg_rr_splits : g.Splits)
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfg : PosComboRealRooted f g) :
    ∃ h : ℝ[X], Prec f h ∧ Prec g h :=
  posComboPairHasCommonInterleaver_of_degreeSplit_via_nonnegShift
    (boundaryRightPairOrientation_implies_sameDegreeOrientationAlternative_nonneg
      hboundary)
    (succDegreePairHasCommonInterleaver_nonneg_of_boundaryRightPairOrientation
      hboundary)
    hf_rr_ne hf_rr_splits hg_rr_ne hg_rr_splits hf_pos hg_pos hfg

/-- The stronger boundary-right-pair orientation hypothesis already finishes
the full positive-leading compatibility bridge after the nonnegative shift
reduction. -/
theorem compatiblePairHasCommonInterleaver_of_boundaryRightPairOrientation_via_nonnegShift
    (hboundary : PosComboNoCommonBoundaryRightPairOrientationStatement) :
    CompatiblePairHasCommonInterleaverStatement :=
  compatiblePairHasCommonInterleaver_of_sameDegreeAlternative_and_affineFamily_via_nonnegShift
    (boundaryRightPairOrientation_implies_sameDegreeOrientationAlternative_nonneg
      hboundary)
    (posComboNoCommonAffineFamily_of_boundaryRightPairOrientation hboundary)

end RealRooted
