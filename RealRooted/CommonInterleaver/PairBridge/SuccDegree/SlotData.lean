import RealRooted.CommonInterleaver.PairBridge.SuccDegree

/-!
# Succ-degree case of the two-polynomial common-interleaver theorem

For a successor-degree pair whose positive combinations are real-rooted, the
lower-degree member splits, the pair is compatible, the upper root counts
differ by at most one at every threshold, and the descending roots therefore
weave into a common interleaver.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- **Successor-degree case of Chudnovsky--Seymour for two polynomials.** If
every positive combination of `f` and `g` is real-rooted, `f` and `g` have
positive leading coefficients and `g.natDegree = f.natDegree + 1`, then they
have a common interleaver. -/
theorem pairHasCommonInterleaver_of_posCombo_succDegree
    {f g : ℝ[X]} (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfg : PosComboRealRooted f g) (hsucc : g.natDegree = f.natDegree + 1) :
    ∃ h : ℝ[X], StrictInterl f h ∧ StrictInterl g h := by
  have hf_split : f.Splits :=
    splits_of_add_C_mul_family_of_succDegree
      (fun {μ} hμ => hfg.isRealRooted_add_right hμ) hf_pos hg_pos hsucc
  have hg_rr : g ≠ 0 ∧ g.Splits :=
    hfg.isRealRooted_right_of_succDegree hf_pos hg_pos hsucc
  have hcomp : Compatible f g :=
    Compatible.of_posComboRealRooted_succDegree hfg hf_pos hg_pos hsucc hf_split
  obtain ⟨hc1, hc2⟩ :=
    succDegreeRootCrossing_of_rootCountAbove hf_split hg_rr.2 hsucc <|
      rootCountAbove_diff_le_one_of_nonRoot_isRoot hf_pos.ne_zero hg_rr.1 <|
        compatibleSuccDegree_rootCountAbove_diff_le_one_of_nonRoot
          hcomp hf_pos hg_pos hsucc hf_split
  have hlenf : (rootSeqDesc f).length = f.natDegree := rootSeqDesc_length hf_split
  have hleng : (rootSeqDesc g).length = g.natDegree := rootSeqDesc_length hg_rr.2
  refine pairHasCommonInterleaver_of_succDegree_slotIntersections
    hf_pos.ne_zero hg_rr.1 hf_split hg_rr.2 hsucc ?_
  intro j _
  exact
    rootSlotInterval_inter_nonempty_of_crossing (rootSeqDesc f) (rootSeqDesc g)
      rootSeqDesc_pairwise rootSeqDesc_pairwise
      (by rw [hleng, hlenf, hsucc])
      (fun k hk1 hk2 => hc1 k hk1 (by rw [hlenf] at hk2; exact hk2))
      (fun k hk1 hk2 => hc2 k hk1 (by rw [hlenf] at hk2; exact hk2))
      j _ _

end RealRooted
