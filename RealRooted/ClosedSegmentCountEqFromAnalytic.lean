import RealRooted.CommonInterleaverTwo
import RealRooted.DegreeIncreasingLocalLowerCount
import RealRooted.SmallPositiveParameterCount

/-!
# Closed-Segment Count Equality from Analytic Inputs

This file packages the issue #42 analytic route into the central
closed-segment count-equality target.  The degree-increasing lower-count input
handles the small-positive endpoint, and the positive-parameter same-degree
lower-count input handles local constancy along the two positive parameter
families.
-/

open Polynomial

namespace RealRooted

/--
The central closed-segment count-equality target follows from the proved
degree-increasing and positive-parameter local lower-count inputs.
-/
private theorem compatibleSuccDegreeClosedSegmentCountEq_of_local_lower_counts :
    CompatibleSuccDegreeClosedSegmentCountEqStatement := by
  intro f g hcomp hf_pos hg_pos hdeg hf_split x hxf hxg hseg
  have hx_roots : x ∉ f.roots :=
    fun hx => hxf ((Polynomial.mem_roots hf_pos.ne_zero).mp hx)
  have hlt : f.natDegree < g.natDegree := by
    simp [hdeg]
  have hfg_split_pos : ∀ μ : ℝ, 0 < μ → (f + C μ * g).Splits := by
    intro μ hμ
    rcases hcomp 1 μ zero_le_one hμ.le with hzero | hrr
    · rw [show f + C μ * g = 0 by simpa using hzero]
      simp
    · simpa using hrr.2
  have hgf_split : ∀ ν ∈ Set.Icc (0 : ℝ) 1, (g + C ν * f).Splits := by
    intro ν hν
    rcases hcomp.comm 1 ν zero_le_one hν.1 with hzero | hrr
    · rw [show g + C ν * f = 0 by simpa using hzero]
      simp
    · simpa using hrr.2
  refine card_filter_gt_endpoint_eq_of_local_lower_counts
    hf_pos hg_pos hdeg hf_split hx_roots
    ?_
    ?_ ?_ ?_ ?_
  · intro ρ hρ
    obtain ⟨δ, hδ_pos, hδ⟩ := degreeIncreasing_local_lower_count hf_split hlt ρ hρ
    refine ⟨δ, hδ_pos, ?_⟩
    intro μ hμ hμδ
    have hsplit := hfg_split_pos μ hμ
    exact ⟨hsplit, hδ μ hμ hμδ hsplit⟩
  · intro μ hμ _
    exact hfg_split_pos μ hμ
  · intro μ hμ _
    exact closedSegment_not_isRoot_add_right_of_nonneg hμ.le hseg
  · exact hgf_split
  · intro ν hν
    refine closedSegment_not_isRoot_add_right_of_nonneg
      (f := g) (g := f) (x := x) hν.1 ?_
    exact (closedSegment_forall_not_isRoot_iff_eval_mul_pos hxg hxf).mpr <|
      by simpa [mul_comm] using (closedSegment_forall_not_isRoot_iff_eval_mul_pos hxf hxg).mp hseg

/-- The proved closed-segment count equality closes the repaired succ-degree
#42 pair-interleaver endpoint. -/
theorem succDegreePairHasCommonInterleaver_nonneg_of_local_lower_counts :
    PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement :=
  succDegreePairHasCommonInterleaver_nonneg_of_closedSegmentCountEq
    compatibleSuccDegreeClosedSegmentCountEq_of_local_lower_counts

end RealRooted
