import RealRooted.CommonInterleaverSeq

/-!
# Finite compatibility families

Lean-facing Chudnovsky--Seymour corollaries for recurrence sums.  A
sequence-specific proof may establish common interleavers pair by pair; the
global family theorem in `RealRooted.CommonInterleaverSeq` then constructs one
interleaver for the entire list, and Wagner's sum theorem proves that its sum
is real-rooted.

These results are unconditional wrappers around proved library theorems.  In
particular, they do not use any of the conditional `PosComboNoCommon...`
statement interfaces.

This sequence-independent corollary family was first used in
`ProofsOeis.CompatibilityFamilies`.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- Pairwise common right interleavers certify real-rootedness of the sum of
an arbitrary nonempty finite family. -/
theorem isRealRooted_sum_of_pairwiseHasCommonInterleaver
    {fs : List ℝ[X]}
    (hsplits : ∀ f ∈ fs, f.Splits)
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hpair : PairwiseHasCommonInterleaver fs)
    (hne : fs ≠ []) :
    fs.sum ≠ 0 ∧ fs.sum.Splits := by
  apply isRealRooted_sum_of_commonInterleaver
  · exact hasCommonInterleaver_of_pairwiseHasCommonInterleaver
      hsplits hpos hpair
  · simp_all
  · simp_all

/-- Pairwise common left interleavers certify real-rootedness of the sum of
an arbitrary nonempty finite family. -/
theorem isRealRooted_sum_of_pairwiseHasCommonLeftInterleaver
    {fs : List ℝ[X]}
    (hsplits : ∀ f ∈ fs, f.Splits)
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hpair : PairwiseHasCommonLeftInterleaver fs)
    (hne : fs ≠ []) :
    fs.sum ≠ 0 ∧ fs.sum.Splits := by
  apply isRealRooted_sum_of_commonLeftInterleaver
  · exact hasCommonLeftInterleaver_of_pairwiseHasCommonLeftInterleaver
      hsplits hpos hpair
  · simp_all
  · simp_all

end RealRooted
