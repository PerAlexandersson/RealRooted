import RealRooted.ChudnovskySeymour.Core

/-!
# Chudnovsky--Seymour roadmap reductions

This module extends the proved pair/family core with generic roadmap reductions
and their first direct successor-degree adapters. Clients needing only the
proved core theorem surface should import
`RealRooted.ChudnovskySeymour.Core`.
-/

noncomputable section

namespace RealRooted

open Polynomial

/-- The nonnegative-coefficient finite-family compatibility target is a formal
consequence of the corresponding common-interleaver target. -/
theorem
    chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_of_commonInterleaver_nonneg
    (hcommon : chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_nonnegCoeffs_target) :
    chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_nonnegCoeffs_target :=
  fun hrr hpos hnn =>
    pairwiseCompatible_iff_familyCompatible_of_commonInterleaver_forward hpos
      (hcommon hrr hpos hnn).1

/-- The nonnegative-coefficient finite-family compatibility target follows
from the repaired same-degree and successor-degree no-common pair bridges. -/
theorem
    chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_of_pairDegreeSplit_nonneg
    (hsame : PosComboNoCommonSameDegreePairHasCommonInterleaverNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement) :
    chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_nonnegCoeffs_target :=
  chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_of_commonInterleaver_nonneg
    (chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_of_pairDegreeSplit_nonneg
      hsame hsucc)

end RealRooted
