/-
# Four-way finite-family equivalences

This module extracts equivalences from four-way common-interleaver packages
and provides their endpoint-specific compatibility corollaries.
-/
import RealRooted.CommonInterleaver.PairwiseUpgrade.FourWay

open Polynomial

noncomputable section

namespace RealRooted

/-- Extract the `1 ↔ 2` Chudnovsky--Seymour equivalence from the four-way
package. -/
theorem pairwiseCompatible_iff_pairwiseHasCommonInterleaver_of_fourWay
    {fs : List ℝ[X]}
    (hfour : ChudnovskySeymourFourWayPackage fs) :
    PairwiseCompatible fs ↔ PairwiseHasCommonInterleaver fs :=
  hfour.1

/-- Extract the `2 ↔ 3` Chudnovsky--Seymour equivalence from the four-way
package. -/
theorem pairwiseHasCommonInterleaver_iff_hasCommonInterleaver_of_fourWay
    {fs : List ℝ[X]}
    (hfour : ChudnovskySeymourFourWayPackage fs) :
    PairwiseHasCommonInterleaver fs ↔ HasCommonInterleaver fs :=
  hfour.2.1

/-- Extract the `3 ↔ 4` Chudnovsky--Seymour equivalence from the four-way
package. -/
theorem hasCommonInterleaver_iff_familyCompatible_of_fourWay
    {fs : List ℝ[X]}
    (hfour : ChudnovskySeymourFourWayPackage fs) :
    HasCommonInterleaver fs ↔ FamilyCompatible fs :=
  hfour.2.2

/-- Extract the `1 ↔ 3` Chudnovsky--Seymour equivalence from the four-way
package. -/
theorem pairwiseCompatible_iff_hasCommonInterleaver_of_fourWay
    {fs : List ℝ[X]}
    (hfour : ChudnovskySeymourFourWayPackage fs) :
    PairwiseCompatible fs ↔ HasCommonInterleaver fs :=
  (pairwiseCompatible_iff_pairwiseHasCommonInterleaver_of_fourWay hfour).trans
    (pairwiseHasCommonInterleaver_iff_hasCommonInterleaver_of_fourWay hfour)

/-- Extract the `1 ↔ 4` Chudnovsky--Seymour equivalence from the four-way
package. -/
theorem pairwiseCompatible_iff_familyCompatible_of_fourWay
    {fs : List ℝ[X]}
    (hfour : ChudnovskySeymourFourWayPackage fs) :
    PairwiseCompatible fs ↔ FamilyCompatible fs :=
  (pairwiseCompatible_iff_hasCommonInterleaver_of_fourWay hfour).trans
    (hasCommonInterleaver_iff_familyCompatible_of_fourWay hfour)

end RealRooted
