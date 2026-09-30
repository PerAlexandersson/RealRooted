import RealRooted.LiuOppositeSigns.FactorReturnAssembly.PredicateDegreeCases

/-!
# Liu factor-return degree-case assembly

This module assembles the six ordinary degree cases into the final deletion-pair
factor-return principle and its translated and x-subtraction consequences.
-/

open Polynomial Filter

namespace RealRooted
namespace LiuOppositeSigns

/-- Degree-case split needed to prove the factor-return principle. -/
def theorem21DeletionPairCommonInterleaverFactorReturnDegreeCasesStatement :
    Prop :=
  theorem21LeftFactorReturnSameDegreeStatement ∧
    theorem21LeftFactorReturnSuccDegreeStatement ∧
      theorem21LeftFactorReturnTwoDegreeStatement ∧
        theorem21RightFactorReturnSameDegreeStatement ∧
          theorem21RightFactorReturnSuccDegreeStatement ∧
            theorem21RightFactorReturnTwoDegreeStatement

/-- Left and right factor-return degree cases assemble into the full six-case
package. -/
theorem theorem21DeletionPairCommonInterleaverFactorReturnDegreeCases_of_leftRightCases
    (hleft : theorem21LeftFactorReturnDegreeCasesStatement)
    (hright : theorem21RightFactorReturnDegreeCasesStatement) :
    theorem21DeletionPairCommonInterleaverFactorReturnDegreeCasesStatement :=
  ⟨hleft.1, hleft.2.1, hleft.2.2,
    hright.1, hright.2.1, hright.2.2⟩

/-- Left projection from a six-case ordinary factor-return package. -/
theorem theorem21LeftFactorReturnDegreeCases_of_factorCases
    (hcases :
      theorem21DeletionPairCommonInterleaverFactorReturnDegreeCasesStatement) :
    theorem21LeftFactorReturnDegreeCasesStatement :=
  ⟨hcases.1, hcases.2.1, hcases.2.2.1⟩

/-- Right projection from a six-case ordinary factor-return package. -/
theorem theorem21RightFactorReturnDegreeCases_of_factorCases
    (hcases :
      theorem21DeletionPairCommonInterleaverFactorReturnDegreeCasesStatement) :
    theorem21RightFactorReturnDegreeCasesStatement :=
  ⟨hcases.2.2.2.1, hcases.2.2.2.2.1, hcases.2.2.2.2.2⟩

/-- All-combinations factor-return degree cases give the corresponding
compatibility factor-return degree cases. -/
theorem theorem21DeletionPairCommonInterleaverFactorReturnDegreeCases_of_allComboDegreeCases
    (hcases :
      theorem21DeletionPairCommonInterleaverFactorReturnAllComboDegreeCasesStatement) :
    theorem21DeletionPairCommonInterleaverFactorReturnDegreeCasesStatement :=
  theorem21DeletionPairCommonInterleaverFactorReturnDegreeCases_of_leftRightCases
    (theorem21LeftFactorReturnDegreeCases_of_allComboCases
      (theorem21LeftFactorReturnAllComboDegreeCases_of_allComboFactorCases
        hcases))
    (theorem21RightFactorReturnDegreeCases_of_allComboCases
      (theorem21RightFactorReturnAllComboDegreeCases_of_allComboFactorCases
        hcases))

/-- Left factor-return degree cases supply all six left/right cases by
symmetry. -/
theorem theorem21DeletionPairCommonInterleaverFactorReturnDegreeCases_of_leftCases
    (hcases : theorem21LeftFactorReturnDegreeCasesStatement) :
    theorem21DeletionPairCommonInterleaverFactorReturnDegreeCasesStatement :=
  theorem21DeletionPairCommonInterleaverFactorReturnDegreeCases_of_leftRightCases
    hcases
    (theorem21RightFactorReturnDegreeCases_of_leftCases hcases)

/-- The explicit factor-return principle follows from its six restored-degree
cases. -/
theorem theorem21DeletionPairCommonInterleaverFactorReturn_of_degreeCases
    (hcases :
      theorem21DeletionPairCommonInterleaverFactorReturnDegreeCasesStatement) :
    theorem21DeletionPairCommonInterleaverFactorReturnStatement := by
  let hleftCases := theorem21LeftFactorReturnDegreeCases_of_factorCases hcases
  let hrightCases := theorem21RightFactorReturnDegreeCases_of_factorCases hcases
  intro f g r s hf hg hsgn
  constructor
  · intro hleft hcommon
    rcases hleft.natDegree_eq_or_eq_succ_or_eq_succ_succ
        hsgn.left_ne_zero hf hg with hdeg | hdeg | hdeg
    · exact hleftCases.1 hf hg hsgn hleft hdeg hcommon
    · exact hleftCases.2.1 hf hg hsgn hleft hdeg hcommon
    · exact hleftCases.2.2 hf hg hsgn hleft hdeg hcommon
  · intro hright hcommon
    rcases hright.natDegree_eq_or_eq_succ_or_eq_succ_succ
        hsgn.right_ne_zero hf hg with hdeg | hdeg | hdeg
    · exact hrightCases.1 hf hg hsgn hright hdeg hcommon
    · exact hrightCases.2.1 hf hg hsgn hright hdeg hcommon
    · exact hrightCases.2.2 hf hg hsgn hright hdeg hcommon

/-- It is enough to prove the left-branch factor-return cases; the right branch
is symmetric. -/
theorem theorem21DeletionPairCommonInterleaverFactorReturn_of_leftCases
    (hcases : theorem21LeftFactorReturnDegreeCasesStatement) :
    theorem21DeletionPairCommonInterleaverFactorReturnStatement :=
  theorem21DeletionPairCommonInterleaverFactorReturn_of_degreeCases
    (theorem21DeletionPairCommonInterleaverFactorReturnDegreeCases_of_leftCases
      hcases)

/-- All-combinations factor-return degree cases imply the compatibility
factor-return principle used by the reverse direction. -/
theorem theorem21DeletionPairCommonInterleaverFactorReturn_of_allComboDegreeCases
    (hcases :
      theorem21DeletionPairCommonInterleaverFactorReturnAllComboDegreeCasesStatement) :
    theorem21DeletionPairCommonInterleaverFactorReturnStatement :=
  theorem21DeletionPairCommonInterleaverFactorReturn_of_degreeCases
    (theorem21DeletionPairCommonInterleaverFactorReturnDegreeCases_of_allComboDegreeCases
      hcases)

/-- Left all-combinations factor-return degree cases imply the compatibility
factor-return principle used by the reverse direction. -/
theorem theorem21DeletionPairCommonInterleaverFactorReturn_of_leftAllComboCases
    (hcases : theorem21LeftFactorReturnAllComboDegreeCasesStatement) :
    theorem21DeletionPairCommonInterleaverFactorReturnStatement :=
  theorem21DeletionPairCommonInterleaverFactorReturn_of_leftCases
    (theorem21LeftFactorReturnDegreeCases_of_allComboCases hcases)

/-- A bundled sign-normalized positive-split x-subtraction case package
implies the factor-return principle used by the reverse direction. -/
theorem theorem21DeletionPairCommonInterleaverFactorReturn_of_xSubCasePackage
    (hcases :
      positiveSplitTranslatedXSubRightFamilyDegreeCasesStatement) :
    theorem21DeletionPairCommonInterleaverFactorReturnStatement :=
  theorem21DeletionPairCommonInterleaverFactorReturn_of_leftCases
    (theorem21LeftFactorReturnDegreeCases_of_xSubCasePackage
      hcases)

/-- Sign-normalized positive-split x-subtraction cases imply the
factor-return principle used by the reverse direction. -/
theorem theorem21DeletionPairCommonInterleaverFactorReturn_of_xSubCases
    (hrightSucc :
      positiveSplitRightSuccDegreeTranslatedXSubRightFamilyStatement)
    (hsame : positiveSplitSameDegreeTranslatedXSubRightFamilyStatement)
    (hleftSucc :
      positiveSplitLeftSuccDegreeTranslatedXSubRightFamilyStatement) :
    theorem21DeletionPairCommonInterleaverFactorReturnStatement :=
  theorem21DeletionPairCommonInterleaverFactorReturn_of_xSubCasePackage
    ⟨hrightSucc, hsame, hleftSucc⟩

/-- Since the same-degree and left-successor x-subtraction cases are proved, the
reverse factor-return principle only needs the remaining right-successor
x-subtraction leaf. -/
theorem theorem21DeletionPairCommonInterleaverFactorReturn_of_rightSucc_xSub
    (hrightSucc :
      positiveSplitRightSuccDegreeTranslatedXSubRightFamilyStatement) :
    theorem21DeletionPairCommonInterleaverFactorReturnStatement :=
  theorem21DeletionPairCommonInterleaverFactorReturn_of_xSubCases
    hrightSucc positiveSplitSameDegreeTranslatedXSubRightFamily
    positiveSplitLeftSuccDegreeTranslatedXSubRightFamily

/-- The proved sign-normalized positive-split x-subtraction cases imply the
factor-return principle used by the reverse direction. -/
theorem theorem21DeletionPairCommonInterleaverFactorReturn_of_xSub :
    theorem21DeletionPairCommonInterleaverFactorReturnStatement :=
  theorem21DeletionPairCommonInterleaverFactorReturn_of_xSubCasePackage
    positiveSplitTranslatedXSubRightFamilyDegreeCases

/-- The factor-return principle follows from same/succ left leaves and the
translated two-degree compatibility target. -/
theorem theorem21DeletionPairCommonInterleaverFactorReturn_of_sameSucc_and_translatedTwo
    (hsame : theorem21LeftFactorReturnSameDegreeStatement)
    (hsucc : theorem21LeftFactorReturnSuccDegreeStatement)
    (htwo : theorem21LeftFactorReturnTwoDegreeTranslatedCompatibleStatement) :
    theorem21DeletionPairCommonInterleaverFactorReturnStatement :=
  theorem21DeletionPairCommonInterleaverFactorReturn_of_leftCases
    (theorem21LeftFactorReturnDegreeCases_of_sameSucc_and_translatedTwo
      hsame hsucc htwo)

/-- The factor-return principle follows from same/succ left leaves and the
translated right-family two-degree target. -/
theorem theorem21DeletionPairCommonInterleaverFactorReturn_of_sameSucc_and_rightFamily
    (hsame : theorem21LeftFactorReturnSameDegreeStatement)
    (hsucc : theorem21LeftFactorReturnSuccDegreeStatement)
    (hright :
      theorem21LeftFactorReturnTwoDegreeTranslatedRightFamilyStatement) :
    theorem21DeletionPairCommonInterleaverFactorReturnStatement :=
  theorem21DeletionPairCommonInterleaverFactorReturn_of_leftCases
    (theorem21LeftFactorReturnDegreeCases_of_sameSucc_and_rightFamily
      hsame hsucc hright)

/-- The factor-return principle follows from same/succ left leaves and the
sign-normalized positive-split subtraction-family leaf. -/
theorem theorem21DeletionPairCommonInterleaverFactorReturn_of_sameSucc_and_xSub
    (hsame : theorem21LeftFactorReturnSameDegreeStatement)
    (hsucc : theorem21LeftFactorReturnSuccDegreeStatement)
    (hsub :
      positiveSplitLeftSuccDegreeTranslatedXSubRightFamilyStatement) :
    theorem21DeletionPairCommonInterleaverFactorReturnStatement :=
  theorem21DeletionPairCommonInterleaverFactorReturn_of_sameSucc_and_rightFamily
    hsame hsucc
    (theorem21LeftFactorReturnTwoDegreeTranslatedRightFamily_of_xSub hsub)

end LiuOppositeSigns
end RealRooted
