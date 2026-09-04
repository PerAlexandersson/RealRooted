/-
# Global and full-family common-interleaver compatibility

This module relates global common interleavers, pairwise common interleavers,
and compatibility of all nonnegative weighted sums.
-/
import RealRooted.CommonInterleaver.PairwiseUpgrade

open Polynomial

noncomputable section

namespace RealRooted

/-- A single common right interleaver is in particular a pairwise common right
interleaver witness. -/
theorem pairwiseHasCommonInterleaver_of_commonInterleaver
    {fs : List ℝ[X]}
    (hcommon : HasCommonInterleaver fs) :
    PairwiseHasCommonInterleaver fs :=
  Exists.elim hcommon fun h hprec i j _ => ⟨h,
    hprec (fs.get i) (List.get_mem _ _),
    hprec (fs.get j) (List.get_mem _ _)⟩

/-- A single common left interleaver is in particular a pairwise common left
interleaver witness. -/
theorem pairwiseHasCommonLeftInterleaver_of_commonLeftInterleaver
    {fs : List ℝ[X]}
    (hcommon : HasCommonLeftInterleaver fs) :
    PairwiseHasCommonLeftInterleaver fs :=
  Exists.elim hcommon fun h hprec i j _ => ⟨h,
    hprec (fs.get i) (List.get_mem _ _),
    hprec (fs.get j) (List.get_mem _ _)⟩

/-- A common right interleaver yields full family compatibility for all
nonnegative weighted sums. -/
theorem familyCompatible_of_commonInterleaver
    {fs : List ℝ[X]}
    (hcommon : HasCommonInterleaver fs)
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f) :
    FamilyCompatible fs := by
  obtain ⟨h, hprec⟩ := hcommon
  intro l hmem hnonneg
  by_cases hex : ∃ ap ∈ l, 0 < ap.1
  · exact Or.inr (prec_weightedSum_right l h hnonneg
      (fun ap hap => hprec ap.2 (hmem ap hap))
      (fun ap hap => hpos ap.2 (hmem ap hap)) hex).1
  · exact Or.inl (weightedSum_eq_zero_of_forall_coeff_zero l fun ap hap =>
      le_antisymm (not_lt.1 fun hlt => hex ⟨ap, hap, hlt⟩) (hnonneg ap hap))

/-- Full family compatibility implies pairwise compatibility by specializing to
two-term weighted sums. -/
theorem pairwiseCompatible_of_familyCompatible
    {fs : List ℝ[X]}
    (hfull : FamilyCompatible fs) :
    PairwiseCompatible fs := by
  intro i j _hij α β hα hβ
  have hpair := hfull [(α, fs.get i), (β, fs.get j)]
    (by simp)
    (by simp [hα, hβ])
  simpa [weightedSum] using hpair

/-- A forward common-interleaver upgrade is enough to identify pairwise
compatibility with full family compatibility for positive-leading families. -/
theorem pairwiseCompatible_iff_familyCompatible_of_commonInterleaver_forward
    {fs : List ℝ[X]}
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hcommon : PairwiseCompatible fs → HasCommonInterleaver fs) :
    PairwiseCompatible fs ↔ FamilyCompatible fs :=
  ⟨fun hpair => familyCompatible_of_commonInterleaver (hcommon hpair) hpos,
    pairwiseCompatible_of_familyCompatible⟩

/-- Roadmap target for the common-interlacing form of the
Chudnovsky--Seymour theorem used in `INTERLACING.md`.

The finite-family left-handed Helly upgrade is now packaged as
`CommonLeftInterleaverFamilyUpgradeStatement`, so the remaining input is the
two-polynomial bridge
`Compatible f g -> ∃ h, Prec h f ∧ Prec h g`. -/
def chudnovskySeymour_pairwiseCompatible_iff_commonLeftInterleaver_statement : Prop :=
  ∀ {fs : List ℝ[X]},
    (∀ f ∈ fs, (f ≠ 0 ∧ f.Splits)) →
    (∀ f ∈ fs, HasPosLeadingCoeff f) →
    (PairwiseCompatible fs ↔ HasCommonLeftInterleaver fs)
end RealRooted
