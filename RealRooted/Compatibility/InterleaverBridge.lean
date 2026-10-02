import RealRooted.Compatibility.Basic
import RealRooted.CommonInterleaverSeq

/-!
# Compatibility from common interleavers

A family with a common (left or right) interleaver, or with pairwise common
interleavers, is pairwise compatible: the easy direction of
Chudnovsky--Seymour.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- A family with a common left interleaver is pairwise compatible. This is
the easy Chudnovsky--Seymour direction. -/
theorem pairwiseCompatible_of_commonLeftInterleaver
    {fs : List ℝ[X]}
    (hcommon : HasCommonLeftInterleaver fs)
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f) :
    PairwiseCompatible fs :=
  let ⟨_, hstrictInterl⟩ := hcommon
  fun i j _ => Compatible.of_commonLeftInterleaver
    (hstrictInterl (fs.get i) (fs.get_mem i))
    (hstrictInterl (fs.get j) (fs.get_mem j))
    (hpos (fs.get i) (fs.get_mem i))
    (hpos (fs.get j) (fs.get_mem j))

/-- The same easy direction, but starting from pairwise common left
interleavers rather than a single global witness. -/
theorem pairwiseCompatible_of_pairwiseHasCommonLeftInterleaver
    {fs : List ℝ[X]}
    (hpair : PairwiseHasCommonLeftInterleaver fs)
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f) :
    PairwiseCompatible fs :=
  fun i j hij =>
    let ⟨_, hwf, hwg⟩ := hpair i j hij
    Compatible.of_commonLeftInterleaver hwf hwg
      (hpos (fs.get i) (fs.get_mem i))
      (hpos (fs.get j) (fs.get_mem j))

/-- A family with a common right interleaver is pairwise compatible. -/
theorem pairwiseCompatible_of_commonInterleaver
    {fs : List ℝ[X]}
    (hcommon : HasCommonInterleaver fs)
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f) :
    PairwiseCompatible fs :=
  let ⟨_, hstrictInterl⟩ := hcommon
  fun i j _ => Compatible.of_commonInterleaver
    (hstrictInterl (fs.get i) (fs.get_mem i))
    (hstrictInterl (fs.get j) (fs.get_mem j))
    (hpos (fs.get i) (fs.get_mem i))
    (hpos (fs.get j) (fs.get_mem j))

/-- Pairwise common right interleavers imply pairwise compatibility. -/
theorem pairwiseCompatible_of_pairwiseHasCommonInterleaver
    {fs : List ℝ[X]}
    (hpair : PairwiseHasCommonInterleaver fs)
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f) :
    PairwiseCompatible fs :=
  fun i j hij =>
    let ⟨_, hwf, hwg⟩ := hpair i j hij
    Compatible.of_commonInterleaver hwf hwg
      (hpos (fs.get i) (fs.get_mem i))
      (hpos (fs.get j) (fs.get_mem j))

/-- Compatibility plus positive leading coefficients implies a common right
interleaver.  This is proved by
`chudnovskySeymour_compatiblePairHasCommonInterleaver`; the proposition is kept
only for its `LiuOppositeSigns` callers. -/
def CompatiblePairHasCommonInterleaverStatement : Prop :=
  ∀ ⦃f g : ℝ[X]⦄,
    HasPosLeadingCoeff f →
    HasPosLeadingCoeff g →
    Compatible f g →
    ∃ h : ℝ[X], StrictInterl f h ∧ StrictInterl g h

end RealRooted
