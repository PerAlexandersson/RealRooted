import RealRooted.Compatibility.Basic
import RealRooted.CommonInterleaverSeq

/-!
# Compatibility and common-interleaver bridge statements

This module contains the pairwise compatibility/common-interleaver bridge layer
used by the two-polynomial converse and Chudnovsky--Seymour packaging.
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
  let ⟨_, hprec⟩ := hcommon
  fun i j _ => Compatible.of_commonLeftInterleaver
    (hprec (fs.get i) (fs.get_mem i))
    (hprec (fs.get j) (fs.get_mem j))
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
  let ⟨_, hprec⟩ := hcommon
  fun i j _ => Compatible.of_commonInterleaver
    (hprec (fs.get i) (fs.get_mem i))
    (hprec (fs.get j) (fs.get_mem j))
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

/-- Natural two-polynomial bridge hypothesis in the Chudnovsky--Seymour setup:
compatibility plus positive leading coefficients implies a common right
interleaver. -/
def CompatiblePairHasCommonInterleaverStatement : Prop :=
  ∀ ⦃f g : ℝ[X]⦄,
    HasPosLeadingCoeff f →
    HasPosLeadingCoeff g →
    Compatible f g →
    ∃ h : ℝ[X], Prec f h ∧ Prec g h

private theorem compatiblePairHasCommonInterleaver_core
    (hbridge : CompatiblePairHasCommonInterleaverStatement)
    {f g : ℝ[X]}
    (hf : HasPosLeadingCoeff f) (hg : HasPosLeadingCoeff g) (h : Compatible f g) :
    ∃ h : ℝ[X], Prec f h ∧ Prec g h :=
  hbridge hf hg h

/-- Two-polynomial common-left bridge, parameterized by the corresponding
positive-leading common-right bridge to avoid an import cycle with the analytic
Chudnovsky--Seymour endpoints. -/
theorem compatiblePairHasCommonLeftInterleaver
    (hbridge : CompatiblePairHasCommonInterleaverStatement)
    {f g : ℝ[X]}
    (hf : HasPosLeadingCoeff f) (hg : HasPosLeadingCoeff g) (h : Compatible f g) :
    ∃ h : ℝ[X], Prec h f ∧ Prec h g := by
  have hclose := h.natDegree_close hf hg
  by_cases hdeg : f.natDegree ≤ g.natDegree
  · obtain ⟨k, hfk, hgk⟩ := compatiblePairHasCommonInterleaver_core hbridge hf hg h
    exact pairHasCommonLeftInterleaver_of_commonInterleaver hfk hgk hdeg hclose.2
  · have hdeg' : g.natDegree ≤ f.natDegree := le_of_not_ge hdeg
    obtain ⟨k, hgk, hfk⟩ :=
      compatiblePairHasCommonInterleaver_core hbridge hg hf h.comm
    obtain ⟨l, hlg, hlf⟩ :=
      pairHasCommonLeftInterleaver_of_commonInterleaver hgk hfk hdeg' hclose.1
    exact ⟨l, hlf, hlg⟩

/-- Positive-leading two-polynomial common-left bridge.  This is the usable
pair-local form for the roadmap theorem, whose finite-family statement already
assumes memberwise positive leading coefficients. -/
def CompatiblePairHasCommonLeftInterleaverPosStatement : Prop :=
  ∀ ⦃f g : ℝ[X]⦄,
    HasPosLeadingCoeff f →
    HasPosLeadingCoeff g →
    Compatible f g →
    ∃ h : ℝ[X], Prec h f ∧ Prec h g

/-- Once the two-polynomial common-left-interleaver converse is available, the
pairwise Chudnovsky--Seymour hypothesis immediately upgrades to pairwise common
left interleavers. This isolates the exact missing bridge. -/
theorem pairwiseHasCommonLeftInterleaver_of_pairwiseCompatible
    (htwo : CompatiblePairHasCommonLeftInterleaverPosStatement)
    {fs : List ℝ[X]}
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hpair : PairwiseCompatible fs) :
    PairwiseHasCommonLeftInterleaver fs :=
  fun i j hij =>
    htwo
      (hpos (fs.get i) (fs.get_mem i))
      (hpos (fs.get j) (fs.get_mem j))
      (hpair i j hij)

/-- Positive-leading version of
`pairwiseHasCommonLeftInterleaver_of_pairwiseCompatible`, using the memberwise
positive-leading hypotheses already present in the finite-family theorem. -/
theorem pairwiseHasCommonLeftInterleaver_of_pairwiseCompatible_pos
    {fs : List ℝ[X]}
    (htwo : CompatiblePairHasCommonLeftInterleaverPosStatement)
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hpair : PairwiseCompatible fs) :
    PairwiseHasCommonLeftInterleaver fs :=
  fun i j hij =>
    htwo
      (hpos (fs.get i) (fs.get_mem i))
      (hpos (fs.get j) (fs.get_mem j))
      (hpair i j hij)

/-- Reduction for the left-oriented Chudnovsky--Seymour target: the full
`PairwiseCompatible ↔ HasCommonLeftInterleaver` statement follows from the
two-polynomial common-left bridge and the finite-family left Helly upgrade. -/
theorem pairwiseCompatible_iff_commonLeftInterleaver_of_pairwiseLeftBridge
    {fs : List ℝ[X]}
    (htwo : CompatiblePairHasCommonLeftInterleaverPosStatement)
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hglobal : PairwiseHasCommonLeftInterleaver fs → HasCommonLeftInterleaver fs) :
    PairwiseCompatible fs ↔ HasCommonLeftInterleaver fs :=
  ⟨fun hpair =>
    hglobal (pairwiseHasCommonLeftInterleaver_of_pairwiseCompatible htwo hpos hpair),
    fun hcommon => pairwiseCompatible_of_commonLeftInterleaver hcommon hpos⟩

/-- Direct left-oriented finite-family reduction after the common-left Helly
upgrade: only the two-polynomial common-left bridge remains as input. -/
theorem pairwiseCompatible_iff_commonLeftInterleaver_of_pairwiseLeftBridge_direct
    {fs : List ℝ[X]}
    (htwo : CompatiblePairHasCommonLeftInterleaverPosStatement)
    (hrr : ∀ f ∈ fs, f.Splits)
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f) :
    PairwiseCompatible fs ↔ HasCommonLeftInterleaver fs :=
  pairwiseCompatible_iff_commonLeftInterleaver_of_pairwiseLeftBridge htwo hpos <|
    hasCommonLeftInterleaver_of_pairwiseHasCommonLeftInterleaver hrr hpos

/-- Direct left-oriented finite-family reduction from the positive-leading
two-polynomial common-left bridge. -/
theorem pairwiseCompatible_iff_commonLeftInterleaver_of_pairwiseLeftBridgePos_direct
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, f.Splits)
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (htwo : CompatiblePairHasCommonLeftInterleaverPosStatement) :
    PairwiseCompatible fs ↔ HasCommonLeftInterleaver fs :=
  ⟨fun hpair =>
    hasCommonLeftInterleaver_of_pairwiseHasCommonLeftInterleaver hrr hpos <|
      pairwiseHasCommonLeftInterleaver_of_pairwiseCompatible_pos htwo hpos hpair,
    fun hcommon => pairwiseCompatible_of_commonLeftInterleaver hcommon hpos⟩

/-- Positive-leading two-polynomial common-right bridge: compatibility implies
a common right interleaver. -/
def CompatiblePairHasCommonRightInterleaverStatement : Prop :=
  ∀ ⦃f g : ℝ[X]⦄,
    HasPosLeadingCoeff f →
    HasPosLeadingCoeff g →
    Compatible f g →
    ∃ h : ℝ[X], Prec f h ∧ Prec g h

/-- Natural two-polynomial bridge: compatibility plus positive leading
coefficients implies a common right interleaver. -/
theorem compatiblePairHasCommonInterleaver
    (hbridge : CompatiblePairHasCommonInterleaverStatement)
    {f g : ℝ[X]}
    (hf : HasPosLeadingCoeff f) (hg : HasPosLeadingCoeff g) (h : Compatible f g) :
    ∃ h : ℝ[X], Prec f h ∧ Prec g h :=
  compatiblePairHasCommonInterleaver_core hbridge hf hg h

/-- Once the two-polynomial common-right-interleaver converse is available, the
pairwise Chudnovsky--Seymour hypothesis upgrades to pairwise common right
interleavers. -/
theorem pairwiseHasCommonInterleaver_of_pairwiseCompatible
    {fs : List ℝ[X]}
    (htwo : CompatiblePairHasCommonRightInterleaverStatement)
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hpair : PairwiseCompatible fs) :
    PairwiseHasCommonInterleaver fs :=
  fun i j hij =>
    htwo
      (hpos (fs.get i) (fs.get_mem i))
      (hpos (fs.get j) (fs.get_mem j))
      (hpair i j hij)

/-- Same-degree branch of the positive-leading compatibility bridge. This is
the honest `Compatible`-level version of article 3.6.1 → 3.6.2 in the equal-
degree case. -/
def CompatibleSameDegreePairHasCommonInterleaverStatement : Prop :=
  ∀ ⦃f g : ℝ[X]⦄,
    HasPosLeadingCoeff f →
    HasPosLeadingCoeff g →
    Compatible f g →
    g.natDegree = f.natDegree →
    ∃ h : ℝ[X], Prec f h ∧ Prec g h

/-- Succ-degree branch of the positive-leading compatibility bridge. Since
`Compatible.natDegree_close` already rules out larger degree gaps, this and
the same-degree branch are the only genuinely remaining cases. -/
def CompatibleSuccDegreePairHasCommonInterleaverStatement : Prop :=
  ∀ ⦃f g : ℝ[X]⦄,
    HasPosLeadingCoeff f →
    HasPosLeadingCoeff g →
    Compatible f g →
    g.natDegree = f.natDegree + 1 →
    ∃ h : ℝ[X], Prec f h ∧ Prec g h

/-- Since `Compatible.natDegree_close` limits the degree gap to at most one,
the full positive-leading compatibility bridge reduces to the same-degree and
succ-degree cases, together with symmetry. -/
theorem compatiblePairHasCommonInterleaver_of_degreeSplit
    (hsame : CompatibleSameDegreePairHasCommonInterleaverStatement)
    (hsucc : CompatibleSuccDegreePairHasCommonInterleaverStatement) :
    CompatiblePairHasCommonInterleaverStatement := by
  intro f g hf hg hfg
  have : f.natDegree ≤ g.natDegree + 1 ∧ g.natDegree ≤ f.natDegree + 1 :=
    hfg.natDegree_close hf hg
  by_cases hdeg : f.natDegree ≤ g.natDegree
  · rcases (by lia : g.natDegree = f.natDegree ∨
      g.natDegree = f.natDegree + 1) with hsame_deg | hsucc_deg
    · exact hsame hf hg hfg hsame_deg
    · exact hsucc hf hg hfg hsucc_deg
  · have : g.natDegree ≤ f.natDegree := le_of_not_ge hdeg
    rcases (by lia : f.natDegree = g.natDegree ∨
      f.natDegree = g.natDegree + 1) with hsame_deg | hsucc_deg
    · lia
    · exact (hsucc hg hf hfg.comm hsucc_deg).imp fun _ h => h.symm

/-- A positive-leading common-right bridge implies the corresponding common-left
bridge: first get a common right interleaver, then convert it to a common left
interleaver using degree closeness. -/
theorem compatiblePairHasCommonLeftInterleaverPos_of_pairBridge
    (hright : CompatiblePairHasCommonInterleaverStatement) :
    CompatiblePairHasCommonLeftInterleaverPosStatement := by
  intro f g hf hg hfg
  have : f.natDegree ≤ g.natDegree + 1 ∧ g.natDegree ≤ f.natDegree + 1 :=
    hfg.natDegree_close hf hg
  by_cases hdeg : f.natDegree ≤ g.natDegree
  · rcases hright hf hg hfg with ⟨h, hfh, hgh⟩
    exact
      pairHasCommonLeftInterleaver_of_commonInterleaver
        hfh hgh hdeg this.2
  · rcases hright hg hf hfg.comm with ⟨h, hgh, hfh⟩
    exact (pairHasCommonLeftInterleaver_of_commonInterleaver
      hgh hfh (le_of_not_ge hdeg) this.1).imp fun _ h => h.symm

end RealRooted
