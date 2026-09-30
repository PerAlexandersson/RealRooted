import RealRooted.CommonInterleaver.PairBridge.Reduction.AllCombo
import RealRooted.CommonInterleaver.PairBridge.Reduction.CommonInterleaver

/-!
# Pair bridge assembly: compatibility endpoints

Final pairwise and compatibility-to-common-interleaver wrappers.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- Reduction of no-common orientation to the all-combinations bridge plus
Obreschkoff converse (`strictInterl_of_allComboRealRooted`). -/
theorem posComboNoCommonOrientation_of_allComboBridge
    (hallBridge : PosComboNoCommonToAllComboBridgeStatement) :
    PosComboNoCommonOrientationStatement := by
  intro f g hfg hf_pos hg_pos hdeg_lo hdeg_hi hno
  have hall : AllComboRealRooted f g :=
    hallBridge hf_pos hg_pos hfg hdeg_lo hdeg_hi hno
  exact
    CommonInterleaver.PairBridge.strictInterl_or_reverse_of_allComboRealRooted_ordered
      hf_pos hg_pos hall hdeg_lo hdeg_hi

/-- Compatibility-to-common-interleaver reduction through the positive-combo
bridge. -/
theorem compatiblePairHasCommonInterleaver_of_posComboPair
    (hposCombo : PosComboPairHasCommonInterleaverStatement) :
    CompatiblePairHasCommonInterleaverStatement :=
  fun {_ _} hf_pos hg_pos hfg =>
    hposCombo hf_pos hg_pos
      (hfg.toPosComboRealRooted hf_pos hg_pos)

/-- If one has both the no-common-roots orientation core and degree closeness
for the current `PosComboRealRooted` pair, then the pair has a common right
interleaver. -/
theorem posComboPairHasCommonInterleaver_of_noCommonOrientation_and_degreeBounds
    (hstep : PosComboNoCommonOrientationStatement)
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfg : PosComboRealRooted f g)
    (hclose :
      f.natDegree ≤ g.natDegree + 1 ∧
        g.natDegree ≤ f.natDegree + 1) :
    ∃ h : ℝ[X], StrictInterl f h ∧ StrictInterl g h := by
  by_cases hfg_deg : f.natDegree ≤ g.natDegree
  · have hstrictInterl_or : StrictInterl f g ∨ StrictInterl g f :=
      PosComboRealRooted.strictInterl_or_reverse_of_posComboRealRooted_of_no_common
        (hstep := fun hfg hf_pos hg_pos hdeg_lo hdeg_hi hno =>
          hstep hfg hf_pos hg_pos hdeg_lo hdeg_hi hno)
        hfg hf_pos hg_pos hfg_deg hclose.2
    exact pairHasCommonInterleaver_of_strictInterl_or_reverse hstrictInterl_or
  · have hgf_deg : g.natDegree ≤ f.natDegree := le_of_not_ge hfg_deg
    have hstrictInterl_or : StrictInterl g f ∨ StrictInterl f g :=
      PosComboRealRooted.strictInterl_or_reverse_of_posComboRealRooted_of_no_common
        (hstep := fun hfg hf_pos hg_pos hdeg_lo hdeg_hi hno =>
          hstep hfg hf_pos hg_pos hdeg_lo hdeg_hi hno)
        (PosComboRealRooted.comm hfg) hg_pos hf_pos hgf_deg hclose.1
    exact pairHasCommonInterleaver_of_strictInterl_or_reverse (Or.symm hstrictInterl_or)

/-- If one has both the no-common-roots orientation core and degree closeness
for `PosComboRealRooted` pairs, then every positive-leading `PosComboRealRooted`
pair has a common right interleaver. -/
theorem posComboPairHasCommonInterleaver_of_noCommonOrientation_and_degreeClose
    (hstep : PosComboNoCommonOrientationStatement)
    (hdegClose : PosComboNatDegreeCloseStatement) :
    PosComboPairHasCommonInterleaverStatement :=
  fun _ _ hf_pos hg_pos hfg =>
    posComboPairHasCommonInterleaver_of_noCommonOrientation_and_degreeBounds
      hstep hf_pos hg_pos hfg (hdegClose hfg)

/-- Degree-closeness specialization with nonnegative coefficients. -/
theorem posComboNatDegreeClose_of_nonnegCoeffs
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f) (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g) :
    f.natDegree ≤ g.natDegree + 1 ∧
      g.natDegree ≤ f.natDegree + 1 :=
  natDegree_close_of_posComboRealRooted_of_nonnegCoeffs
    hfg (hf_pos.ne_zero)
    (hg_pos.ne_zero) hfnn hgnn

/-- In the nonnegative-coefficient regime, the no-common-roots orientation
core already implies the full positive-combo pair bridge. -/
theorem posComboPairHasCommonInterleaver_of_noCommonOrientation_and_nonnegCoeffs
    (hstep : PosComboNoCommonOrientationStatement)
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f) (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g) :
    ∃ h : ℝ[X], StrictInterl f h ∧ StrictInterl g h :=
  posComboPairHasCommonInterleaver_of_noCommonOrientation_and_degreeBounds
    hstep hf_pos hg_pos hfg
    (posComboNatDegreeClose_of_nonnegCoeffs hf_pos hg_pos hfnn hgnn hfg)

/-- In the nonnegative-coefficient regime, the affine-family bridge already
implies the full positive-combo pair bridge. -/
theorem posComboPairHasCommonInterleaver_of_affineFamilyBridge_and_nonnegCoeffs
    (haffBridge : PosComboNoCommonAffineFamilyStatement)
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f) (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g) :
    ∃ h : ℝ[X], StrictInterl f h ∧ StrictInterl g h :=
  pairHasCommonInterleaver_of_strictInterl_or_reverse <|
    posComboOrientation_of_affineFamilyBridge_and_nonnegCoeffs
      haffBridge hf_pos hg_pos hfnn hgnn hfg

/-- An ordered positive-combo pair bridge plus the nonnegative degree-closeness
theorem gives the unordered pair bridge. -/
theorem posComboPairHasCommonInterleaver_of_orderedBridge_and_nonnegCoeffs
    (hordered :
      ∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        f.natDegree ≤ g.natDegree →
        g.natDegree ≤ f.natDegree + 1 →
        ∃ h : ℝ[X], StrictInterl f h ∧ StrictInterl g h)
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f) (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g) :
    ∃ h : ℝ[X], StrictInterl f h ∧ StrictInterl g h := by
  have hf0 : f ≠ 0 := hf_pos.ne_zero
  have hg0 : g ≠ 0 := hg_pos.ne_zero
  have hclose :
      f.natDegree ≤ g.natDegree + 1 ∧
        g.natDegree ≤ f.natDegree + 1 :=
    natDegree_close_of_posComboRealRooted_of_nonnegCoeffs
      hfg hf0 hg0 hfnn hgnn
  by_cases hdeg : f.natDegree ≤ g.natDegree
  · exact hordered hf_pos hg_pos hfnn hgnn hfg hdeg hclose.2
  · have hdeg' : g.natDegree ≤ f.natDegree := le_of_not_ge hdeg
    rcases
        hordered hg_pos hf_pos hgnn hfnn (PosComboRealRooted.comm hfg) hdeg' hclose.1 with
      ⟨h, hg_strictInterl, hf_strictInterl⟩
    exact ⟨h, hf_strictInterl, hg_strictInterl⟩

/-- Repaired degree-split package for the full positive-combo pair bridge in
the nonnegative-coefficient regime. This is the version to use after the
same-degree orientation alternative is replaced by a common-interleaver target.
-/
theorem posComboPairHasCommonInterleaver_of_pairDegreeSplit_and_nonnegCoeffs
    (hsame : PosComboNoCommonSameDegreePairHasCommonInterleaverNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement)
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f) (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g) :
    ∃ h : ℝ[X], StrictInterl f h ∧ StrictInterl g h :=
  posComboPairHasCommonInterleaver_of_orderedBridge_and_nonnegCoeffs
    (fun {f g} hf_pos hg_pos hfnn hgnn hfg hdeg_lo hdeg_hi =>
      CommonInterleaver.PairBridge.pairDegreeSplit_ordered
        (f := f) (g := g) hsame hsucc hf_pos hg_pos hfnn hgnn hfg hdeg_lo hdeg_hi)
    hf_pos hg_pos hfnn hgnn hfg

private theorem compatiblePairHasCommonInterleaver_of_nonnegPosComboPairBridge
    (hbridge :
      ∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        ∃ h : ℝ[X], StrictInterl f h ∧ StrictInterl g h)
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f) (hgnn : HasNonnegCoeffs g)
    (hfg : Compatible f g) :
    ∃ h : ℝ[X], StrictInterl f h ∧ StrictInterl g h :=
  hbridge hf_pos hg_pos hfnn hgnn
    (hfg.toPosComboRealRooted hf_pos hg_pos)

private theorem nonnegPosComboPairBridge_of_noCommonOrientation
    (hstep : PosComboNoCommonOrientationStatement) :
    ∀ ⦃f g : ℝ[X]⦄,
      HasPosLeadingCoeff f →
      HasPosLeadingCoeff g →
      HasNonnegCoeffs f →
      HasNonnegCoeffs g →
      PosComboRealRooted f g →
      ∃ h : ℝ[X], StrictInterl f h ∧ StrictInterl g h :=
  fun {_ _} hf_pos hg_pos hfnn hgnn hfg =>
    posComboPairHasCommonInterleaver_of_noCommonOrientation_and_nonnegCoeffs
      hstep hf_pos hg_pos hfnn hgnn hfg

private theorem nonnegPosComboPairBridge_of_affineFamilyBridge
    (haffBridge : PosComboNoCommonAffineFamilyStatement) :
    ∀ ⦃f g : ℝ[X]⦄,
      HasPosLeadingCoeff f →
      HasPosLeadingCoeff g →
      HasNonnegCoeffs f →
      HasNonnegCoeffs g →
      PosComboRealRooted f g →
      ∃ h : ℝ[X], StrictInterl f h ∧ StrictInterl g h :=
  fun {_ _} hf_pos hg_pos hfnn hgnn hfg =>
    posComboPairHasCommonInterleaver_of_affineFamilyBridge_and_nonnegCoeffs
      haffBridge hf_pos hg_pos hfnn hgnn hfg

private theorem nonnegPosComboPairBridge_of_pairDegreeSplit
    (hsame : PosComboNoCommonSameDegreePairHasCommonInterleaverNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement) :
    ∀ ⦃f g : ℝ[X]⦄,
      HasPosLeadingCoeff f →
      HasPosLeadingCoeff g →
      HasNonnegCoeffs f →
      HasNonnegCoeffs g →
      PosComboRealRooted f g →
      ∃ h : ℝ[X], StrictInterl f h ∧ StrictInterl g h :=
  fun {_ _} hf_pos hg_pos hfnn hgnn hfg =>
    posComboPairHasCommonInterleaver_of_pairDegreeSplit_and_nonnegCoeffs
      hsame hsucc hf_pos hg_pos hfnn hgnn hfg

/-- Compatibility-to-common-interleaver bridge under no-common orientation and
nonnegative coefficients. -/
theorem compatiblePairHasCommonInterleaver_of_noCommonOrientation_and_nonnegCoeffs
    (hstep : PosComboNoCommonOrientationStatement)
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f) (hgnn : HasNonnegCoeffs g)
    (hfg : Compatible f g) :
    ∃ h : ℝ[X], StrictInterl f h ∧ StrictInterl g h :=
  compatiblePairHasCommonInterleaver_of_nonnegPosComboPairBridge
    (nonnegPosComboPairBridge_of_noCommonOrientation hstep)
    hf_pos hg_pos hfnn hgnn hfg

/-- Compatibility bridge under nonnegative coefficients, reduced to the
affine-family bridge. -/
theorem compatiblePairHasCommonInterleaver_of_affineFamilyBridge_and_nonnegCoeffs
    (haffBridge : PosComboNoCommonAffineFamilyStatement)
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f) (hgnn : HasNonnegCoeffs g)
    (hfg : Compatible f g) :
    ∃ h : ℝ[X], StrictInterl f h ∧ StrictInterl g h :=
  compatiblePairHasCommonInterleaver_of_nonnegPosComboPairBridge
    (nonnegPosComboPairBridge_of_affineFamilyBridge haffBridge)
    hf_pos hg_pos hfnn hgnn hfg

/-- Compatibility bridge under nonnegative coefficients, reduced to the
repaired degree-split package with common-interleaver conclusions in both
branches. -/
theorem compatiblePairHasCommonInterleaver_of_pairDegreeSplit_and_nonnegCoeffs
    (hsame : PosComboNoCommonSameDegreePairHasCommonInterleaverNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement)
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f) (hgnn : HasNonnegCoeffs g)
    (hfg : Compatible f g) :
    ∃ h : ℝ[X], StrictInterl f h ∧ StrictInterl g h :=
  compatiblePairHasCommonInterleaver_of_nonnegPosComboPairBridge
    (nonnegPosComboPairBridge_of_pairDegreeSplit hsame hsucc)
    hf_pos hg_pos hfnn hgnn hfg

end RealRooted
