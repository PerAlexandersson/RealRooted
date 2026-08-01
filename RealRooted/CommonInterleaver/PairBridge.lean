/-
# Pair bridge assembly for two-polynomial common interleavers

This module contains the two-polynomial bridge assembly extracted from
`CommonInterleaverTwo`: common-root reductions, nonnegative-coefficient and
translation reductions, and compatibility-to-common-interleaver endpoints.
-/
import RealRooted.Compatibility.InterleaverBridge
import RealRooted.CommonInterleaver.AffineBoundary
import RealRooted.CommonInterleaver.SuccDegreeEndpoint
import RealRooted.CommonInterleaver.RootCountCombinatorics
import RealRooted.CommonInterleaver.RightPencil
import RealRooted.CommonInterleaver.SuccDegreeLowDegree
import RealRooted.CommonInterleaver.IntervalLemmas
import RealRooted.CommonInterleaver.SameDegreeRootCount
import RealRooted.CommonInterleaver.Statements
import RealRooted.PosCombo
import RealRooted.CommonInterleaverSeq
import RealRooted.AffineFamily
import RealRooted.DegreeDropDivXPrec
import RealRooted.DegreeDropReversal
import RealRooted.GammaRealRoots
import RealRooted.PFPolynomial
import RealRooted.RootOrderBridge
import RealRooted.RootCountJump
import RealRooted.RootContinuity
import RealRooted.SameDegreeCubicRootCount
import RealRooted.SameDegreeQuadraticRootCount
import RealRooted.SuccDegreeRootCrossing
import RealRooted.SuccDegreeLeftEndpoint

open Polynomial

noncomputable section

namespace RealRooted

private lemma nonneg_of_add_mul_pos_forall {a b : ℝ}
    (h : ∀ {μ : ℝ}, 0 < μ → 0 ≤ a + μ * b) :
    0 ≤ a := by
  by_contra ha
  have ha_lt : a < 0 := lt_of_not_ge ha
  by_cases hb : b ≤ 0
  · have hbad : a + (1 : ℝ) * b < 0 := by
      nlinarith
    exact not_lt_of_ge (h zero_lt_one) hbad
  · have hb_pos : 0 < b := lt_of_not_ge hb
    let μ : ℝ := -a / (2 * b)
    have hμ_pos : 0 < μ := by
      unfold μ
      simp_all
    have hμ_ge : 0 ≤ a + μ * b := h hμ_pos
    have hμ_bad : a + μ * b < 0 := by
      unfold μ
      have hb_ne : b ≠ 0 := ne_of_gt hb_pos
      field_simp [hb_ne]
      nlinarith
    grind

private lemma coeff_nonneg_of_add_C_mul_nonneg_forall
    {f g : ℝ[X]}
    (h : ∀ {μ : ℝ}, 0 < μ → HasNonnegCoeffs (f + C μ * g)) :
    HasNonnegCoeffs f := by
  intro n
  refine nonneg_of_add_mul_pos_forall
    (a := f.coeff n) (b := g.coeff n) ?_
  intro μ hμ
  have hμnn : HasNonnegCoeffs (f + C μ * g) := h hμ
  simpa [Polynomial.coeff_add, Polynomial.coeff_C_mul] using hμnn n

/-- The corrected shifted-pair same-degree hypothesis already implies the
original same-degree orientation statement in the nonnegative regime, via the
public shifted-pair subtraction theorem from `AffineFamily`. -/
theorem posComboNoCommonSameDegreeOrientation_of_shiftedPairOrientation_and_nonnegCoeffs
    (hshift : PosComboNoCommonSameDegreeShiftedPairOrientationStatement) :
    PosComboNoCommonSameDegreeOrientationNonnegStatement := by
  intro f g hf_pos hg_pos hfnn hgnn hfg hdeg hno
  have hf0 : f ≠ 0 := hf_pos.ne_zero
  have hg0 : g ≠ 0 := hg_pos.ne_zero
  exact
    prec_of_prec_shifted_pair_sameDegree_nonneg
      (hshift hf_pos hg_pos hfnn hgnn hfg hdeg hno)
      hf0 hg0 hfnn hgnn hdeg

/-- Consequently, the corrected shifted-pair same-degree hypothesis already
gives the same-degree all-combinations bridge in the nonnegative regime. -/
theorem allComboRealRooted_of_sameDegreeShiftedPairOrientation_and_nonnegCoeffs
    (hshift : PosComboNoCommonSameDegreeShiftedPairOrientationStatement)
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g)
    (hdeg : g.natDegree = f.natDegree)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    AllComboRealRooted f g :=
  allComboRealRooted_of_prec
    ((posComboNoCommonSameDegreeOrientation_of_shiftedPairOrientation_and_nonnegCoeffs
        hshift) hf_pos hg_pos hfnn hgnn hfg hdeg hno)

/-- Forward orientation of the right-family pair `(f + g, f + 2g)` already
forces the sum `f + g` to interlace `g` on the left in the high-degree
same-degree nonnegative branch. This is the first concrete transport step
behind the right-family reroute. -/
theorem prec_sum_left_of_prec_right_family_forward_sameDegree_nonneg
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfg : PosComboRealRooted f g)
    (hdeg : g.natDegree = f.natDegree)
    (hdeg_pos : 1 ≤ g.natDegree)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hpair : Prec (f + g) (f + C (2 : ℝ) * g)) :
    Prec (f + g) g := by
  let F : ℝ[X] := f + g
  let G : ℝ[X] := f + C (2 : ℝ) * g
  rcases
      PosComboRealRooted.family_pair_data_right_one_two
        (f := f) (g := g) hfg (by lia) hf_pos hg_pos hno with
    ⟨_, hF_pos, hG_pos, hF_deg, hG_deg, _⟩
  have hF_deg' : F.natDegree = g.natDegree := by grind
  have hno_FG : ∀ r, F.IsRoot r → ¬ G.IsRoot r := by
    simpa [F, G] using
      PosComboRealRooted.no_common_root_right_family_one_two_of_no_common
        (f := f) (g := g) hno
  have hFG_deg : F.natDegree = G.natDegree := by lia
  have hG_deg_pos : 1 ≤ G.natDegree := by lia
  obtain ⟨uR, q, hGq, huR_root, huR_max, hqF⟩ :=
    exists_rightmost_factor_interlaces_of_prec_sameDegree
      (f := F) (g := G) hpair hFG_deg hG_deg_pos
  have hq_pos : HasPosLeadingCoeff q :=
    hasPosLeadingCoeff_of_X_sub_C_mul (by simpa [G, hGq] using hG_pos)
  have hFq_no : ∀ r, F.IsRoot r → ¬ q.IsRoot r := by simp_all
  have hroot_lt : ∀ r, F.IsRoot r → r < uR := by
    intro r hFr
    have hr_le : r ≤ uR :=
      roots_le_of_prec_right hpair huR_max r ((mem_roots hpair.1.1).mpr hFr)
    grind
  have htarget_eq : C (-1 : ℝ) * F + (X - C uR) * q = g := by
    dsimp [F, G] at hGq ⊢
    calc
      C (-1 : ℝ) * (f + g) + (X - C uR) * q
          = C (-1 : ℝ) * (f + g) + (f + C (2 : ℝ) * g) := by
              lia
      _ = g := by
            ext n
            simp [Polynomial.coeff_C_mul]
            ring
  have htarget_eq' : -F + (X - C uR) * q = g := by simp_all
  have hprec :
      Prec F (C (-1 : ℝ) * F + (X - C uR) * q) :=
    prec_of_interlaces_evalCoeff_neg_same
      (f := F) (g := q) (a := C (-1 : ℝ)) (b := X - C uR)
      hqF hq_pos
      (by lia)
      (by lia)
      hFq_no
      (by simp_all)
  lia

/-- Swapping the roles of `f` and `g` gives the symmetric forward transport for
the left-family pair `(f + g, 2f + g)`. -/
theorem prec_sum_left_of_prec_left_family_forward_sameDegree_nonneg
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfg : PosComboRealRooted f g)
    (hdeg : g.natDegree = f.natDegree)
    (hdeg_pos : 1 ≤ g.natDegree)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hpair : Prec (f + g) (C (2 : ℝ) * f + g)) :
    Prec (f + g) f := by
  have hno_swap : ∀ r, g.IsRoot r → ¬ f.IsRoot r := by grind
  have hf_deg_pos : 1 ≤ f.natDegree := by lia
  simpa [add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc] using
    prec_sum_left_of_prec_right_family_forward_sameDegree_nonneg
      (f := g) (g := f)
      hg_pos hf_pos (PosComboRealRooted.comm hfg) hdeg.symm hf_deg_pos
      hno_swap
      (by simpa [add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc]
        using hpair)

/-- If both specialized one-step families point forward, then their common
middle sum `f + g` is already a common left interleaver for `f` and `g`. This
makes the purpose of the `f + g`, `f + 2g`, `2f + g` reroutes explicit. -/
theorem pairHasCommonLeftInterleaver_of_forward_oneTwoFamilies_sameDegree_nonneg
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfg : PosComboRealRooted f g)
    (hdeg : g.natDegree = f.natDegree)
    (hdeg_pos : 1 ≤ g.natDegree)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hright : Prec (f + g) (f + C (2 : ℝ) * g))
    (hleft : Prec (f + g) (C (2 : ℝ) * f + g)) :
    ∃ h : ℝ[X], Prec h f ∧ Prec h g := by
  refine ⟨f + g, ?_, ?_⟩
  · exact
      prec_sum_left_of_prec_left_family_forward_sameDegree_nonneg
        hf_pos hg_pos hfg hdeg hdeg_pos hno hleft
  · exact
      prec_sum_left_of_prec_right_family_forward_sameDegree_nonneg
        hf_pos hg_pos hfg hdeg hdeg_pos hno hright

/-- The same forward one-two-family hypotheses already force the original pair
to be compatible: the common left interleaver `f + g` witnesses all
nonnegative combinations. -/
theorem compatible_of_forward_oneTwoFamilies_sameDegree_nonneg
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfg : PosComboRealRooted f g)
    (hdeg : g.natDegree = f.natDegree)
    (hdeg_pos : 1 ≤ g.natDegree)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hright : Prec (f + g) (f + C (2 : ℝ) * g))
    (hleft : Prec (f + g) (C (2 : ℝ) * f + g)) :
    Compatible f g := by
  obtain ⟨h, hhf, hhg⟩ :=
    pairHasCommonLeftInterleaver_of_forward_oneTwoFamilies_sameDegree_nonneg
      hf_pos hg_pos hfg hdeg hdeg_pos hno hright hleft
  exact Compatible.of_commonLeftInterleaver hhf hhg hf_pos hg_pos

/-- Consequently, any generic two-polynomial compatibility bridge can consume
the forward one-two-family hypotheses directly. -/
theorem pairHasCommonInterleaver_of_forward_oneTwoFamilies_sameDegree_nonneg
    (htwo : CompatiblePairHasCommonInterleaverStatement)
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfg : PosComboRealRooted f g)
    (hdeg : g.natDegree = f.natDegree)
    (hdeg_pos : 1 ≤ g.natDegree)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hright : Prec (f + g) (f + C (2 : ℝ) * g))
    (hleft : Prec (f + g) (C (2 : ℝ) * f + g)) :
    ∃ h : ℝ[X], Prec f h ∧ Prec g h :=
  htwo hf_pos hg_pos
    (compatible_of_forward_oneTwoFamilies_sameDegree_nonneg
      hf_pos hg_pos hfg hdeg hdeg_pos hno hright hleft)

/-- Any no-common orientation core already contains the honest same-degree
branch in the nonnegative regime: one simply specializes the degree bounds to
equality. -/
theorem posComboNoCommonSameDegreeOrientationAlternative_of_noCommonOrientation
    (hstep : PosComboNoCommonOrientationStatement) :
    PosComboNoCommonSameDegreeOrientationAlternativeNonnegStatement :=
  fun {_ _} hf_pos hg_pos _ _ hfg hdeg hno =>
    hstep hfg hf_pos hg_pos (by lia) (by lia) hno

/-- In the succ-degree branch, any no-common orientation core automatically
forces the forward orientation by degree, so it also packages the honest
succ-degree orientation statement. -/
theorem posComboNoCommonSuccDegreeOrientation_of_noCommonOrientation
    (hstep : PosComboNoCommonOrientationStatement) :
    PosComboNoCommonSuccDegreeOrientationNonnegStatement :=
  fun {_ _} hf_pos hg_pos _ _ hfg hsucc hno =>
    prec_forward_of_orientation_of_succDegree hsucc <|
      hstep hfg hf_pos hg_pos (by lia) (by lia) hno

/-- Consequently, any proof of the older no-common orientation core can be fed
directly into the corrected succ-degree common-interleaver bridge. -/
theorem posComboNoCommonSuccDegreePairHasCommonInterleaver_of_noCommonOrientation
    (hstep : PosComboNoCommonOrientationStatement) :
    PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement :=
  posComboNoCommonSuccDegreePairHasCommonInterleaver_of_orientation_nonneg
    (posComboNoCommonSuccDegreeOrientation_of_noCommonOrientation hstep)

/-- Common-left-interleaver formulation of the succ-degree no-common
root-count target.  This isolates the Obreschkoff-converse content needed for
the honest common-non-root leaf. -/
def PosComboNoCommonSuccDegreeCommonLeftInterleaverNonnegStatement : Prop :=
  ∀ ⦃f g : ℝ[X]⦄,
    HasPosLeadingCoeff f →
    HasPosLeadingCoeff g →
    HasNonnegCoeffs f →
    HasNonnegCoeffs g →
    PosComboRealRooted f g →
    g.natDegree = f.natDegree + 1 →
    (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
    f.Splits →
    ∃ h : ℝ[X], Prec h f ∧ Prec h g

/-- The fixed-orientation succ-degree endpoint supplies the common-left
interleaver formulation by using `f` as the witness. -/
theorem posComboNoCommonSuccDegreeCommonLeftInterleaver_of_orientation
    (horient : PosComboNoCommonSuccDegreeOrientationNonnegStatement) :
    PosComboNoCommonSuccDegreeCommonLeftInterleaverNonnegStatement := by
  intro f g hf_pos hg_pos hfnn hgnn hfg hdeg hno _hf_split
  exact pairHasCommonLeftInterleaver_of_prec <|
    horient hf_pos hg_pos hfnn hgnn hfg hdeg hno

/-- A common left interleaver gives the lower common-non-root succ-degree
root-count target.  The degrees force the left interleaver to have the same
degree as `f`, so the same-degree and tight succ-degree oriented count bounds
combine directly. -/
theorem posComboNoCommonSuccDegreeRootCountNonRoot_of_commonLeftInterleaver
    (hleft : PosComboNoCommonSuccDegreeCommonLeftInterleaverNonnegStatement) :
    PosComboNoCommonSuccDegreeRootCountNonRootNonnegStatement := by
  intro f g hf_pos hg_pos hfnn hgnn hfg hdeg hno hf_split x _hxf _hxg
  obtain ⟨h, hhf, hhg⟩ :=
    hleft hf_pos hg_pos hfnn hgnn hfg hdeg hno hf_split
  have hhf_le := hhf.natDegree_le
  have hhg_le_succ := hhg.natDegree_le_succ
  have hdh : f.natDegree = h.natDegree := by lia
  have hdg : g.natDegree = h.natDegree + 1 := by lia
  obtain ⟨hA1, hA2⟩ := sameDegreeRootCountOriented_of_prec hhf hdh x
  obtain ⟨hB1, hB2⟩ := succDegreeRootCountLowerOriented_of_prec hhg hdg x
  exact ⟨by lia, by lia⟩

/-- The honest common-non-root upper-count succ-degree leaf, reduced to the
common-left-interleaver formulation. -/
theorem posComboNoCommonSuccDegreeRootCountAboveNonRoot_of_commonLeftInterleaver
    (hleft : PosComboNoCommonSuccDegreeCommonLeftInterleaverNonnegStatement) :
    PosComboNoCommonSuccDegreeRootCountAboveNonRootNonnegStatement :=
  posComboNoCommonSuccDegreeRootCountAboveNonRoot_iff_rootCountNonRoot.mpr
    (posComboNoCommonSuccDegreeRootCountNonRoot_of_commonLeftInterleaver hleft)

/-- The succ-degree root-count formulation implies the descending-root
crossing formulation. -/
theorem posComboNoCommonSuccDegreeRootCrossing_of_rootCount
    (hcount : PosComboNoCommonSuccDegreeRootCountNonnegStatement) :
    PosComboNoCommonSuccDegreeRootCrossingNonnegStatement := by
  intro f g hf_pos hg_pos hfnn hgnn hfg hdeg hno hf_split
  have hg_split : g.Splits :=
    (hfg.isRealRooted_right_of_succDegree hf_pos hg_pos hdeg).2
  exact succDegreeRootCrossing_of_rootCount hf_split hg_split hdeg
    (hcount hf_pos hg_pos hfnn hgnn hfg hdeg hno hf_split)

/-- The upper-threshold succ-degree root-count formulation implies the
descending-root crossing formulation. -/
theorem posComboNoCommonSuccDegreeRootCrossing_of_rootCountAbove
    (hcount : PosComboNoCommonSuccDegreeRootCountAboveNonnegStatement) :
    PosComboNoCommonSuccDegreeRootCrossingNonnegStatement := by
  intro f g hf_pos hg_pos hfnn hgnn hfg hdeg hno hf_split
  have hg_split : g.Splits :=
    (hfg.isRealRooted_right_of_succDegree hf_pos hg_pos hdeg).2
  exact succDegreeRootCrossing_of_rootCountAbove hf_split hg_split hdeg
    (hcount hf_pos hg_pos hfnn hgnn hfg hdeg hno hf_split)

/-- The upper-threshold root-count target implies the lower-threshold
root-count target. -/
theorem posComboNoCommonSuccDegreeRootCount_of_rootCountAbove
    (hcount : PosComboNoCommonSuccDegreeRootCountAboveNonnegStatement) :
    PosComboNoCommonSuccDegreeRootCountNonnegStatement := by
  intro f g hf_pos hg_pos hfnn hgnn hfg hdeg hno hf_split
  have hg_split : g.Splits :=
    (hfg.isRealRooted_right_of_succDegree hf_pos hg_pos hdeg).2
  exact succDegreeRootCount_of_rootCountAbove hf_split hg_split hdeg
    (hcount hf_pos hg_pos hfnn hgnn hfg hdeg hno hf_split)

/-- The lower-threshold root-count target implies the upper-threshold
root-count target. -/
theorem posComboNoCommonSuccDegreeRootCountAbove_of_rootCount
    (hcount : PosComboNoCommonSuccDegreeRootCountNonnegStatement) :
    PosComboNoCommonSuccDegreeRootCountAboveNonnegStatement := by
  intro f g hf_pos hg_pos hfnn hgnn hfg hdeg hno hf_split
  have hg_split : g.Splits :=
    (hfg.isRealRooted_right_of_succDegree hf_pos hg_pos hdeg).2
  exact succDegreeRootCountAbove_of_rootCount hf_split hg_split hdeg
    (hcount hf_pos hg_pos hfnn hgnn hfg hdeg hno hf_split)

/-- The lower- and upper-threshold succ-degree root-count targets are
equivalent. -/
theorem posComboNoCommonSuccDegreeRootCountAbove_iff_rootCount :
    PosComboNoCommonSuccDegreeRootCountAboveNonnegStatement ↔
      PosComboNoCommonSuccDegreeRootCountNonnegStatement :=
  ⟨posComboNoCommonSuccDegreeRootCount_of_rootCountAbove,
    posComboNoCommonSuccDegreeRootCountAbove_of_rootCount⟩

/-- The lower-threshold succ-degree root-count target follows from the
common-non-root upper-threshold variant. -/
theorem posComboNoCommonSuccDegreeRootCount_of_nonRoot
    (hcount : PosComboNoCommonSuccDegreeRootCountAboveNonRootNonnegStatement) :
    PosComboNoCommonSuccDegreeRootCountNonnegStatement :=
  posComboNoCommonSuccDegreeRootCount_of_rootCountAbove
    (posComboNoCommonSuccDegreeRootCountAbove_of_nonRoot hcount)

/-- The lower-threshold succ-degree root-count target follows from the lower
common-non-root formulation. -/
theorem posComboNoCommonSuccDegreeRootCount_of_rootCountNonRoot
    (hcount : PosComboNoCommonSuccDegreeRootCountNonRootNonnegStatement) :
    PosComboNoCommonSuccDegreeRootCountNonnegStatement :=
  posComboNoCommonSuccDegreeRootCount_of_rootCountAbove
    (posComboNoCommonSuccDegreeRootCountAbove_of_rootCountNonRoot hcount)

/-- The succ-degree root-crossing target follows from the lower
common-non-root root-count formulation. -/
theorem posComboNoCommonSuccDegreeRootCrossing_of_rootCountNonRoot
    (hcount : PosComboNoCommonSuccDegreeRootCountNonRootNonnegStatement) :
    PosComboNoCommonSuccDegreeRootCrossingNonnegStatement :=
  posComboNoCommonSuccDegreeRootCrossing_of_rootCount
    (posComboNoCommonSuccDegreeRootCount_of_rootCountNonRoot hcount)

/-- The succ-degree root-crossing target follows from the upper common-non-root
root-count formulation. -/
theorem posComboNoCommonSuccDegreeRootCrossing_of_rootCountAboveNonRoot
    (hcount : PosComboNoCommonSuccDegreeRootCountAboveNonRootNonnegStatement) :
    PosComboNoCommonSuccDegreeRootCrossingNonnegStatement :=
  posComboNoCommonSuccDegreeRootCrossing_of_rootCountAbove
    (posComboNoCommonSuccDegreeRootCountAbove_of_nonRoot hcount)

/-- The fixed-orientation succ-degree endpoint implies the upper-threshold
root-count target. -/
theorem posComboNoCommonSuccDegreeRootCountAbove_of_orientation
    (horient : PosComboNoCommonSuccDegreeOrientationNonnegStatement) :
    PosComboNoCommonSuccDegreeRootCountAboveNonnegStatement := by
  intro f g hf_pos hg_pos hfnn hgnn hfg hdeg hno _hf_split
  exact succDegreeRootCountAbove_of_prec
    (horient hf_pos hg_pos hfnn hgnn hfg hdeg hno) hdeg

/-- The fixed-orientation succ-degree endpoint implies the lower-threshold
root-count target, via the upper/lower threshold conversion. -/
theorem posComboNoCommonSuccDegreeRootCount_of_orientation
    (horient : PosComboNoCommonSuccDegreeOrientationNonnegStatement) :
    PosComboNoCommonSuccDegreeRootCountNonnegStatement :=
  posComboNoCommonSuccDegreeRootCount_of_rootCountAbove
    (posComboNoCommonSuccDegreeRootCountAbove_of_orientation horient)

/-- Upper-threshold `divX` reduction of the right-zero lead branch.

This is the same reduction as
`posComboNoCommonSuccDegreeRootCountLeadRightZero_of_divX_sameDegreeCount`,
but with the same-degree comparison supplied in the opposite upper-threshold
orientation between `g.divX` and `f`. -/
theorem
    posComboNoCommonSuccDegreeRootCountLeadRightZero_of_divX_sameDegreeCountAbove
    (hcount :
      ∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        g.natDegree = f.natDegree + 1 →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        f.Splits →
        f.coeff 0 ≠ 0 →
        g.coeff 0 = 0 →
        ∀ x : ℝ,
          ((g.divX.roots.filter (x < ·)).card : ℤ) ≤
              (f.roots.filter (x < ·)).card ∧
          ((f.roots.filter (x < ·)).card : ℤ) ≤
              (g.divX.roots.filter (x < ·)).card + 1) :
    PosComboNoCommonSuccDegreeRootCountLeadRightZeroNonnegStatement :=
  posComboNoCommonSuccDegreeRootCountLeadRightZero_of_divX_sameDegreeCount
    (fun {f g} hf_pos hg_pos hfnn hgnn hfg hdeg hno hf_split hf0 hg0 x => by
      have hg_split : g.Splits :=
        (hfg.isRealRooted_right_of_succDegree hf_pos hg_pos hdeg).2
      have hdiv_split : g.divX.Splits :=
        (DegreeDropReversal.splits_iff_divX_splits_of_coeff_zero hg0).1 hg_split
      have hdiv_deg : g.divX.natDegree = f.natDegree := by
        rw [Polynomial.natDegree_divX_eq_natDegree_tsub_one, hdeg]
        simp
      exact (sameDegreeRootCountAbove_oriented_iff_rootCount_oriented_pointwise
        hf_split hdiv_split hdiv_deg x).mp
        (hcount hf_pos hg_pos hfnn hgnn hfg hdeg hno hf_split hf0 hg0 x))

/-- `Prec`/`divX` reduction of the right-zero lead branch.

When `g.coeff 0 = 0`, `g.divX` has the same degree as `f`, so a same-degree
interlacing orientation `Prec (g.divX) f` supplies exactly the oriented
lower-threshold count comparison needed by
`posComboNoCommonSuccDegreeRootCountLeadRightZero_of_divX_sameDegreeCount`.
This packages the whole right-zero lead branch from a checked orientation. -/
theorem posComboNoCommonSuccDegreeRootCountLeadRightZero_of_divX_prec
    (horient :
      PosComboNoCommonSuccDegreeRootCountLeadRightZeroDivXPrecStatement) :
    PosComboNoCommonSuccDegreeRootCountLeadRightZeroNonnegStatement := by
  apply posComboNoCommonSuccDegreeRootCountLeadRightZero_of_divX_sameDegreeCount
  intro f g hf_pos hg_pos hfnn hgnn hfg hdeg hno hf_split hf0 hg0 x
  have hprec : Prec (g.divX) f :=
    horient hf_pos hg_pos hfnn hgnn hfg hdeg hno hf_split hf0 hg0
  have hgdivX : g.divX.natDegree = g.natDegree - 1 :=
    Polynomial.natDegree_divX_eq_natDegree_tsub_one
  have hdeg' : f.natDegree = g.divX.natDegree := by
    rw [hgdivX]
    lia
  exact sameDegreeRootCountOriented_of_prec hprec hdeg' x

/-- The full lead root-count branch follows from the both-nonzero branch and
the `divX` orientation target for the right-zero branch. -/
theorem posComboNoCommonSuccDegreeRootCountLead_of_bothNonzero_and_divX_prec
    (hboth : PosComboNoCommonSuccDegreeRootCountLeadBothNonzeroNonnegStatement)
    (hdivX : PosComboNoCommonSuccDegreeRootCountLeadRightZeroDivXPrecStatement) :
    PosComboNoCommonSuccDegreeRootCountLeadNonnegStatement :=
  posComboNoCommonSuccDegreeRootCountLead_of_bothNonzero_and_rightZero hboth
    (posComboNoCommonSuccDegreeRootCountLeadRightZero_of_divX_prec hdivX)

/-- The residual succ-degree root-count branch follows from an interlacing
orientation in that branch. -/
theorem posComboNoCommonSuccDegreeRootCountResidual_of_prec
    (horient : PosComboNoCommonSuccDegreeRootCountResidualPrecStatement) :
    PosComboNoCommonSuccDegreeRootCountResidualNonnegStatement := by
  intro f g hf_pos hg_pos hfnn hgnn hfg hdeg hno hf_split hf0 hg0
  exact succDegreeRootCount_of_prec
    (horient hf_pos hg_pos hfnn hgnn hfg hdeg hno hf_split hf0 hg0) hdeg

/-- The succ-degree no-common root-count target splits into exactly two
constant-term branches: the `f.coeff 0 ≠ 0` branch and the residual
`f.coeff 0 = 0`, `g.coeff 0 ≠ 0` branch.  The no-common-root hypothesis rules
out the common-`X` branch. -/
theorem posComboNoCommonSuccDegreeRootCount_of_residual_and_lead
    (hlead : PosComboNoCommonSuccDegreeRootCountLeadNonnegStatement)
    (hres : PosComboNoCommonSuccDegreeRootCountResidualNonnegStatement) :
    PosComboNoCommonSuccDegreeRootCountNonnegStatement := by
  intro f g hf_pos hg_pos hfnn hgnn hfg hdeg hno hf_split
  by_cases hf0 : f.coeff 0 = 0
  · exact hres hf_pos hg_pos hfnn hgnn hfg hdeg hno hf_split hf0
      (right_coeff_zero_ne_of_no_common_of_left_coeff_zero hno hf0)
  · exact hlead hf_pos hg_pos hfnn hgnn hfg hdeg hno hf_split hf0

/-- The upper-threshold succ-degree no-common root-count target follows from
the two lower-threshold constant-term branches. -/
theorem posComboNoCommonSuccDegreeRootCountAbove_of_residual_and_lead
    (hlead : PosComboNoCommonSuccDegreeRootCountLeadNonnegStatement)
    (hres : PosComboNoCommonSuccDegreeRootCountResidualNonnegStatement) :
    PosComboNoCommonSuccDegreeRootCountAboveNonnegStatement :=
  posComboNoCommonSuccDegreeRootCountAbove_of_rootCount
    (posComboNoCommonSuccDegreeRootCount_of_residual_and_lead hlead hres)

/-- The succ-degree root-crossing target follows from the two constant-term
root-count branches. -/
theorem posComboNoCommonSuccDegreeRootCrossing_of_residual_and_lead
    (hlead : PosComboNoCommonSuccDegreeRootCountLeadNonnegStatement)
    (hres : PosComboNoCommonSuccDegreeRootCountResidualNonnegStatement) :
    PosComboNoCommonSuccDegreeRootCrossingNonnegStatement :=
  posComboNoCommonSuccDegreeRootCrossing_of_rootCount
    (posComboNoCommonSuccDegreeRootCount_of_residual_and_lead hlead hres)

/-- The lower-threshold succ-degree root-count target follows from the
residual branch, the both-nonzero lead branch, and the right-zero `divX`
orientation target. -/
theorem posComboNoCommonSuccDegreeRootCount_of_residual_bothNonzero_divX_prec
    (hboth : PosComboNoCommonSuccDegreeRootCountLeadBothNonzeroNonnegStatement)
    (hdivX : PosComboNoCommonSuccDegreeRootCountLeadRightZeroDivXPrecStatement)
    (hres : PosComboNoCommonSuccDegreeRootCountResidualNonnegStatement) :
    PosComboNoCommonSuccDegreeRootCountNonnegStatement :=
  posComboNoCommonSuccDegreeRootCount_of_residual_and_lead
    (posComboNoCommonSuccDegreeRootCountLead_of_bothNonzero_and_divX_prec
      hboth hdivX)
    hres

/-- The upper-threshold succ-degree root-count target follows from the
residual branch, the both-nonzero lead branch, and the right-zero `divX`
orientation target. -/
theorem posComboNoCommonSuccDegreeRootCountAbove_of_residual_bothNonzero_divX_prec
    (hboth : PosComboNoCommonSuccDegreeRootCountLeadBothNonzeroNonnegStatement)
    (hdivX : PosComboNoCommonSuccDegreeRootCountLeadRightZeroDivXPrecStatement)
    (hres : PosComboNoCommonSuccDegreeRootCountResidualNonnegStatement) :
    PosComboNoCommonSuccDegreeRootCountAboveNonnegStatement :=
  posComboNoCommonSuccDegreeRootCountAbove_of_residual_and_lead
    (posComboNoCommonSuccDegreeRootCountLead_of_bothNonzero_and_divX_prec
      hboth hdivX)
    hres

/-- The succ-degree root-crossing target follows from the residual branch, the
both-nonzero lead branch, and the right-zero `divX` orientation target. -/
theorem posComboNoCommonSuccDegreeRootCrossing_of_residual_bothNonzero_divX_prec
    (hboth : PosComboNoCommonSuccDegreeRootCountLeadBothNonzeroNonnegStatement)
    (hdivX : PosComboNoCommonSuccDegreeRootCountLeadRightZeroDivXPrecStatement)
    (hres : PosComboNoCommonSuccDegreeRootCountResidualNonnegStatement) :
    PosComboNoCommonSuccDegreeRootCrossingNonnegStatement :=
  posComboNoCommonSuccDegreeRootCrossing_of_residual_and_lead
    (posComboNoCommonSuccDegreeRootCountLead_of_bothNonzero_and_divX_prec
      hboth hdivX)
    hres

/-- The lower-threshold succ-degree root-count target follows from the
residual orientation target, the both-nonzero lead branch, and the right-zero
`divX` orientation target. -/
theorem posComboNoCommonSuccDegreeRootCount_of_residualPrec_bothNonzero_divX_prec
    (hresPrec : PosComboNoCommonSuccDegreeRootCountResidualPrecStatement)
    (hboth : PosComboNoCommonSuccDegreeRootCountLeadBothNonzeroNonnegStatement)
    (hdivX : PosComboNoCommonSuccDegreeRootCountLeadRightZeroDivXPrecStatement) :
    PosComboNoCommonSuccDegreeRootCountNonnegStatement :=
  posComboNoCommonSuccDegreeRootCount_of_residual_bothNonzero_divX_prec
    hboth hdivX (posComboNoCommonSuccDegreeRootCountResidual_of_prec hresPrec)

/-- The upper-threshold succ-degree root-count target follows from the residual
orientation target, the both-nonzero lead branch, and the right-zero `divX`
orientation target. -/
theorem
    posComboNoCommonSuccDegreeRootCountAbove_of_residualPrec_bothNonzero_divX_prec
    (hresPrec : PosComboNoCommonSuccDegreeRootCountResidualPrecStatement)
    (hboth : PosComboNoCommonSuccDegreeRootCountLeadBothNonzeroNonnegStatement)
    (hdivX : PosComboNoCommonSuccDegreeRootCountLeadRightZeroDivXPrecStatement) :
    PosComboNoCommonSuccDegreeRootCountAboveNonnegStatement :=
  posComboNoCommonSuccDegreeRootCountAbove_of_residual_bothNonzero_divX_prec
    hboth hdivX (posComboNoCommonSuccDegreeRootCountResidual_of_prec hresPrec)

/-- The succ-degree root-crossing target follows from the residual orientation
target, the both-nonzero lead branch, and the right-zero `divX` orientation
target. -/
theorem
    posComboNoCommonSuccDegreeRootCrossing_of_residualPrec_bothNonzero_divX_prec
    (hresPrec : PosComboNoCommonSuccDegreeRootCountResidualPrecStatement)
    (hboth : PosComboNoCommonSuccDegreeRootCountLeadBothNonzeroNonnegStatement)
    (hdivX : PosComboNoCommonSuccDegreeRootCountLeadRightZeroDivXPrecStatement) :
    PosComboNoCommonSuccDegreeRootCrossingNonnegStatement :=
  posComboNoCommonSuccDegreeRootCrossing_of_residual_bothNonzero_divX_prec
    hboth hdivX (posComboNoCommonSuccDegreeRootCountResidual_of_prec hresPrec)

/-- The compatible common-non-root root-count leaf implies closed-segment
endpoint count equality.  The root-count leaf bounds the endpoint upper-count
difference by one in both directions, while the no-crossing hypothesis forces
that difference to be even. -/
theorem compatibleSuccDegreeClosedSegmentCountEq_of_nonRoot
    (hcount : CompatibleSuccDegreeRootCountAboveNonRootStatement) :
    CompatibleSuccDegreeClosedSegmentCountEqStatement := by
  intro f g hcomp hf_pos hg_pos hdeg hf_split x hxf hxg hseg
  obtain ⟨hfg_le, hgf_le⟩ :=
    hcount hcomp hf_pos hg_pos hdeg hf_split x hxf hxg
  exact
    compatibleSuccDegreeClosedSegmentCountEq_of_rootCountAbove_bounds
      hcomp hf_pos hg_pos hdeg hf_split hxf hxg hseg hfg_le hgf_le

/-- The compatible root-count target gives the gap-at-most-two target: in
degree at least two this is the derivative induction step, while degrees zero
and one are handled by the explicit low-degree bases. -/
theorem compatibleSuccDegreeRootCountAboveLeTwo_of_nonRoot
    (hcount : CompatibleSuccDegreeRootCountAboveNonRootStatement) :
    CompatibleSuccDegreeRootCountAboveLeTwoStatement := by
  intro f g hcomp hf_pos hg_pos hdeg hf_split x _hxf _hxg
  by_cases hfdeg : 2 ≤ f.natDegree
  · exact compatibleSuccDegreeRootCountAbove_le_two_of_derivative
      hcount hcomp hf_pos hg_pos hdeg hf_split hfdeg x
  · have hfdeg_le_one : f.natDegree ≤ 1 :=
      Nat.lt_succ_iff.mp (Nat.lt_of_not_ge hfdeg)
    obtain ⟨hfg, hgf⟩ :=
      compatibleSuccDegreeRootCountAbove_of_natDegree_le_one
        hcomp hf_pos hg_pos hdeg hf_split hfdeg_le_one x
    constructor <;> linarith

/-- The exact gap-two obstruction closes the compatible common-non-root
root-count target.  The proof is by strong induction on the lower endpoint
degree: low degrees are explicit, while degree at least two uses derivative
induction for the gap-at-most-two bound and the no-gap hypothesis to rule out
the remaining exact gap. -/
theorem compatibleSuccDegreeRootCountAboveNonRoot_of_noGapTwo
    (hgap : CompatibleSuccDegreeRootCountAboveNoGapTwoStatement) :
    CompatibleSuccDegreeRootCountAboveNonRootStatement := by
  have hmain :
      ∀ n : ℕ, ∀ {f g : ℝ[X]},
        f.natDegree = n →
        Compatible f g →
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        g.natDegree = f.natDegree + 1 →
        f.Splits →
        ∀ x : ℝ, ¬ f.IsRoot x → ¬ g.IsRoot x →
          ((f.roots.filter (x < ·)).card : ℤ) -
              (g.roots.filter (x < ·)).card ≤ 1 ∧
          ((g.roots.filter (x < ·)).card : ℤ) -
              (f.roots.filter (x < ·)).card ≤ 1 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro f g hfdeg_eq hcomp hf_pos hg_pos hdeg hf_split x hxf hxg
      by_cases hfdeg : 2 ≤ f.natDegree
      · have hf'_pos : HasPosLeadingCoeff f.derivative :=
          hf_pos.derivative (by lia)
        have hg'_pos : HasPosLeadingCoeff g.derivative :=
          hg_pos.derivative (by rw [hdeg]; lia)
        have hdeg' : g.derivative.natDegree = f.derivative.natDegree + 1 :=
          succDegree_derivative_natDegree_eq hdeg (by lia)
        have hf'_split : f.derivative.Splits :=
          (derivative_interlaces hf_split hfdeg).2.1.2
        have hfder_lt_self : f.derivative.natDegree < f.natDegree := by
          rw [f.natDegree_derivative]
          lia
        have hfder_lt : f.derivative.natDegree < n := by
          rwa [hfdeg_eq] at hfder_lt_self
        have hder_bound :
            ∀ y : ℝ,
              ¬ f.derivative.IsRoot y → ¬ g.derivative.IsRoot y →
                ((f.derivative.roots.filter (y < ·)).card : ℤ) -
                    (g.derivative.roots.filter (y < ·)).card ≤ 1 ∧
                ((g.derivative.roots.filter (y < ·)).card : ℤ) -
                    (f.derivative.roots.filter (y < ·)).card ≤ 1 := by
          intro y hyf hyg
          exact ih f.derivative.natDegree hfder_lt rfl hcomp.derivative
            hf'_pos hg'_pos hdeg' hf'_split y hyf hyg
        obtain ⟨hfg_le2, hgf_le2⟩ :=
          compatibleSuccDegreeRootCountAbove_le_two_of_derivative_bound
            hcomp hf_pos hg_pos hdeg hf_split hfdeg hder_bound x
        obtain ⟨hfg_ne2, hgf_ne2⟩ :=
          hgap hcomp hf_pos hg_pos hdeg hf_split x hxf hxg
        exact ⟨int_le_one_of_le_two_ne_two hfg_le2 hfg_ne2,
          int_le_one_of_le_two_ne_two hgf_le2 hgf_ne2⟩
      · have hfdeg_le_one : f.natDegree ≤ 1 :=
          Nat.lt_succ_iff.mp (Nat.lt_of_not_ge hfdeg)
        exact compatibleSuccDegreeRootCountAbove_of_natDegree_le_one
          hcomp hf_pos hg_pos hdeg hf_split hfdeg_le_one x
  intro f g hcomp hf_pos hg_pos hdeg hf_split x hxf hxg
  exact hmain f.natDegree rfl hcomp hf_pos hg_pos hdeg hf_split x hxf hxg

/-- The closed-segment no-gap-two theorem closes the compatible succ-degree
common-non-root upper root-count leaf. -/
theorem compatibleSuccDegreeRootCountAboveNonRoot_of_closedSegment
    (hclosed : CompatibleSuccDegreeClosedSegmentNoGapTwoStatement) :
    CompatibleSuccDegreeRootCountAboveNonRootStatement :=
  compatibleSuccDegreeRootCountAboveNonRoot_of_noGapTwo
    (compatibleSuccDegreeRootCountAboveNoGapTwo_of_closedSegment hclosed)

/-- Closed-segment endpoint count equality closes the compatible succ-degree
common-non-root upper root-count leaf. -/
theorem compatibleSuccDegreeRootCountAboveNonRoot_of_closedSegmentCountEq
    (hcount : CompatibleSuccDegreeClosedSegmentCountEqStatement) :
    CompatibleSuccDegreeRootCountAboveNonRootStatement :=
  compatibleSuccDegreeRootCountAboveNonRoot_of_closedSegment
    (compatibleSuccDegreeClosedSegmentNoGapTwo_of_countEq hcount)

/-- The closed-segment endpoint count-equality target is equivalent to the
compatible common-non-root upper root-count leaf. -/
theorem compatibleSuccDegreeClosedSegmentCountEq_iff_nonRoot :
    CompatibleSuccDegreeClosedSegmentCountEqStatement ↔
      CompatibleSuccDegreeRootCountAboveNonRootStatement :=
  ⟨compatibleSuccDegreeRootCountAboveNonRoot_of_closedSegmentCountEq,
    compatibleSuccDegreeClosedSegmentCountEq_of_nonRoot⟩

/-- Closed-segment endpoint count equality also supplies the positive-combo
succ-degree common-non-root upper root-count leaf used by the repaired #42
pair-interleaver route. -/
theorem posComboNoCommonSuccDegreeRootCountAboveNonRoot_of_closedSegmentCountEq
    (hcount : CompatibleSuccDegreeClosedSegmentCountEqStatement) :
    PosComboNoCommonSuccDegreeRootCountAboveNonRootNonnegStatement :=
  posComboNoCommonSuccDegreeRootCountAboveNonRoot_of_compatible
    (compatibleSuccDegreeRootCountAboveNonRoot_of_closedSegmentCountEq hcount)

/-- Closed-segment no-gap-two supplies the positive-combo succ-degree
common-non-root upper root-count leaf. -/
theorem posComboNoCommonSuccDegreeRootCountAboveNonRoot_of_closedSegmentNoGapTwo
    (hclosed : CompatibleSuccDegreeClosedSegmentNoGapTwoStatement) :
    PosComboNoCommonSuccDegreeRootCountAboveNonRootNonnegStatement :=
  posComboNoCommonSuccDegreeRootCountAboveNonRoot_of_compatible
    (compatibleSuccDegreeRootCountAboveNonRoot_of_closedSegment hclosed)

/-- The right-pencil no-gap-two theorem closes the compatible succ-degree
common-non-root upper root-count leaf. -/
theorem compatibleSuccDegreeRootCountAboveNonRoot_of_rightFamily
    (hright : CompatibleSuccDegreeRightFamilyNoGapTwoStatement) :
    CompatibleSuccDegreeRootCountAboveNonRootStatement :=
  compatibleSuccDegreeRootCountAboveNonRoot_of_noGapTwo
    (compatibleSuccDegreeRootCountAboveNoGapTwo_of_rightFamily hright)

/-- The endpoint-sign no-gap-two theorem closes the compatible succ-degree
common-non-root upper root-count leaf. -/
theorem compatibleSuccDegreeRootCountAboveNonRoot_of_endpointSign
    (hsign : CompatibleSuccDegreeEndpointSignNoGapTwoStatement) :
    CompatibleSuccDegreeRootCountAboveNonRootStatement :=
  compatibleSuccDegreeRootCountAboveNonRoot_of_noGapTwo
    (compatibleSuccDegreeRootCountAboveNoGapTwo_of_endpointSign hsign)

/-- The lower-threshold endpoint-sign no-gap theorem closes the compatible
succ-degree common-non-root upper root-count leaf. -/
theorem compatibleSuccDegreeRootCountAboveNonRoot_of_endpointSignLower
    (hlower : CompatibleSuccDegreeEndpointSignLowerNoGapStatement) :
    CompatibleSuccDegreeRootCountAboveNonRootStatement :=
  compatibleSuccDegreeRootCountAboveNonRoot_of_noGapTwo
    (compatibleSuccDegreeRootCountAboveNoGapTwo_of_endpointSignLower hlower)

/-- The exact lower-count endpoint comparison closes the compatible
succ-degree common-non-root upper root-count leaf. -/
theorem compatibleSuccDegreeRootCountAboveNonRoot_of_lowerCountEq
    (hcount : CompatibleSuccDegreeEndpointSignLowerCountEqStatement) :
    CompatibleSuccDegreeRootCountAboveNonRootStatement :=
  compatibleSuccDegreeRootCountAboveNonRoot_of_noGapTwo
    (compatibleSuccDegreeRootCountAboveNoGapTwo_of_lowerCountEq hcount)

/-- Right-pencil no-gap-two supplies the positive-combo succ-degree
common-non-root upper root-count leaf. -/
theorem posComboNoCommonSuccDegreeRootCountAboveNonRoot_of_rightFamilyNoGapTwo
    (hright : CompatibleSuccDegreeRightFamilyNoGapTwoStatement) :
    PosComboNoCommonSuccDegreeRootCountAboveNonRootNonnegStatement :=
  posComboNoCommonSuccDegreeRootCountAboveNonRoot_of_compatible
    (compatibleSuccDegreeRootCountAboveNonRoot_of_rightFamily hright)

/-- Endpoint-sign no-gap-two supplies the positive-combo succ-degree
common-non-root upper root-count leaf. -/
theorem posComboNoCommonSuccDegreeRootCountAboveNonRoot_of_endpointSignNoGapTwo
    (hsign : CompatibleSuccDegreeEndpointSignNoGapTwoStatement) :
    PosComboNoCommonSuccDegreeRootCountAboveNonRootNonnegStatement :=
  posComboNoCommonSuccDegreeRootCountAboveNonRoot_of_compatible
    (compatibleSuccDegreeRootCountAboveNonRoot_of_endpointSign hsign)

/-- Lower endpoint-sign no-gap supplies the positive-combo succ-degree
common-non-root upper root-count leaf. -/
theorem posComboNoCommonSuccDegreeRootCountAboveNonRoot_of_endpointSignLower
    (hlower : CompatibleSuccDegreeEndpointSignLowerNoGapStatement) :
    PosComboNoCommonSuccDegreeRootCountAboveNonRootNonnegStatement :=
  posComboNoCommonSuccDegreeRootCountAboveNonRoot_of_compatible
    (compatibleSuccDegreeRootCountAboveNonRoot_of_endpointSignLower hlower)

/-- Exact lower-count endpoint comparison supplies the positive-combo
succ-degree common-non-root upper root-count leaf. -/
theorem posComboNoCommonSuccDegreeRootCountAboveNonRoot_of_lowerCountEq
    (hcount : CompatibleSuccDegreeEndpointSignLowerCountEqStatement) :
    PosComboNoCommonSuccDegreeRootCountAboveNonRootNonnegStatement :=
  posComboNoCommonSuccDegreeRootCountAboveNonRoot_of_compatible
    (compatibleSuccDegreeRootCountAboveNonRoot_of_lowerCountEq hcount)

/-- Low-degree base case for the succ-degree root-crossing target.  In the
constant-vs-linear case all crossing inequalities are vacuous. -/
theorem succDegreeRootCrossing_of_natDegree_eq_zero
    {f g : ℝ[X]} (hf_deg0 : f.natDegree = 0) :
    (∀ j, 1 ≤ j → j ≤ f.natDegree →
        (rootSeqDesc g).getD j 0 ≤ (rootSeqDesc f).getD (j - 1) 0) ∧
    (∀ j, 1 ≤ j → j < f.natDegree →
        (rootSeqDesc f).getD j 0 ≤ (rootSeqDesc g).getD (j - 1) 0) := by
  refine ⟨?_, ?_⟩ <;> intro j hj1 hjlt <;> exfalso <;> lia

private lemma succCross_getD_reverse (l : List ℝ) (j : ℕ) (hj : j < l.length) :
    l.reverse.getD j 0 = l.getD (l.length - 1 - j) 0 := by
  have hj' : j < l.reverse.length := by simpa using hj
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hj', List.getElem?_eq_getElem (by lia)]
  simp [List.getElem_reverse]

private lemma succCross_getD_mono
    {rs : List ℝ} (hrs : rs.Pairwise (· ≤ ·))
    {i j : ℕ} (hij : i ≤ j) (hj : j < rs.length) :
    rs.getD i 0 ≤ rs.getD j 0 := by
  have hi : i < rs.length := by lia
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj]
  simp only [Option.getD_some]
  rcases lt_or_eq_of_le hij with hij' | rfl
  · exact List.pairwise_iff_get.mp hrs ⟨i, hi⟩ ⟨j, hj⟩ hij'
  · simp

/-- Differ-by-one weak interlacing of ascending root lists gives the two
descending-root crossing inequalities in the succ-degree shape consumed by
`rootSlotInterval_inter_nonempty_of_crossing`. -/
theorem rootCrossing_of_listInterlaces {ss rs : List ℝ}
    (hrs_pw : rs.Pairwise (· ≤ ·))
    (hlen : ss.length + 1 = rs.length)
    (hint : ListInterlaces ss rs) :
    (∀ j, 1 ≤ j → j ≤ ss.length →
        rs.reverse.getD j 0 ≤ ss.reverse.getD (j - 1) 0) ∧
    (∀ j, 1 ≤ j → j < ss.length →
        ss.reverse.getD j 0 ≤ rs.reverse.getD (j - 1) 0) := by
  obtain ⟨hA, hB⟩ := listInterlaces_getD_bounds ss rs hint hlen
  refine ⟨?_, ?_⟩
  · intro j hj1 hj2
    have hjr : j < rs.length := by lia
    have hjs : j - 1 < ss.length := by lia
    rw [succCross_getD_reverse rs j hjr, succCross_getD_reverse ss (j - 1) hjs]
    have e1 : rs.length - 1 - j = ss.length - j := by lia
    have e2 : ss.length - 1 - (j - 1) = ss.length - j := by lia
    rw [e1, e2]
    exact hA (ss.length - j) (by lia)
  · intro j hj1 hj2
    have hjs : j < ss.length := by lia
    have hjr : j - 1 < rs.length := by lia
    rw [succCross_getD_reverse ss j hjs, succCross_getD_reverse rs (j - 1) hjr]
    set i := ss.length - 1 - j with hi
    have e2 : rs.length - 1 - (j - 1) = i + 2 := by lia
    rw [e2]
    have hstep := hB i (by lia)
    have hmono : rs.getD (i + 1) 0 ≤ rs.getD (i + 2) 0 :=
      succCross_getD_mono hrs_pw (by lia) (by lia)
    exact le_trans hstep hmono

/-- The fixed-orientation succ-degree statement implies the descending-root
crossing endpoint. -/
theorem posComboNoCommonSuccDegreeRootCrossing_of_orientation
    (hsucc : PosComboNoCommonSuccDegreeOrientationNonnegStatement) :
    PosComboNoCommonSuccDegreeRootCrossingNonnegStatement := by
  intro f g hf_pos hg_pos hfnn hgnn hfg hdeg hno _
  have hprec : Prec f g := hsucc hf_pos hg_pos hfnn hgnn hfg hdeg hno
  obtain ⟨hf, hg, ss, rs, hss_pw, hrs_pw, hss_eq, hrs_eq, hshape⟩ := hprec
  have hss_len : ss.length = f.natDegree := by
    rw [← Multiset.coe_card, hss_eq, card_roots_of_splits hf.2]
  have hrs_len : rs.length = g.natDegree := by
    rw [← Multiset.coe_card, hrs_eq, card_roots_of_splits hg.2]
  have hint : ListInterlaces ss rs := by
    rcases hshape with ⟨_, h⟩ | ⟨hlen2, _⟩
    · exact h
    · exfalso
      rw [hss_len, hrs_len, hdeg] at hlen2
      lia
  have hlen : ss.length + 1 = rs.length := by rw [hss_len, hrs_len, hdeg]
  have hdf : rootSeqDesc f = ss.reverse :=
    rootSeqDesc_eq_reverse_of_pairwise hss_pw hss_eq
  have hdg : rootSeqDesc g = rs.reverse :=
    rootSeqDesc_eq_reverse_of_pairwise hrs_pw hrs_eq
  obtain ⟨hc1, hc2⟩ := rootCrossing_of_listInterlaces hrs_pw hlen hint
  rw [hdf, hdg]
  exact ⟨fun j hj1 hj2 => hc1 j hj1 (by rw [hss_len]; exact hj2),
    fun j hj1 hj2 => hc2 j hj1 (by rw [hss_len]; exact hj2)⟩

/-- **Decomposition of milestone B2 into its two honest remaining pieces.**

The succ-degree slot-data statement follows from left-endpoint real-rootedness
of `f` (`PosComboSuccDegreeLeftSplitsNonnegStatement`) together with the
descending-root crossing inequalities
(`PosComboNoCommonSuccDegreeRootCrossingNonnegStatement`); the combinatorial
step is discharged by `rootSlotInterval_inter_nonempty_of_crossing`. Via
`posComboNoCommonSuccDegreeSlotData_iff_pairHasCommonInterleaver` this reduces
the corrected common-right-interleaver target for milestone B2 (#42) to these
two analytic statements. -/
theorem posComboNoCommonSuccDegreeSlotData_of_leftSplits_and_rootCrossing
    (hsplit : PosComboSuccDegreeLeftSplitsNonnegStatement)
    (hcross : PosComboNoCommonSuccDegreeRootCrossingNonnegStatement) :
    PosComboNoCommonSuccDegreeSlotDataNonnegStatement := by
  intro f g hf_pos hg_pos hfnn hgnn hfg hsucc hno
  have hf_split : f.Splits := hsplit hf_pos hg_pos hfnn hgnn hfg hsucc
  have hg_split : g.Splits :=
    (hfg.isRealRooted_right_of_succDegree hf_pos hg_pos hsucc).2
  refine ⟨⟨HasPosLeadingCoeff.ne_zero hf_pos, hf_split⟩, ?_⟩
  obtain ⟨hc1, hc2⟩ := hcross hf_pos hg_pos hfnn hgnn hfg hsucc hno hf_split
  have hlenf : (rootSeqDesc f).length = f.natDegree := rootSeqDesc_length hf_split
  have hleng : (rootSeqDesc g).length = g.natDegree := rootSeqDesc_length hg_split
  intro j _ hjf hjg
  exact
    rootSlotInterval_inter_nonempty_of_crossing (rootSeqDesc f) (rootSeqDesc g)
      rootSeqDesc_pairwise rootSeqDesc_pairwise
      (by rw [hleng, hlenf, hsucc])
      (fun k hk1 hk2 => hc1 k hk1 (by rw [hlenf] at hk2; exact hk2))
      (fun k hk1 hk2 => hc2 k hk1 (by rw [hlenf] at hk2; exact hk2))
      j hjf hjg

/-- The corrected succ-degree pair-interleaver endpoint follows directly from
left-endpoint real-rootedness and the succ-degree descending-root crossing
inequalities. -/
theorem succDegreePairHasCommonInterleaver_nonneg_of_leftSplits_and_rootCrossing
    (hsplit : PosComboSuccDegreeLeftSplitsNonnegStatement)
    (hcross : PosComboNoCommonSuccDegreeRootCrossingNonnegStatement) :
    PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement :=
  succDegreePairHasCommonInterleaver_nonneg_of_slotData
    (posComboNoCommonSuccDegreeSlotData_of_leftSplits_and_rootCrossing hsplit hcross)

/-- Succ-degree slot data from the unconditional root-continuity left endpoint
and the descending-root crossing inequalities. -/
theorem posComboNoCommonSuccDegreeSlotData_of_rootCrossing
    (hcross : PosComboNoCommonSuccDegreeRootCrossingNonnegStatement) :
    PosComboNoCommonSuccDegreeSlotDataNonnegStatement :=
  posComboNoCommonSuccDegreeSlotData_of_leftSplits_and_rootCrossing
    PosComboSuccDegreeLeftSplitsNonnegStatement_of_rootContinuity hcross

/-- The corrected succ-degree pair-interleaver endpoint follows from the
succ-degree descending-root crossing inequalities alone; root continuity
supplies the left endpoint. -/
theorem succDegreePairHasCommonInterleaver_nonneg_of_rootCrossing
    (hcross : PosComboNoCommonSuccDegreeRootCrossingNonnegStatement) :
    PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement :=
  succDegreePairHasCommonInterleaver_nonneg_of_slotData
    (posComboNoCommonSuccDegreeSlotData_of_rootCrossing hcross)

/-- Succ-degree slot data from the lower-threshold root-count formulation. -/
theorem posComboNoCommonSuccDegreeSlotData_of_rootCount
    (hcount : PosComboNoCommonSuccDegreeRootCountNonnegStatement) :
    PosComboNoCommonSuccDegreeSlotDataNonnegStatement :=
  posComboNoCommonSuccDegreeSlotData_of_rootCrossing
    (posComboNoCommonSuccDegreeRootCrossing_of_rootCount hcount)

/-- The corrected succ-degree pair-interleaver endpoint follows directly from
the lower-threshold root-count formulation. -/
theorem succDegreePairHasCommonInterleaver_nonneg_of_rootCount
    (hcount : PosComboNoCommonSuccDegreeRootCountNonnegStatement) :
    PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement :=
  succDegreePairHasCommonInterleaver_nonneg_of_rootCrossing
    (posComboNoCommonSuccDegreeRootCrossing_of_rootCount hcount)

/-- Succ-degree slot data from the upper-threshold root-count formulation. -/
theorem posComboNoCommonSuccDegreeSlotData_of_rootCountAbove
    (hcount : PosComboNoCommonSuccDegreeRootCountAboveNonnegStatement) :
    PosComboNoCommonSuccDegreeSlotDataNonnegStatement :=
  posComboNoCommonSuccDegreeSlotData_of_rootCrossing
    (posComboNoCommonSuccDegreeRootCrossing_of_rootCountAbove hcount)

/-- The corrected succ-degree pair-interleaver endpoint follows directly from
the upper-threshold root-count formulation. -/
theorem succDegreePairHasCommonInterleaver_nonneg_of_rootCountAbove
    (hcount : PosComboNoCommonSuccDegreeRootCountAboveNonnegStatement) :
    PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement :=
  succDegreePairHasCommonInterleaver_nonneg_of_rootCrossing
    (posComboNoCommonSuccDegreeRootCrossing_of_rootCountAbove hcount)

/-- Succ-degree slot data from the common-non-root upper-threshold root-count
formulation. -/
theorem posComboNoCommonSuccDegreeSlotData_of_nonRoot
    (hcount : PosComboNoCommonSuccDegreeRootCountAboveNonRootNonnegStatement) :
    PosComboNoCommonSuccDegreeSlotDataNonnegStatement :=
  posComboNoCommonSuccDegreeSlotData_of_rootCountAbove
    (posComboNoCommonSuccDegreeRootCountAbove_of_nonRoot hcount)

/-- Succ-degree slot data from the common-non-root upper-threshold root-count
formulation, with an explicit name for the `rootCountAboveNonRoot` leaf. -/
theorem posComboNoCommonSuccDegreeSlotData_of_rootCountAboveNonRoot
    (hcount : PosComboNoCommonSuccDegreeRootCountAboveNonRootNonnegStatement) :
    PosComboNoCommonSuccDegreeSlotDataNonnegStatement :=
  posComboNoCommonSuccDegreeSlotData_of_nonRoot hcount

/-- The repaired succ-degree pair-interleaver endpoint follows from the
common-non-root upper-threshold root-count formulation. -/
theorem succDegreePairHasCommonInterleaver_nonneg_of_nonRoot
    (hcount : PosComboNoCommonSuccDegreeRootCountAboveNonRootNonnegStatement) :
    PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement :=
  succDegreePairHasCommonInterleaver_nonneg_of_rootCountAbove
    (posComboNoCommonSuccDegreeRootCountAbove_of_nonRoot hcount)

/-- The repaired succ-degree pair-interleaver endpoint follows from the
common-non-root upper-threshold root-count formulation, with an explicit name
for the `rootCountAboveNonRoot` leaf. -/
theorem succDegreePairHasCommonInterleaver_nonneg_of_rootCountAboveNonRoot
    (hcount : PosComboNoCommonSuccDegreeRootCountAboveNonRootNonnegStatement) :
    PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement :=
  succDegreePairHasCommonInterleaver_nonneg_of_nonRoot hcount

/-- Closed-segment endpoint count equality supplies the repaired succ-degree
#42 pair-interleaver endpoint. -/
theorem succDegreePairHasCommonInterleaver_nonneg_of_closedSegmentCountEq
    (hcount : CompatibleSuccDegreeClosedSegmentCountEqStatement) :
    PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement :=
  succDegreePairHasCommonInterleaver_nonneg_of_rootCountAboveNonRoot
    (posComboNoCommonSuccDegreeRootCountAboveNonRoot_of_closedSegmentCountEq hcount)

/-- Closed-segment no-gap-two supplies the repaired succ-degree #42
pair-interleaver endpoint. -/
theorem succDegreePairHasCommonInterleaver_nonneg_of_closedSegmentNoGapTwo
    (hclosed : CompatibleSuccDegreeClosedSegmentNoGapTwoStatement) :
    PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement :=
  succDegreePairHasCommonInterleaver_nonneg_of_rootCountAboveNonRoot
    (posComboNoCommonSuccDegreeRootCountAboveNonRoot_of_closedSegmentNoGapTwo hclosed)

/-- Right-pencil no-gap-two supplies the repaired succ-degree #42
pair-interleaver endpoint. -/
theorem succDegreePairHasCommonInterleaver_nonneg_of_rightFamilyNoGapTwo
    (hright : CompatibleSuccDegreeRightFamilyNoGapTwoStatement) :
    PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement :=
  succDegreePairHasCommonInterleaver_nonneg_of_rootCountAboveNonRoot
    (posComboNoCommonSuccDegreeRootCountAboveNonRoot_of_rightFamilyNoGapTwo hright)

/-- Endpoint-sign no-gap-two supplies the repaired succ-degree #42
pair-interleaver endpoint. -/
theorem succDegreePairHasCommonInterleaver_nonneg_of_endpointSignNoGapTwo
    (hsign : CompatibleSuccDegreeEndpointSignNoGapTwoStatement) :
    PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement :=
  succDegreePairHasCommonInterleaver_nonneg_of_rootCountAboveNonRoot
    (posComboNoCommonSuccDegreeRootCountAboveNonRoot_of_endpointSignNoGapTwo hsign)

/-- Lower endpoint-sign no-gap supplies the repaired succ-degree #42
pair-interleaver endpoint. -/
theorem succDegreePairHasCommonInterleaver_nonneg_of_endpointSignLower
    (hlower : CompatibleSuccDegreeEndpointSignLowerNoGapStatement) :
    PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement :=
  succDegreePairHasCommonInterleaver_nonneg_of_rootCountAboveNonRoot
    (posComboNoCommonSuccDegreeRootCountAboveNonRoot_of_endpointSignLower hlower)

/-- Exact lower-count endpoint comparison supplies the repaired succ-degree
#42 pair-interleaver endpoint. -/
theorem succDegreePairHasCommonInterleaver_nonneg_of_lowerCountEq
    (hcount : CompatibleSuccDegreeEndpointSignLowerCountEqStatement) :
    PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement :=
  succDegreePairHasCommonInterleaver_nonneg_of_rootCountAboveNonRoot
    (posComboNoCommonSuccDegreeRootCountAboveNonRoot_of_lowerCountEq hcount)

/-- Succ-degree slot data from the lower common-non-root root-count
formulation. -/
theorem posComboNoCommonSuccDegreeSlotData_of_rootCountNonRoot
    (hcount : PosComboNoCommonSuccDegreeRootCountNonRootNonnegStatement) :
    PosComboNoCommonSuccDegreeSlotDataNonnegStatement :=
  posComboNoCommonSuccDegreeSlotData_of_rootCount
    (posComboNoCommonSuccDegreeRootCount_of_rootCountNonRoot hcount)

/-- The repaired succ-degree pair-interleaver endpoint follows from the lower
common-non-root root-count formulation. -/
theorem succDegreePairHasCommonInterleaver_nonneg_of_rootCountNonRoot
    (hcount : PosComboNoCommonSuccDegreeRootCountNonRootNonnegStatement) :
    PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement :=
  succDegreePairHasCommonInterleaver_nonneg_of_rootCount
    (posComboNoCommonSuccDegreeRootCount_of_rootCountNonRoot hcount)

/-- Succ-degree slot data from the two lower-threshold constant-term
root-count branches. -/
theorem posComboNoCommonSuccDegreeSlotData_of_residual_and_lead
    (hlead : PosComboNoCommonSuccDegreeRootCountLeadNonnegStatement)
    (hres : PosComboNoCommonSuccDegreeRootCountResidualNonnegStatement) :
    PosComboNoCommonSuccDegreeSlotDataNonnegStatement :=
  posComboNoCommonSuccDegreeSlotData_of_rootCount
    (posComboNoCommonSuccDegreeRootCount_of_residual_and_lead hlead hres)

/-- The repaired succ-degree pair-interleaver endpoint follows from the two
lower-threshold constant-term root-count branches. -/
theorem succDegreePairHasCommonInterleaver_nonneg_of_residual_and_lead
    (hlead : PosComboNoCommonSuccDegreeRootCountLeadNonnegStatement)
    (hres : PosComboNoCommonSuccDegreeRootCountResidualNonnegStatement) :
    PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement :=
  succDegreePairHasCommonInterleaver_nonneg_of_rootCount
    (posComboNoCommonSuccDegreeRootCount_of_residual_and_lead hlead hres)

/-- The repaired succ-degree pair-interleaver endpoint follows from the
residual branch, the both-nonzero lead branch, and the right-zero `divX`
orientation target. -/
theorem succDegreePairHasCommonInterleaver_nonneg_of_residual_bothNonzero_divX_prec
    (hboth : PosComboNoCommonSuccDegreeRootCountLeadBothNonzeroNonnegStatement)
    (hdivX : PosComboNoCommonSuccDegreeRootCountLeadRightZeroDivXPrecStatement)
    (hres : PosComboNoCommonSuccDegreeRootCountResidualNonnegStatement) :
    PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement :=
  succDegreePairHasCommonInterleaver_nonneg_of_rootCount
    (posComboNoCommonSuccDegreeRootCount_of_residual_bothNonzero_divX_prec
      hboth hdivX hres)

/-- The repaired succ-degree pair-interleaver endpoint follows from the
residual orientation target, the both-nonzero lead branch, and the right-zero
`divX` orientation target. -/
theorem
    succDegreePairHasCommonInterleaver_nonneg_of_residualPrec_bothNonzero_divX_prec
    (hresPrec : PosComboNoCommonSuccDegreeRootCountResidualPrecStatement)
    (hboth : PosComboNoCommonSuccDegreeRootCountLeadBothNonzeroNonnegStatement)
    (hdivX : PosComboNoCommonSuccDegreeRootCountLeadRightZeroDivXPrecStatement) :
    PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement :=
  succDegreePairHasCommonInterleaver_nonneg_of_rootCount
    (posComboNoCommonSuccDegreeRootCount_of_residualPrec_bothNonzero_divX_prec
      hresPrec hboth hdivX)

/-- Succ-degree slot data from the PF/ASW left-endpoint route and the
descending-root crossing inequalities. -/
theorem posComboNoCommonSuccDegreeSlotData_of_forward_asw_and_rootCrossing
    (hASW : aissenSchoenbergWhitneyForwardOrZeroStatement)
    (hcross : PosComboNoCommonSuccDegreeRootCrossingNonnegStatement) :
    PosComboNoCommonSuccDegreeSlotDataNonnegStatement :=
  posComboNoCommonSuccDegreeSlotData_of_leftSplits_and_rootCrossing
    (PosComboSuccDegreeLeftSplitsNonnegStatement_of_forward_asw hASW) hcross

/-- Succ-degree slot data from the splitting-only ASW target and the
root-crossing target. -/
theorem posComboNoCommonSuccDegreeSlotData_of_forward_asw_splits_and_rootCrossing
    (hASW : aissenSchoenbergWhitneyForwardSplitsStatement)
    (hcross : PosComboNoCommonSuccDegreeRootCrossingNonnegStatement) :
    PosComboNoCommonSuccDegreeSlotDataNonnegStatement :=
  posComboNoCommonSuccDegreeSlotData_of_forward_asw_and_rootCrossing
    (aissenSchoenbergWhitneyForwardOrZero_of_splits hASW) hcross

/-- Succ-degree pair interleavers from the PF/ASW left-endpoint route and the
descending-root crossing inequalities. -/
theorem
    succDegreePairHasCommonInterleaver_nonneg_of_forward_asw_and_rootCrossing
    (hASW : aissenSchoenbergWhitneyForwardOrZeroStatement)
    (hcross : PosComboNoCommonSuccDegreeRootCrossingNonnegStatement) :
    PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement :=
  succDegreePairHasCommonInterleaver_nonneg_of_leftSplits_and_rootCrossing
    (PosComboSuccDegreeLeftSplitsNonnegStatement_of_forward_asw hASW) hcross

/-- Succ-degree pair interleavers from the splitting-only ASW target and the
root-crossing target. -/
theorem
    succDegreePairHasCommonInterleaver_nonneg_of_forward_asw_splits_and_rootCrossing
    (hASW : aissenSchoenbergWhitneyForwardSplitsStatement)
    (hcross : PosComboNoCommonSuccDegreeRootCrossingNonnegStatement) :
    PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement :=
  succDegreePairHasCommonInterleaver_nonneg_of_forward_asw_and_rootCrossing
    (aissenSchoenbergWhitneyForwardOrZero_of_splits hASW) hcross

/-- Succ-degree slot data from left-endpoint real-rootedness and the fixed
orientation.  The orientation supplies the root-crossing inequalities. -/
theorem posComboNoCommonSuccDegreeSlotData_of_leftSplits_and_orientation
    (hsplit : PosComboSuccDegreeLeftSplitsNonnegStatement)
    (horient : PosComboNoCommonSuccDegreeOrientationNonnegStatement) :
    PosComboNoCommonSuccDegreeSlotDataNonnegStatement :=
  posComboNoCommonSuccDegreeSlotData_of_leftSplits_and_rootCrossing hsplit
    (posComboNoCommonSuccDegreeRootCrossing_of_orientation horient)

/-- The repaired succ-degree pair-interleaver endpoint follows from
left-endpoint real-rootedness and the fixed orientation. -/
theorem succDegreePairHasCommonInterleaver_nonneg_of_leftSplits_and_orientation
    (hsplit : PosComboSuccDegreeLeftSplitsNonnegStatement)
    (horient : PosComboNoCommonSuccDegreeOrientationNonnegStatement) :
    PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement :=
  succDegreePairHasCommonInterleaver_nonneg_of_leftSplits_and_rootCrossing hsplit
    (posComboNoCommonSuccDegreeRootCrossing_of_orientation horient)

/-- Succ-degree slot data from the PF/ASW left-endpoint route and the fixed
orientation. -/
theorem posComboNoCommonSuccDegreeSlotData_of_forward_asw_and_orientation
    (hASW : aissenSchoenbergWhitneyForwardOrZeroStatement)
    (horient : PosComboNoCommonSuccDegreeOrientationNonnegStatement) :
    PosComboNoCommonSuccDegreeSlotDataNonnegStatement :=
  posComboNoCommonSuccDegreeSlotData_of_forward_asw_and_rootCrossing hASW
    (posComboNoCommonSuccDegreeRootCrossing_of_orientation horient)

/-- Succ-degree slot data from the splitting-only ASW target and the fixed
succ-degree orientation. -/
theorem posComboNoCommonSuccDegreeSlotData_of_forward_asw_splits_and_orientation
    (hASW : aissenSchoenbergWhitneyForwardSplitsStatement)
    (horient : PosComboNoCommonSuccDegreeOrientationNonnegStatement) :
    PosComboNoCommonSuccDegreeSlotDataNonnegStatement :=
  posComboNoCommonSuccDegreeSlotData_of_forward_asw_and_orientation
    (aissenSchoenbergWhitneyForwardOrZero_of_splits hASW) horient

/-- Succ-degree pair interleavers from the PF/ASW left-endpoint route and the
fixed orientation. -/
theorem succDegreePairHasCommonInterleaver_nonneg_of_forward_asw_and_orientation
    (hASW : aissenSchoenbergWhitneyForwardOrZeroStatement)
    (horient : PosComboNoCommonSuccDegreeOrientationNonnegStatement) :
    PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement :=
  succDegreePairHasCommonInterleaver_nonneg_of_forward_asw_and_rootCrossing hASW
    (posComboNoCommonSuccDegreeRootCrossing_of_orientation horient)

/-- Succ-degree pair interleavers from the splitting-only ASW target and the
fixed orientation. -/
theorem succDegreePairHasCommonInterleaver_nonneg_of_forward_asw_splits_and_orientation
    (hASW : aissenSchoenbergWhitneyForwardSplitsStatement)
    (horient : PosComboNoCommonSuccDegreeOrientationNonnegStatement) :
    PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement :=
  succDegreePairHasCommonInterleaver_nonneg_of_forward_asw_and_orientation
    (aissenSchoenbergWhitneyForwardOrZero_of_splits hASW) horient

/-- Honest nonnegative degree-split reduction of the no-common orientation
problem: it is enough to solve the same-degree branch up to orientation
alternative and the succ-degree branch in the forced direction. -/
theorem posComboNoCommonOrientation_of_degreeSplit_and_nonnegCoeffs
    (hsame : PosComboNoCommonSameDegreeOrientationAlternativeNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreeOrientationNonnegStatement)
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g)
    (hdeg_lo : f.natDegree ≤ g.natDegree)
    (hdeg_hi : g.natDegree ≤ f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    Prec f g ∨ Prec g f := by
  have hdeg : g.natDegree = f.natDegree ∨ g.natDegree = f.natDegree + 1 := by lia
  rcases hdeg with hsame_deg | hsucc_deg
  · exact hsame hf_pos hg_pos hfnn hgnn hfg hsame_deg hno
  · exact Or.inl (hsucc hf_pos hg_pos hfnn hgnn hfg hsucc_deg hno)

/-- The same honest degree-split reduction also packages the no-common
all-combinations bridge in the nonnegative regime. -/
theorem allComboRealRooted_of_degreeSplit_and_nonnegCoeffs
    (hsame : PosComboNoCommonSameDegreeOrientationAlternativeNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreeOrientationNonnegStatement)
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g)
    (hdeg_lo : f.natDegree ≤ g.natDegree)
    (hdeg_hi : g.natDegree ≤ f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    AllComboRealRooted f g :=
  allComboRealRooted_of_prec_or_revPrec <|
    posComboNoCommonOrientation_of_degreeSplit_and_nonnegCoeffs
      hsame hsucc hf_pos hg_pos hfnn hgnn hfg hdeg_lo hdeg_hi hno

/-- Affine-family bridge upgraded to the all-combinations conclusion in the
nonnegative-coefficient regime, via `AffineFamily.allComboRealRooted_of_affine_family_nonneg`.
-/
theorem allComboRealRooted_of_affineFamilyBridge_and_nonnegCoeffs
    (haffBridge : PosComboNoCommonAffineFamilyStatement)
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g)
    (hdeg_lo : f.natDegree ≤ g.natDegree)
    (hdeg_hi : g.natDegree ≤ f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    AllComboRealRooted f g := by
  have hf0 : f ≠ 0 := hf_pos.ne_zero
  have hg0 : g ≠ 0 := hg_pos.ne_zero
  have haff :
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        ((((C s * X + C t) * f) + g) ≠ 0 ∧
          (((C s * X + C t) * f) + g).Splits) :=
    fun {s t} hs ht =>
      haffBridge hf_pos hg_pos hfnn hgnn hfg hdeg_lo hdeg_hi hno hs ht
  exact
    allComboRealRooted_of_affine_family_nonneg
      hf0 hg0 hfnn hgnn haff

/-- Coefficient-free common-root reduction for a no-common all-combinations
terminal bridge.  If the no-common close-degree positive-combination case
upgrades to `AllComboRealRooted`, then the same conclusion holds with shared
roots by peeling common linear factors and multiplying them back. -/
theorem allComboRealRooted_of_noCommonBridge_ordered
    (hterminal : PosComboNoCommonToAllComboBridgeStatement)
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfg : PosComboRealRooted f g)
    (hdeg_lo : f.natDegree ≤ g.natDegree)
    (hdeg_hi : g.natDegree ≤ f.natDegree + 1) :
    AllComboRealRooted f g := by
  refine
    Nat.strong_induction_on
      (p := fun n =>
        ∀ {f g : ℝ[X]},
          f.natDegree = n →
          HasPosLeadingCoeff f →
          HasPosLeadingCoeff g →
          PosComboRealRooted f g →
          f.natDegree ≤ g.natDegree →
          g.natDegree ≤ f.natDegree + 1 →
          AllComboRealRooted f g)
      f.natDegree ?_ rfl hf_pos hg_pos hfg hdeg_lo hdeg_hi
  intro n ih f g hfdeg hf_pos hg_pos hfg hdeg_lo hdeg_hi
  by_cases hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r
  · exact hterminal hf_pos hg_pos hfg hdeg_lo hdeg_hi hno
  · push Not at hno
    rcases hno with ⟨r, hrf, hrg⟩
    obtain ⟨qf, qg, hqf, hqg, hqfg, hqf_pos, hqg_pos, hqdeg_lo, hqdeg_hi⟩ :=
      PosComboRealRooted.common_root_reduction_data
        hfg hf_pos hg_pos hdeg_lo hdeg_hi hrf hrg
    have hqf_deg_lt : qf.natDegree < n := by
      rw [← hfdeg, hqf, natDegree_mul (X_sub_C_ne_zero r) hqf_pos.ne_zero,
        natDegree_X_sub_C]
      lia
    have hall_q : AllComboRealRooted qf qg :=
      ih qf.natDegree hqf_deg_lt rfl hqf_pos hqg_pos hqfg hqdeg_lo hqdeg_hi
    have hall_mul : AllComboRealRooted ((X - C r) * qf) ((X - C r) * qg) :=
      allComboRealRooted_mul_common_factor (isRealRooted_X_sub_C r).2 hall_q
    simpa [hqf, hqg] using hall_mul

/-- The no-common all-combinations bridge implies the compatible succ-degree
all-combinations target, with common roots handled by
`allComboRealRooted_of_noCommonBridge_ordered`. -/
theorem compatibleSuccDegreeAllCombo_of_allComboBridge
    (hallBridge : PosComboNoCommonToAllComboBridgeStatement) :
    CompatibleSuccDegreeAllComboStatement := by
  intro f g hcomp hf_pos hg_pos hdeg _hf_split
  exact
    allComboRealRooted_of_noCommonBridge_ordered
      hallBridge hf_pos hg_pos
      (hcomp.toPosComboRealRooted hf_pos hg_pos) (by lia) (by lia)

/-- The no-common all-combinations bridge also implies the nonnegative
negative right-pencil target. -/
theorem compatibleSuccDegreeNegativeRightFamilyNonneg_of_allComboBridge
    (hallBridge : PosComboNoCommonToAllComboBridgeStatement) :
    CompatibleSuccDegreeNegativeRightFamilyNonnegStatement :=
  compatibleSuccDegreeNegativeRightFamilyNonneg_of_allCombo
    (compatibleSuccDegreeAllCombo_of_allComboBridge hallBridge)

private lemma prec_or_revPrec_of_allComboRealRooted_ordered
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hall : AllComboRealRooted f g)
    (hdeg_lo : f.natDegree ≤ g.natDegree)
    (hdeg_hi : g.natDegree ≤ f.natDegree + 1) :
    Prec f g ∨ Prec g f := by
  have hf0 : f ≠ 0 := hf_pos.ne_zero
  have hg0 : g ≠ 0 := hg_pos.ne_zero
  have hf_rr : (f ≠ 0 ∧ f.Splits) := hall.isRealRooted_left hf0
  have hg_rr : (g ≠ 0 ∧ g.Splits) := hall.isRealRooted_right hg0
  have hdeg : f.natDegree + 1 = g.natDegree ∨ f.natDegree = g.natDegree := by
    lia
  exact prec_of_allComboRealRooted hf_rr.1 hf_rr.2 hg_rr.1 hg_rr.2 hall hdeg

/-- The same affine-family bridge also yields the no-common orientation step,
since `AllComboRealRooted` can be fed into the completed Obreschkoff converse.
-/
theorem posComboNoCommonOrientation_of_affineFamilyBridge_and_nonnegCoeffs
    (haffBridge : PosComboNoCommonAffineFamilyStatement)
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g)
    (hdeg_lo : f.natDegree ≤ g.natDegree)
    (hdeg_hi : g.natDegree ≤ f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    Prec f g ∨ Prec g f := by
  have hall : AllComboRealRooted f g :=
    allComboRealRooted_of_affineFamilyBridge_and_nonnegCoeffs
      haffBridge hf_pos hg_pos hfnn hgnn hfg hdeg_lo hdeg_hi hno
  exact
    prec_or_revPrec_of_allComboRealRooted_ordered
      hf_pos hg_pos hall hdeg_lo hdeg_hi

private lemma hasNonnegCoeffs_quotient_add_right_of_common_root
    {f g qf qg : ℝ[X]} {r μ : ℝ}
    (hfg : PosComboRealRooted f g)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (hqf : f = (X - C r) * qf)
    (hqg : g = (X - C r) * qg)
    (hμ : 0 < μ) :
    HasNonnegCoeffs (qf + C μ * qg) := by
  let p : ℝ[X] := f + C μ * g
  have hp_rr : (p ≠ 0 ∧ p.Splits) := by
    simpa [p] using hfg.isRealRooted_add_right hμ
  have hp_nn : HasNonnegCoeffs p := by
    dsimp [p]
    exact hfnn.add (nonnegCoeffs_C_mul hμ.le hgnn)
  have hp_eq : p = (X - C r) * (qf + C μ * qg) := by grind
  have hq_ne : qf + C μ * qg ≠ 0 := by simp_all
  have hq_rr : ((qf + C μ * qg) ≠ 0 ∧ (qf + C μ * qg).Splits) :=
    isRealRooted_of_dvd hp_rr.1 hp_rr.2 hq_ne
      ⟨X - C r, by grind⟩
  have hp_pos : HasPosLeadingCoeff p := hp_nn.pos_leadingCoeff hp_rr.1
  have hq_pos : HasPosLeadingCoeff (qf + C μ * qg) :=
    hasPosLeadingCoeff_of_X_sub_C_mul (by simpa [hp_eq] using hp_pos)
  exact
    hasNonnegCoeffs_of_dvd_of_isRealRooted_of_hasPosLeadingCoeff
      hp_rr.1 hp_rr.2 hp_nn hq_rr.1 hq_rr.2 hq_pos
      ⟨X - C r, by grind⟩

private lemma common_root_reduction_data_of_posCombo_nonneg
    {f g : ℝ[X]} {r : ℝ}
    (hfg : PosComboRealRooted f g)
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (hdeg_lo : f.natDegree ≤ g.natDegree)
    (hdeg_hi : g.natDegree ≤ f.natDegree + 1)
    (hrf : f.IsRoot r)
    (hrg : g.IsRoot r) :
    ∃ qf qg,
      f = (X - C r) * qf ∧
      g = (X - C r) * qg ∧
      PosComboRealRooted qf qg ∧
      HasNonnegCoeffs qf ∧
      HasNonnegCoeffs qg ∧
      qf ≠ 0 ∧
      qg ≠ 0 ∧
      HasPosLeadingCoeff qf ∧
      HasPosLeadingCoeff qg ∧
      qf.natDegree ≤ qg.natDegree ∧
      qg.natDegree ≤ qf.natDegree + 1 := by
  obtain ⟨qf, hqf⟩ := dvd_iff_isRoot.mpr hrf
  obtain ⟨qg, hqg⟩ := dvd_iff_isRoot.mpr hrg
  have hqfg : PosComboRealRooted qf qg :=
    PosComboRealRooted.of_mul_X_sub_C (r := r) (by lia)
  have hf0 : f ≠ 0 := hf_pos.ne_zero
  have hg0 : g ≠ 0 := hg_pos.ne_zero
  have hqf0 : qf ≠ 0 := by simp_all
  have hqg0 : qg ≠ 0 := by simp_all
  have hqf_nn : HasNonnegCoeffs qf :=
    coeff_nonneg_of_add_C_mul_nonneg_forall (f := qf) (g := qg) fun {μ} hμ =>
      hasNonnegCoeffs_quotient_add_right_of_common_root
        hfg hfnn hgnn hqf hqg hμ
  have hqg_nn : HasNonnegCoeffs qg :=
    coeff_nonneg_of_add_C_mul_nonneg_forall (f := qg) (g := qf) fun {μ} hμ => by
      simpa [add_comm] using
      hasNonnegCoeffs_quotient_add_right_of_common_root
        (f := g) (g := f) (qf := qg) (qg := qf) (r := r)
        (PosComboRealRooted.comm hfg) hgnn hfnn hqg hqf hμ
  have hqf_pos : HasPosLeadingCoeff qf := hqf_nn.pos_leadingCoeff hqf0
  have hqg_pos : HasPosLeadingCoeff qg := hqg_nn.pos_leadingCoeff hqg0
  have hqdeg_lo : qf.natDegree ≤ qg.natDegree := by
    rw [hqf, hqg, natDegree_mul (X_sub_C_ne_zero r) hqf0, natDegree_X_sub_C,
      natDegree_mul (X_sub_C_ne_zero r) hqg0, natDegree_X_sub_C] at hdeg_lo
    lia
  have hqdeg_hi : qg.natDegree ≤ qf.natDegree + 1 := by
    rw [hqf, hqg, natDegree_mul (X_sub_C_ne_zero r) hqf0, natDegree_X_sub_C,
      natDegree_mul (X_sub_C_ne_zero r) hqg0, natDegree_X_sub_C] at hdeg_hi
    lia
  exact
    ⟨qf, qg, hqf, hqg, hqfg, hqf_nn, hqg_nn, hqf0, hqg0, hqf_pos, hqg_pos,
      hqdeg_lo, hqdeg_hi⟩

/-- Repaired no-common degree-split reduction of the common-interleaver bridge
in the nonnegative regime: both same-degree and succ-degree branches are stated
directly with the common-right-interleaver conclusion needed downstream. -/
theorem posComboNoCommonPairHasCommonInterleaver_of_pairDegreeSplit_and_nonnegCoeffs
    (hsucc : PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement)
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g)
    (hdeg_lo : f.natDegree ≤ g.natDegree)
    (hdeg_hi : g.natDegree ≤ f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    ∃ h : ℝ[X], Prec f h ∧ Prec g h := by
  have hdeg : g.natDegree = f.natDegree ∨ g.natDegree = f.natDegree + 1 := by lia
  rcases hdeg with hsame_deg | hsucc_deg
  · exact PosComboNoCommonSameDegreePairHasCommonInterleaverNonneg hf_pos hg_pos hfnn hgnn hfg hsame_deg hno
  · exact hsucc hf_pos hg_pos hfnn hgnn hfg hsucc_deg hno

/-- Honest no-common degree-split reduction of the common-interleaver bridge
in the nonnegative regime: the same-degree branch only needs the Obreschkoff
alternative, while the succ-degree branch only asks for a common interleaver.
-/
theorem posComboNoCommonPairHasCommonInterleaver_of_degreeSplit_and_nonnegCoeffs
    (hsame : PosComboNoCommonSameDegreeOrientationAlternativeNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement)
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g)
    (hdeg_lo : f.natDegree ≤ g.natDegree)
    (hdeg_hi : g.natDegree ≤ f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    ∃ h : ℝ[X], Prec f h ∧ Prec g h :=
  posComboNoCommonPairHasCommonInterleaver_of_pairDegreeSplit_and_nonnegCoeffs hsucc hf_pos hg_pos hfnn hgnn hfg hdeg_lo hdeg_hi hno

/-- Repaired no-common degree-split reduction with the succ-degree branch
discharged by the affine-family bridge.  After this reduction, the only
remaining local branch is the same-degree common-interleaver statement. -/
theorem posComboNoCommonPairHasCommonInterleaver_of_sameDegreePair_and_affineFamily_nonneg
    (haffBridge : PosComboNoCommonAffineFamilyStatement)
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g)
    (hdeg_lo : f.natDegree ≤ g.natDegree)
    (hdeg_hi : g.natDegree ≤ f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    ∃ h : ℝ[X], Prec f h ∧ Prec g h :=
  posComboNoCommonPairHasCommonInterleaver_of_pairDegreeSplit_and_nonnegCoeffs
    (posComboNoCommonSuccDegreePairHasCommonInterleaver_of_affineFamily haffBridge)
    hf_pos hg_pos hfnn hgnn hfg hdeg_lo hdeg_hi hno

private theorem posComboPairHasCommonInterleaver_of_noCommonPairBridge_and_nonnegCoeffs_ordered
    (hterminal :
      ∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        f.natDegree ≤ g.natDegree →
        g.natDegree ≤ f.natDegree + 1 →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        ∃ h : ℝ[X], Prec f h ∧ Prec g h)
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g)
    (hdeg_lo : f.natDegree ≤ g.natDegree)
    (hdeg_hi : g.natDegree ≤ f.natDegree + 1) :
    ∃ h : ℝ[X], Prec f h ∧ Prec g h := by
  refine
    Nat.strong_induction_on
      (p := fun n =>
        ∀ {f g : ℝ[X]},
          f.natDegree = n →
          HasPosLeadingCoeff f →
          HasPosLeadingCoeff g →
          HasNonnegCoeffs f →
          HasNonnegCoeffs g →
          PosComboRealRooted f g →
          f.natDegree ≤ g.natDegree →
          g.natDegree ≤ f.natDegree + 1 →
          ∃ h : ℝ[X], Prec f h ∧ Prec g h)
      f.natDegree ?_ rfl hf_pos hg_pos hfnn hgnn hfg hdeg_lo hdeg_hi
  intro n ih f g hfdeg hf_pos hg_pos hfnn hgnn hfg hdeg_lo hdeg_hi
  by_cases hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r
  · exact
      hterminal hf_pos hg_pos hfnn hgnn hfg hdeg_lo hdeg_hi hno
  · push Not at hno
    rcases hno with ⟨r, hrf, hrg⟩
    obtain ⟨qf, qg, hqf, hqg, hqfg, hqf_nn, hqg_nn, hqf0, hqg0,
      hqf_pos, hqg_pos, hqdeg_lo, hqdeg_hi⟩ :=
      common_root_reduction_data_of_posCombo_nonneg
        hfg hf_pos hg_pos hfnn hgnn hdeg_lo hdeg_hi hrf hrg
    have hqf_deg_lt : qf.natDegree < n := by
      rw [← hfdeg, hqf, natDegree_mul (X_sub_C_ne_zero r) hqf0, natDegree_X_sub_C]
      lia
    rcases
        ih qf.natDegree hqf_deg_lt rfl
          hqf_pos hqg_pos hqf_nn hqg_nn hqfg hqdeg_lo hqdeg_hi with
      ⟨h, hqf_prec, hqg_prec⟩
    refine ⟨(X - C r) * h, ?_, ?_⟩
    · simpa [hqf] using
        prec_mul_common_factor (isRealRooted_X_sub_C r).1 (isRealRooted_X_sub_C r).2 hqf_prec
    · simpa [hqg] using
        prec_mul_common_factor (isRealRooted_X_sub_C r).1 (isRealRooted_X_sub_C r).2 hqg_prec

/-- Degree-bounded common-root reduction for the nonnegative
common-interleaver bridge.  Given a terminal endpoint that produces a common
right interleaver for no-common pairs whose right degree is at most `N`,
peeling common linear factors by strong induction on `f.natDegree` extends the
conclusion to all nonnegative positive-combination pairs of right degree at
most `N`, common roots included. -/
theorem posComboPairHasCommonInterleaver_of_natDegree_le_reduction
    {N : ℕ}
    (hterminal :
      ∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        f.natDegree ≤ g.natDegree →
        g.natDegree ≤ f.natDegree + 1 →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        g.natDegree ≤ N →
        ∃ h : ℝ[X], Prec f h ∧ Prec g h)
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g)
    (hdeg_lo : f.natDegree ≤ g.natDegree)
    (hdeg_hi : g.natDegree ≤ f.natDegree + 1)
    (hgdeg : g.natDegree ≤ N) :
    ∃ h : ℝ[X], Prec f h ∧ Prec g h := by
  refine
    Nat.strong_induction_on
      (p := fun n =>
        ∀ {f g : ℝ[X]},
          f.natDegree = n →
          HasPosLeadingCoeff f →
          HasPosLeadingCoeff g →
          HasNonnegCoeffs f →
          HasNonnegCoeffs g →
          PosComboRealRooted f g →
          f.natDegree ≤ g.natDegree →
          g.natDegree ≤ f.natDegree + 1 →
          g.natDegree ≤ N →
          ∃ h : ℝ[X], Prec f h ∧ Prec g h)
      f.natDegree ?_ rfl hf_pos hg_pos hfnn hgnn hfg hdeg_lo hdeg_hi hgdeg
  intro n ih f g hfdeg hf_pos hg_pos hfnn hgnn hfg hdeg_lo hdeg_hi hgdeg
  by_cases hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r
  · exact hterminal hf_pos hg_pos hfnn hgnn hfg hdeg_lo hdeg_hi hno hgdeg
  · push Not at hno
    rcases hno with ⟨r, hrf, hrg⟩
    obtain ⟨qf, qg, hqf, hqg, hqfg, hqf_nn, hqg_nn, hqf0, hqg0,
      hqf_pos, hqg_pos, hqdeg_lo, hqdeg_hi⟩ :=
      common_root_reduction_data_of_posCombo_nonneg
        hfg hf_pos hg_pos hfnn hgnn hdeg_lo hdeg_hi hrf hrg
    have hqf_deg_lt : qf.natDegree < n := by
      rw [← hfdeg, hqf, natDegree_mul (X_sub_C_ne_zero r) hqf0, natDegree_X_sub_C]
      lia
    have hqg_deg_le : qg.natDegree ≤ N := by
      have hle : qg.natDegree ≤ g.natDegree := by
        rw [hqg, natDegree_mul (X_sub_C_ne_zero r) hqg0, natDegree_X_sub_C]
        lia
      exact le_trans hle hgdeg
    rcases
        ih qf.natDegree hqf_deg_lt rfl
          hqf_pos hqg_pos hqf_nn hqg_nn hqfg hqdeg_lo hqdeg_hi hqg_deg_le with
      ⟨h, hqf_prec, hqg_prec⟩
    refine ⟨(X - C r) * h, ?_, ?_⟩
    · simpa [hqf] using
        prec_mul_common_factor (isRealRooted_X_sub_C r).1
          (isRealRooted_X_sub_C r).2 hqf_prec
    · simpa [hqg] using
        prec_mul_common_factor (isRealRooted_X_sub_C r).1
          (isRealRooted_X_sub_C r).2 hqg_prec

/-- Unordered degree-bounded common-root reduction for the nonnegative
common-interleaver bridge.  If a no-common terminal endpoint handles every
ordered close-degree pair whose right degree is at most `N`, then the same
conclusion holds for every nonnegative positive-combination pair whose two
degrees are both at most `N`. -/
theorem posComboPairHasCommonInterleaver_of_natDegree_le_reduction_unordered
    {N : ℕ}
    (hterminal :
      ∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        f.natDegree ≤ g.natDegree →
        g.natDegree ≤ f.natDegree + 1 →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        g.natDegree ≤ N →
        ∃ h : ℝ[X], Prec f h ∧ Prec g h)
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g)
    (hfdeg : f.natDegree ≤ N)
    (hgdeg : g.natDegree ≤ N) :
    ∃ h : ℝ[X], Prec f h ∧ Prec g h := by
  obtain ⟨hclose_left, hclose_right⟩ :=
    natDegree_close_of_posComboRealRooted_of_nonnegCoeffs
      hfg hf_pos.ne_zero hg_pos.ne_zero hfnn hgnn
  by_cases hdeg : f.natDegree ≤ g.natDegree
  · exact
      posComboPairHasCommonInterleaver_of_natDegree_le_reduction
        (N := N) hterminal hf_pos hg_pos hfnn hgnn hfg hdeg hclose_right hgdeg
  · have hdeg' : g.natDegree ≤ f.natDegree := le_of_not_ge hdeg
    rcases
        posComboPairHasCommonInterleaver_of_natDegree_le_reduction
          (N := N) hterminal hg_pos hf_pos hgnn hfnn
          (PosComboRealRooted.comm hfg) hdeg' hclose_left hfdeg with
      ⟨h, hg_prec, hf_prec⟩
    exact ⟨h, hf_prec, hg_prec⟩

/-- Ordered nonnegative-coefficient degree-`≤ 2` pair endpoint.  Shared roots
are factored out recursively, and the terminal no-common-root case is the
checked low-degree root-crossing endpoint. -/
theorem posComboPairHasCommonInterleaver_nonneg_of_natDegree_le_two_ordered
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g)
    (hdeg_lo : f.natDegree ≤ g.natDegree)
    (hdeg_hi : g.natDegree ≤ f.natDegree + 1)
    (hgdeg : g.natDegree ≤ 2) :
    ∃ h : ℝ[X], Prec f h ∧ Prec g h :=
  posComboPairHasCommonInterleaver_of_natDegree_le_reduction
    (N := 2)
    (fun {_f _g} hf_pos hg_pos hfnn hgnn hfg hdeg_lo hdeg_hi hno hgdeg =>
      posComboNoCommonPairHasCommonInterleaver_of_natDegree_le_two
        hf_pos hg_pos hfnn hgnn hfg hdeg_lo hdeg_hi hno hgdeg)
    hf_pos hg_pos hfnn hgnn hfg hdeg_lo hdeg_hi hgdeg

/-- Nonnegative-coefficient degree-`≤ 2` pair endpoint, with no degree order
assumption. -/
theorem posComboPairHasCommonInterleaver_nonneg_of_natDegree_le_two
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g)
    (hfdeg : f.natDegree ≤ 2)
    (hgdeg : g.natDegree ≤ 2) :
    ∃ h : ℝ[X], Prec f h ∧ Prec g h :=
  posComboPairHasCommonInterleaver_of_natDegree_le_reduction_unordered
    (N := 2)
    (fun {_f _g} hf_pos hg_pos hfnn hgnn hfg hdeg_lo hdeg_hi hno hgdeg =>
      posComboNoCommonPairHasCommonInterleaver_of_natDegree_le_two
        hf_pos hg_pos hfnn hgnn hfg hdeg_lo hdeg_hi hno hgdeg)
    hf_pos hg_pos hfnn hgnn hfg hfdeg hgdeg

private theorem posComboPairHasCommonInterleaver_of_degreeSplit_and_nonnegCoeffs_ordered
    (hsame : PosComboNoCommonSameDegreeOrientationAlternativeNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement)
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g)
    (hdeg_lo : f.natDegree ≤ g.natDegree)
    (hdeg_hi : g.natDegree ≤ f.natDegree + 1) :
    ∃ h : ℝ[X], Prec f h ∧ Prec g h :=
  posComboPairHasCommonInterleaver_of_noCommonPairBridge_and_nonnegCoeffs_ordered
    (fun {f g} hf_pos hg_pos hfnn hgnn hfg hdeg_lo hdeg_hi hno =>
      posComboNoCommonPairHasCommonInterleaver_of_degreeSplit_and_nonnegCoeffs
        hsame hsucc (f := f) (g := g)
        hf_pos hg_pos hfnn hgnn hfg hdeg_lo hdeg_hi hno)
    hf_pos hg_pos hfnn hgnn hfg hdeg_lo hdeg_hi

private theorem posComboPairHasCommonInterleaver_of_pairDegreeSplit_and_nonnegCoeffs_ordered
    (hsucc : PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement)
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g)
    (hdeg_lo : f.natDegree ≤ g.natDegree)
    (hdeg_hi : g.natDegree ≤ f.natDegree + 1) :
    ∃ h : ℝ[X], Prec f h ∧ Prec g h :=
  posComboPairHasCommonInterleaver_of_noCommonPairBridge_and_nonnegCoeffs_ordered
    (fun {f g} hf_pos hg_pos hfnn hgnn hfg hdeg_lo hdeg_hi hno =>
      posComboNoCommonPairHasCommonInterleaver_of_pairDegreeSplit_and_nonnegCoeffs hsucc (f := f) (g := g)
        hf_pos hg_pos hfnn hgnn hfg hdeg_lo hdeg_hi hno)
    hf_pos hg_pos hfnn hgnn hfg hdeg_lo hdeg_hi

private theorem allComboRealRooted_of_noCommonBridge_and_nonnegCoeffs_ordered
    (hterminal :
      ∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        f.natDegree ≤ g.natDegree →
        g.natDegree ≤ f.natDegree + 1 →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        AllComboRealRooted f g)
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g)
    (hdeg_lo : f.natDegree ≤ g.natDegree)
    (hdeg_hi : g.natDegree ≤ f.natDegree + 1) :
    AllComboRealRooted f g := by
  refine
    Nat.strong_induction_on
      (p := fun n =>
        ∀ {f g : ℝ[X]},
          f.natDegree = n →
          HasPosLeadingCoeff f →
          HasPosLeadingCoeff g →
          HasNonnegCoeffs f →
          HasNonnegCoeffs g →
          PosComboRealRooted f g →
          f.natDegree ≤ g.natDegree →
          g.natDegree ≤ f.natDegree + 1 →
          AllComboRealRooted f g)
      f.natDegree ?_ rfl hf_pos hg_pos hfnn hgnn hfg hdeg_lo hdeg_hi
  intro n ih f g hfdeg hf_pos hg_pos hfnn hgnn hfg hdeg_lo hdeg_hi
  by_cases hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r
  · exact
      hterminal hf_pos hg_pos hfnn hgnn hfg hdeg_lo hdeg_hi hno
  · push Not at hno
    rcases hno with ⟨r, hrf, hrg⟩
    obtain ⟨qf, qg, hqf, hqg, hqfg, hqf_nn, hqg_nn, hqf0, hqg0,
      hqf_pos, hqg_pos, hqdeg_lo, hqdeg_hi⟩ :=
      common_root_reduction_data_of_posCombo_nonneg
        hfg hf_pos hg_pos hfnn hgnn hdeg_lo hdeg_hi hrf hrg
    have hqf_deg_lt : qf.natDegree < n := by
      rw [← hfdeg, hqf, natDegree_mul (X_sub_C_ne_zero r) hqf0, natDegree_X_sub_C]
      lia
    have hall_q : AllComboRealRooted qf qg :=
      ih qf.natDegree hqf_deg_lt rfl
        hqf_pos hqg_pos hqf_nn hqg_nn hqfg hqdeg_lo hqdeg_hi
    have hall_mul : AllComboRealRooted ((X - C r) * qf) ((X - C r) * qg) :=
      allComboRealRooted_mul_common_factor (isRealRooted_X_sub_C r).2 hall_q
    lia

private theorem allComboRealRooted_of_degreeSplit_and_nonnegCoeffs_ordered
    (hsame : PosComboNoCommonSameDegreeOrientationAlternativeNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreeOrientationNonnegStatement)
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g)
    (hdeg_lo : f.natDegree ≤ g.natDegree)
    (hdeg_hi : g.natDegree ≤ f.natDegree + 1) :
    AllComboRealRooted f g :=
  allComboRealRooted_of_noCommonBridge_and_nonnegCoeffs_ordered
    (fun {f g} hf_pos hg_pos hfnn hgnn hfg hdeg_lo hdeg_hi hno =>
      allComboRealRooted_of_degreeSplit_and_nonnegCoeffs
        hsame hsucc (f := f) (g := g)
        hf_pos hg_pos hfnn hgnn hfg hdeg_lo hdeg_hi hno)
    hf_pos hg_pos hfnn hgnn hfg hdeg_lo hdeg_hi

/-- An ordered all-combinations bridge plus the nonnegative degree-closeness
theorem gives the unordered all-combinations bridge. -/
theorem allComboRealRooted_of_orderedBridge_and_nonnegCoeffs
    (hordered :
      ∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        f.natDegree ≤ g.natDegree →
        g.natDegree ≤ f.natDegree + 1 →
        AllComboRealRooted f g)
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g) :
    AllComboRealRooted f g := by
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
    exact
      allComboRealRooted_comm <|
        hordered hg_pos hf_pos hgnn hfnn (PosComboRealRooted.comm hfg) hdeg' hclose.1

/-- Recursive upgrade of the honest degree-split no-common package to a full
all-combinations result in the nonnegative-coefficient regime. Shared roots are
factored out until one reaches the terminal no-common quotient, where the
same-degree alternative or succ-degree orientation hypothesis is applied. -/
theorem allComboRealRooted_of_posCombo_and_degreeSplit_and_nonnegCoeffs
    (hsame : PosComboNoCommonSameDegreeOrientationAlternativeNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreeOrientationNonnegStatement)
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g) :
    AllComboRealRooted f g :=
  allComboRealRooted_of_orderedBridge_and_nonnegCoeffs
    (fun {f g} hf_pos hg_pos hfnn hgnn hfg hdeg_lo hdeg_hi =>
      allComboRealRooted_of_degreeSplit_and_nonnegCoeffs_ordered
        (f := f) (g := g) hsame hsucc hf_pos hg_pos hfnn hgnn hfg hdeg_lo hdeg_hi)
    hf_pos hg_pos hfnn hgnn hfg

/-- The honest same-degree/succ-degree orientation split supplies the
nonnegative-coefficient negative right-pencil target by upgrading the
positive-combination pair to all-combinations real-rootedness. -/
theorem compatibleSuccDegreeNegativeRightFamilyNonneg_of_degreeSplit
    (hsame : PosComboNoCommonSameDegreeOrientationAlternativeNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreeOrientationNonnegStatement) :
    CompatibleSuccDegreeNegativeRightFamilyNonnegStatement := by
  intro f g hcomp hf_pos hg_pos hfnn hgnn _ _ μ _
  have hall : AllComboRealRooted f g :=
    allComboRealRooted_of_posCombo_and_degreeSplit_and_nonnegCoeffs
      hsame hsucc hf_pos hg_pos hfnn hgnn
      (hcomp.toPosComboRealRooted hf_pos hg_pos)
  simpa using hall 1 μ

/-- In the nonnegative-coefficient regime, all-combinations real-rootedness
implies the Obreschkoff orientation alternative. -/
theorem posComboOrientation_of_allComboRealRooted_and_nonnegCoeffs
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g)
    (hall : AllComboRealRooted f g) :
    Prec f g ∨ Prec g f := by
  have hf0 : f ≠ 0 := hf_pos.ne_zero
  have hg0 : g ≠ 0 := hg_pos.ne_zero
  have hf_rr : (f ≠ 0 ∧ f.Splits) := hall.isRealRooted_left hf0
  have hg_rr : (g ≠ 0 ∧ g.Splits) := hall.isRealRooted_right hg0
  have hclose :
      f.natDegree ≤ g.natDegree + 1 ∧
        g.natDegree ≤ f.natDegree + 1 :=
    natDegree_close_of_posComboRealRooted_of_nonnegCoeffs
      hfg hf0 hg0 hfnn hgnn
  by_cases hdeg : f.natDegree ≤ g.natDegree
  · have hdeg' : f.natDegree + 1 = g.natDegree ∨ f.natDegree = g.natDegree := by
      lia
    exact prec_of_allComboRealRooted hf_rr.1 hf_rr.2 hg_rr.1 hg_rr.2 hall hdeg'
  · have hdeg' : g.natDegree ≤ f.natDegree := le_of_not_ge hdeg
    have hdeg'' : g.natDegree + 1 = f.natDegree ∨ g.natDegree = f.natDegree := by
      lia
    have hprec' : Prec g f ∨ Prec f g :=
      prec_of_allComboRealRooted hg_rr.1 hg_rr.2 hf_rr.1 hf_rr.2
        (allComboRealRooted_comm hall) hdeg''
    exact Or.symm hprec'

/-- The honest degree-split package therefore yields the full Obreschkoff
orientation alternative for every positive-combination pair with nonnegative
coefficients, not just in the terminal no-common case. -/
theorem posComboOrientation_of_posCombo_and_degreeSplit_and_nonnegCoeffs
    (hsame : PosComboNoCommonSameDegreeOrientationAlternativeNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreeOrientationNonnegStatement)
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g) :
    Prec f g ∨ Prec g f := by
  have hall : AllComboRealRooted f g :=
    allComboRealRooted_of_posCombo_and_degreeSplit_and_nonnegCoeffs
      hsame hsucc hf_pos hg_pos hfnn hgnn hfg
  exact
    posComboOrientation_of_allComboRealRooted_and_nonnegCoeffs
      hf_pos hg_pos hfnn hgnn hfg hall

private theorem allComboRealRooted_of_affineFamilyBridge_and_nonnegCoeffs_ordered
    (haffBridge : PosComboNoCommonAffineFamilyStatement)
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g)
    (hdeg_lo : f.natDegree ≤ g.natDegree)
    (hdeg_hi : g.natDegree ≤ f.natDegree + 1) :
    AllComboRealRooted f g :=
  allComboRealRooted_of_noCommonBridge_and_nonnegCoeffs_ordered
    (fun {f g} hf_pos hg_pos hfnn hgnn hfg hdeg_lo hdeg_hi hno =>
      allComboRealRooted_of_affineFamilyBridge_and_nonnegCoeffs
        haffBridge (f := f) (g := g)
        hf_pos hg_pos hfnn hgnn hfg hdeg_lo hdeg_hi hno)
    hf_pos hg_pos hfnn hgnn hfg hdeg_lo hdeg_hi

/-- Recursive upgrade of the affine-family no-common bridge to a full
all-combinations result in the nonnegative-coefficient regime. Shared roots are
factored out using the positive-combination recursion, and the bridge is only
used at the terminal no-common quotient. -/
theorem allComboRealRooted_of_posCombo_and_affineFamilyBridge_and_nonnegCoeffs
    (haffBridge : PosComboNoCommonAffineFamilyStatement)
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g) :
    AllComboRealRooted f g :=
  allComboRealRooted_of_orderedBridge_and_nonnegCoeffs
    (fun {f g} hf_pos hg_pos hfnn hgnn hfg hdeg_lo hdeg_hi =>
      allComboRealRooted_of_affineFamilyBridge_and_nonnegCoeffs_ordered
        (f := f) (g := g) haffBridge hf_pos hg_pos hfnn hgnn hfg hdeg_lo hdeg_hi)
    hf_pos hg_pos hfnn hgnn hfg

/-- The affine-family bridge supplies the nonnegative-coefficient negative
right-pencil target by upgrading the positive-combination pair to
all-combinations real-rootedness. -/
theorem compatibleSuccDegreeNegativeRightFamilyNonneg_of_affineFamilyBridge
    (haffBridge : PosComboNoCommonAffineFamilyStatement) :
    CompatibleSuccDegreeNegativeRightFamilyNonnegStatement := by
  intro f g hcomp hf_pos hg_pos hfnn hgnn _ _ μ _
  have hall : AllComboRealRooted f g :=
    allComboRealRooted_of_posCombo_and_affineFamilyBridge_and_nonnegCoeffs
      haffBridge hf_pos hg_pos hfnn hgnn
      (hcomp.toPosComboRealRooted hf_pos hg_pos)
  simpa using hall 1 μ

/-- The affine-family bridge therefore yields the full Obreschkoff orientation
alternative for every positive-combination pair with nonnegative coefficients,
not just the no-common case. -/
theorem posComboOrientation_of_affineFamilyBridge_and_nonnegCoeffs
    (haffBridge : PosComboNoCommonAffineFamilyStatement)
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g) :
    Prec f g ∨ Prec g f := by
  have hall : AllComboRealRooted f g :=
    allComboRealRooted_of_posCombo_and_affineFamilyBridge_and_nonnegCoeffs
      haffBridge hf_pos hg_pos hfnn hgnn hfg
  exact
    posComboOrientation_of_allComboRealRooted_and_nonnegCoeffs
      hf_pos hg_pos hfnn hgnn hfg hall

/-- The boundary-right-pair orientation statement already yields the full
all-combinations conclusion in the nonnegative-coefficient regime, by first
recovering the affine-family hypothesis and then running the common-root
recursion packaged above. -/
theorem allComboRealRooted_of_posCombo_and_boundaryRightPairOrientation_and_nonnegCoeffs
    (hboundary : PosComboNoCommonBoundaryRightPairOrientationStatement)
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g) :
    AllComboRealRooted f g :=
  allComboRealRooted_of_posCombo_and_affineFamilyBridge_and_nonnegCoeffs
    (posComboNoCommonAffineFamily_of_boundaryRightPairOrientation hboundary)
    hf_pos hg_pos hfnn hgnn hfg

/-- The boundary-right-pair orientation bridge supplies the
nonnegative-coefficient negative right-pencil target through the affine-family
bridge. -/
theorem compatibleSuccDegreeNegativeRightFamilyNonneg_of_boundaryRightPairOrientation
    (hboundary : PosComboNoCommonBoundaryRightPairOrientationStatement) :
    CompatibleSuccDegreeNegativeRightFamilyNonnegStatement :=
  compatibleSuccDegreeNegativeRightFamilyNonneg_of_affineFamilyBridge
    (posComboNoCommonAffineFamily_of_boundaryRightPairOrientation hboundary)

/-- Consequently, the same boundary-right-pair orientation input already gives
the full Obreschkoff orientation alternative for every positive-combination
pair with nonnegative coefficients. -/
theorem posComboOrientation_of_boundaryRightPairOrientation_and_nonnegCoeffs
    (hboundary : PosComboNoCommonBoundaryRightPairOrientationStatement)
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g) :
    Prec f g ∨ Prec g f :=
  posComboOrientation_of_affineFamilyBridge_and_nonnegCoeffs
    (posComboNoCommonAffineFamily_of_boundaryRightPairOrientation hboundary)
    hf_pos hg_pos hfnn hgnn hfg

/-- The stronger boundary-right-pair hypothesis already contains the honest
same-degree no-common branch in the nonnegative regime. -/
theorem
    boundaryRightPairOrientation_implies_sameDegreeOrientationAlternative_nonneg
    (hboundary : PosComboNoCommonBoundaryRightPairOrientationStatement) :
    PosComboNoCommonSameDegreeOrientationAlternativeNonnegStatement :=
  fun {_ _} hf_pos hg_pos hfnn hgnn hfg _ _ =>
    posComboOrientation_of_boundaryRightPairOrientation_and_nonnegCoeffs
      hboundary hf_pos hg_pos hfnn hgnn hfg

/-- The stronger boundary-right-pair hypothesis also contains the corrected
succ-degree common-interleaver branch in the nonnegative regime. -/
theorem
    succDegreePairHasCommonInterleaver_nonneg_of_boundaryRightPairOrientation
    (hboundary : PosComboNoCommonBoundaryRightPairOrientationStatement) :
    PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement := by
  intro f g hf_pos hg_pos hfnn hgnn hfg hsucc hno
  have hprec_or :
      Prec f g ∨ Prec g f :=
    posComboOrientation_of_boundaryRightPairOrientation_and_nonnegCoeffs
      hboundary hf_pos hg_pos hfnn hgnn hfg
  have hprec_fg : Prec f g :=
    prec_forward_of_orientation_of_succDegree hsucc hprec_or
  exact ⟨g, hprec_fg, prec_refl hprec_fg.2.1.1 hprec_fg.2.1.2⟩

/-- Reduction of no-common orientation to the all-combinations bridge plus
Obreschkoff converse (`prec_of_allComboRealRooted`). -/
theorem posComboNoCommonOrientation_of_allComboBridge
    (hallBridge : PosComboNoCommonToAllComboBridgeStatement) :
    PosComboNoCommonOrientationStatement := by
  intro f g hfg hf_pos hg_pos hdeg_lo hdeg_hi hno
  have hall : AllComboRealRooted f g :=
    hallBridge hf_pos hg_pos hfg hdeg_lo hdeg_hi hno
  exact
    prec_or_revPrec_of_allComboRealRooted_ordered
      hf_pos hg_pos hall hdeg_lo hdeg_hi

/-- Converse reduction: the no-common orientation core immediately yields the
all-combinations bridge by passing through `allComboRealRooted_of_prec`. -/
theorem posComboAllComboBridge_of_noCommonOrientation
    (hstep : PosComboNoCommonOrientationStatement) :
    PosComboNoCommonToAllComboBridgeStatement :=
  fun _ _ hf_pos hg_pos hfg hdeg_lo hdeg_hi hno =>
    allComboRealRooted_of_prec_or_revPrec <|
    hstep hfg hf_pos hg_pos hdeg_lo hdeg_hi hno

/-- The two no-common bridge formulations are equivalent:
orientation (`Prec f g ∨ Prec g f`) and all-combinations real-rootedness. -/
theorem posComboNoCommonBridge_iff_orientation :
    PosComboNoCommonToAllComboBridgeStatement ↔
      PosComboNoCommonOrientationStatement :=
  ⟨posComboNoCommonOrientation_of_allComboBridge,
    posComboAllComboBridge_of_noCommonOrientation⟩

/-- The all-combinations no-common bridge also implies the coefficient-free
compatible succ-degree orientation target. -/
theorem compatibleSuccDegreePrec_of_allComboBridge
    (hallBridge : PosComboNoCommonToAllComboBridgeStatement) :
    CompatibleSuccDegreePrecStatement :=
  compatibleSuccDegreePrec_of_allCombo
    (compatibleSuccDegreeAllCombo_of_allComboBridge hallBridge)

/-- The all-combinations no-common bridge implies the exact lower-count
endpoint comparison used by the #42 no-gap reductions. -/
theorem compatibleSuccDegreeEndpointSignLowerCountEq_of_allComboBridge
    (hallBridge : PosComboNoCommonToAllComboBridgeStatement) :
    CompatibleSuccDegreeEndpointSignLowerCountEqStatement :=
  compatibleSuccDegreeEndpointSignLowerCountEq_of_allCombo
    (compatibleSuccDegreeAllCombo_of_allComboBridge hallBridge)

/-- Reduction of the two-polynomial bridge to an orientation theorem for the
positive-combination cone. If one can show `Prec f g ∨ Prec g f` for every
positive-leading `PosComboRealRooted` pair, then compatibility gives a common
right interleaver immediately. -/
theorem compatiblePairHasCommonInterleaver_of_posComboOrientation
    (horient :
      ∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        PosComboRealRooted f g →
        Prec f g ∨ Prec g f) :
    CompatiblePairHasCommonInterleaverStatement :=
  fun {_ _} hf_pos hg_pos hfg =>
    pairHasCommonInterleaver_of_prec_or_revPrec <|
      horient hf_pos hg_pos (hfg.toPosComboRealRooted hf_pos hg_pos)

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
    ∃ h : ℝ[X], Prec f h ∧ Prec g h := by
  by_cases hfg_deg : f.natDegree ≤ g.natDegree
  · have hprec_or : Prec f g ∨ Prec g f :=
      PosComboRealRooted.prec_or_revPrec_of_posComboRealRooted_of_no_common
        (hstep := fun hfg hf_pos hg_pos hdeg_lo hdeg_hi hno =>
          hstep hfg hf_pos hg_pos hdeg_lo hdeg_hi hno)
        hfg hf_pos hg_pos hfg_deg hclose.2
    exact pairHasCommonInterleaver_of_prec_or_revPrec hprec_or
  · have hgf_deg : g.natDegree ≤ f.natDegree := le_of_not_ge hfg_deg
    have hprec_or : Prec g f ∨ Prec f g :=
      PosComboRealRooted.prec_or_revPrec_of_posComboRealRooted_of_no_common
        (hstep := fun hfg hf_pos hg_pos hdeg_lo hdeg_hi hno =>
          hstep hfg hf_pos hg_pos hdeg_lo hdeg_hi hno)
        (PosComboRealRooted.comm hfg) hg_pos hf_pos hgf_deg hclose.1
    exact pairHasCommonInterleaver_of_prec_or_revPrec (Or.symm hprec_or)

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

/-- Pair-bridge reduction through the all-combinations bridge and a separate
degree-closeness input. -/
theorem posComboPairHasCommonInterleaver_of_allComboBridge_and_degreeClose
    (hallBridge : PosComboNoCommonToAllComboBridgeStatement)
    (hdegClose : PosComboNatDegreeCloseStatement) :
    PosComboPairHasCommonInterleaverStatement :=
  posComboPairHasCommonInterleaver_of_noCommonOrientation_and_degreeClose
    (posComboNoCommonOrientation_of_allComboBridge hallBridge)
    hdegClose

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
    ∃ h : ℝ[X], Prec f h ∧ Prec g h :=
  posComboPairHasCommonInterleaver_of_noCommonOrientation_and_degreeBounds
    hstep hf_pos hg_pos hfg
    (posComboNatDegreeClose_of_nonnegCoeffs hf_pos hg_pos hfnn hgnn hfg)

/-- In the nonnegative-coefficient regime, the all-combinations bridge implies
the full positive-combo pair bridge. -/
theorem posComboPairHasCommonInterleaver_of_allComboBridge_and_nonnegCoeffs
    (hallBridge : PosComboNoCommonToAllComboBridgeStatement)
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f) (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g) :
    ∃ h : ℝ[X], Prec f h ∧ Prec g h :=
  posComboPairHasCommonInterleaver_of_noCommonOrientation_and_nonnegCoeffs
    (posComboNoCommonOrientation_of_allComboBridge hallBridge)
    hf_pos hg_pos hfnn hgnn hfg

/-- In the nonnegative-coefficient regime, the affine-family bridge already
implies the full positive-combo pair bridge. -/
theorem posComboPairHasCommonInterleaver_of_affineFamilyBridge_and_nonnegCoeffs
    (haffBridge : PosComboNoCommonAffineFamilyStatement)
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f) (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g) :
    ∃ h : ℝ[X], Prec f h ∧ Prec g h :=
  pairHasCommonInterleaver_of_prec_or_revPrec <|
    posComboOrientation_of_affineFamilyBridge_and_nonnegCoeffs
      haffBridge hf_pos hg_pos hfnn hgnn hfg

/-- The boundary-right-pair orientation statement therefore already yields the
full positive-combo pair bridge in the nonnegative-coefficient regime. -/
theorem posComboPairHasCommonInterleaver_of_boundaryRightPairOrientation_and_nonnegCoeffs
    (hboundary : PosComboNoCommonBoundaryRightPairOrientationStatement)
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f) (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g) :
    ∃ h : ℝ[X], Prec f h ∧ Prec g h :=
  posComboPairHasCommonInterleaver_of_affineFamilyBridge_and_nonnegCoeffs
    (posComboNoCommonAffineFamily_of_boundaryRightPairOrientation hboundary)
    hf_pos hg_pos hfnn hgnn hfg

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
        ∃ h : ℝ[X], Prec f h ∧ Prec g h)
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f) (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g) :
    ∃ h : ℝ[X], Prec f h ∧ Prec g h := by
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
      ⟨h, hg_prec, hf_prec⟩
    exact ⟨h, hf_prec, hg_prec⟩

/-- Repaired degree-split package for the full positive-combo pair bridge in
the nonnegative-coefficient regime. This is the version to use after the
same-degree orientation alternative is replaced by a common-interleaver target.
-/
theorem posComboPairHasCommonInterleaver_of_pairDegreeSplit_and_nonnegCoeffs
    (hsucc : PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement)
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f) (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g) :
    ∃ h : ℝ[X], Prec f h ∧ Prec g h :=
  posComboPairHasCommonInterleaver_of_orderedBridge_and_nonnegCoeffs
    (fun {f g} hf_pos hg_pos hfnn hgnn hfg hdeg_lo hdeg_hi =>
      posComboPairHasCommonInterleaver_of_pairDegreeSplit_and_nonnegCoeffs_ordered
        (f := f) (g := g) hsucc hf_pos hg_pos hfnn hgnn hfg hdeg_lo hdeg_hi)
    hf_pos hg_pos hfnn hgnn hfg

/-- The honest degree-split package also yields the full positive-combo pair
bridge in the nonnegative-coefficient regime. -/
theorem posComboPairHasCommonInterleaver_of_degreeSplit_and_nonnegCoeffs
    (hsame : PosComboNoCommonSameDegreeOrientationAlternativeNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement)
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f) (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g) :
    ∃ h : ℝ[X], Prec f h ∧ Prec g h :=
  posComboPairHasCommonInterleaver_of_pairDegreeSplit_and_nonnegCoeffs hsucc hf_pos hg_pos hfnn hgnn hfg

/-- Full positive-combo pair bridge in the nonnegative-coefficient regime,
using the repaired same-degree branch and the affine-family bridge for the
succ-degree branch. -/
theorem posComboPairHasCommonInterleaver_of_sameDegreePair_and_affineFamily_nonneg
    (haffBridge : PosComboNoCommonAffineFamilyStatement)
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f) (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g) :
    ∃ h : ℝ[X], Prec f h ∧ Prec g h :=
  posComboPairHasCommonInterleaver_of_pairDegreeSplit_and_nonnegCoeffs
    (posComboNoCommonSuccDegreePairHasCommonInterleaver_of_affineFamily haffBridge)
    hf_pos hg_pos hfnn hgnn hfg

private theorem compatiblePairHasCommonInterleaver_of_nonnegPosComboPairBridge
    (hbridge :
      ∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        ∃ h : ℝ[X], Prec f h ∧ Prec g h)
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f) (hgnn : HasNonnegCoeffs g)
    (hfg : Compatible f g) :
    ∃ h : ℝ[X], Prec f h ∧ Prec g h :=
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
      ∃ h : ℝ[X], Prec f h ∧ Prec g h :=
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
      ∃ h : ℝ[X], Prec f h ∧ Prec g h :=
  fun {_ _} hf_pos hg_pos hfnn hgnn hfg =>
    posComboPairHasCommonInterleaver_of_affineFamilyBridge_and_nonnegCoeffs
      haffBridge hf_pos hg_pos hfnn hgnn hfg

private theorem nonnegPosComboPairBridge_of_pairDegreeSplit
    (hsucc : PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement) :
    ∀ ⦃f g : ℝ[X]⦄,
      HasPosLeadingCoeff f →
      HasPosLeadingCoeff g →
      HasNonnegCoeffs f →
      HasNonnegCoeffs g →
      PosComboRealRooted f g →
      ∃ h : ℝ[X], Prec f h ∧ Prec g h :=
  fun {_ _} hf_pos hg_pos hfnn hgnn hfg =>
    posComboPairHasCommonInterleaver_of_pairDegreeSplit_and_nonnegCoeffs hsucc hf_pos hg_pos hfnn hgnn hfg

/-- Compatibility-to-common-interleaver bridge under no-common orientation and
nonnegative coefficients. -/
theorem compatiblePairHasCommonInterleaver_of_noCommonOrientation_and_nonnegCoeffs
    (hstep : PosComboNoCommonOrientationStatement)
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f) (hgnn : HasNonnegCoeffs g)
    (hfg : Compatible f g) :
    ∃ h : ℝ[X], Prec f h ∧ Prec g h :=
  compatiblePairHasCommonInterleaver_of_nonnegPosComboPairBridge
    (nonnegPosComboPairBridge_of_noCommonOrientation hstep)
    hf_pos hg_pos hfnn hgnn hfg

/-- Compatibility bridge under nonnegative coefficients, reduced to the
all-combinations bridge. -/
theorem compatiblePairHasCommonInterleaver_of_allComboBridge_and_nonnegCoeffs
    (hallBridge : PosComboNoCommonToAllComboBridgeStatement)
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f) (hgnn : HasNonnegCoeffs g)
    (hfg : Compatible f g) :
    ∃ h : ℝ[X], Prec f h ∧ Prec g h :=
  compatiblePairHasCommonInterleaver_of_noCommonOrientation_and_nonnegCoeffs
    (posComboNoCommonOrientation_of_allComboBridge hallBridge)
    hf_pos hg_pos hfnn hgnn hfg

/-- Compatibility bridge under nonnegative coefficients, reduced to the
affine-family bridge. -/
theorem compatiblePairHasCommonInterleaver_of_affineFamilyBridge_and_nonnegCoeffs
    (haffBridge : PosComboNoCommonAffineFamilyStatement)
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f) (hgnn : HasNonnegCoeffs g)
    (hfg : Compatible f g) :
    ∃ h : ℝ[X], Prec f h ∧ Prec g h :=
  compatiblePairHasCommonInterleaver_of_nonnegPosComboPairBridge
    (nonnegPosComboPairBridge_of_affineFamilyBridge haffBridge)
    hf_pos hg_pos hfnn hgnn hfg

/-- Compatibility bridge under nonnegative coefficients, reduced to the
boundary-right-pair orientation statement. -/
theorem compatiblePairHasCommonInterleaver_of_boundaryRightPairOrientation_and_nonnegCoeffs
    (hboundary : PosComboNoCommonBoundaryRightPairOrientationStatement)
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f) (hgnn : HasNonnegCoeffs g)
    (hfg : Compatible f g) :
    ∃ h : ℝ[X], Prec f h ∧ Prec g h :=
  compatiblePairHasCommonInterleaver_of_affineFamilyBridge_and_nonnegCoeffs
    (posComboNoCommonAffineFamily_of_boundaryRightPairOrientation hboundary)
    hf_pos hg_pos hfnn hgnn hfg

/-- Compatibility bridge under nonnegative coefficients, reduced to the
repaired degree-split package with common-interleaver conclusions in both
branches. -/
theorem compatiblePairHasCommonInterleaver_of_pairDegreeSplit_and_nonnegCoeffs
    (hsucc : PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement)
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f) (hgnn : HasNonnegCoeffs g)
    (hfg : Compatible f g) :
    ∃ h : ℝ[X], Prec f h ∧ Prec g h :=
  compatiblePairHasCommonInterleaver_of_nonnegPosComboPairBridge
    (nonnegPosComboPairBridge_of_pairDegreeSplit hsucc)
    hf_pos hg_pos hfnn hgnn hfg

/-- Compatibility bridge under nonnegative coefficients, reduced to the honest
degree-split package. -/
theorem compatiblePairHasCommonInterleaver_of_degreeSplit_and_nonnegCoeffs
    (hsame : PosComboNoCommonSameDegreeOrientationAlternativeNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement)
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f) (hgnn : HasNonnegCoeffs g)
    (hfg : Compatible f g) :
    ∃ h : ℝ[X], Prec f h ∧ Prec g h :=
  compatiblePairHasCommonInterleaver_of_pairDegreeSplit_and_nonnegCoeffs hsucc hf_pos hg_pos hfnn hgnn hfg

/-- Compatibility bridge in the nonnegative-coefficient regime, using the
repaired same-degree branch and the affine-family bridge for the succ-degree
branch. -/
theorem compatiblePairHasCommonInterleaver_of_sameDegreePair_and_affineFamily_nonneg
    (haffBridge : PosComboNoCommonAffineFamilyStatement)
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f) (hgnn : HasNonnegCoeffs g)
    (hfg : Compatible f g) :
    ∃ h : ℝ[X], Prec f h ∧ Prec g h :=
  compatiblePairHasCommonInterleaver_of_pairDegreeSplit_and_nonnegCoeffs
    (posComboNoCommonSuccDegreePairHasCommonInterleaver_of_affineFamily haffBridge)
    hf_pos hg_pos hfnn hgnn hfg

private theorem posComboPairHasCommonInterleaver_via_nonnegShift
    {f g : ℝ[X]}
    (_hf_rr_ne : f ≠ 0) (hf_rr_splits : f.Splits)
    (_hg_rr_ne : g ≠ 0) (hg_rr_splits : g.Splits)
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfg : PosComboRealRooted f g)
    (hNonneg :
      ∀ {F G : ℝ[X]},
        HasPosLeadingCoeff F →
        HasPosLeadingCoeff G →
        HasNonnegCoeffs F →
        HasNonnegCoeffs G →
        PosComboRealRooted F G →
        ∃ h : ℝ[X], Prec F h ∧ Prec G h) :
    ∃ h : ℝ[X], Prec f h ∧ Prec g h := by
  obtain ⟨rf, hrf⟩ := exists_root_upper_bound f
  obtain ⟨rg, hrg⟩ := exists_root_upper_bound g
  let r : ℝ := max rf rg
  let f' : ℝ[X] := f.comp (X + C r)
  let g' : ℝ[X] := g.comp (X + C r)
  have hf'_pos : HasPosLeadingCoeff f' := by
    simpa [f'] using hf_pos.comp_X_add_C r
  have hg'_pos : HasPosLeadingCoeff g' := by
    simpa [g'] using hg_pos.comp_X_add_C r
  have hfnn : HasNonnegCoeffs f' := by
    refine hasNonnegCoeffs_comp_X_add_C_of_roots_le hf_pos hf_rr_splits ?_
    grind
  have hgnn : HasNonnegCoeffs g' := by
    refine hasNonnegCoeffs_comp_X_add_C_of_roots_le hg_pos hg_rr_splits ?_
    grind
  have hfg' : PosComboRealRooted f' g' := by
    intro α β hα hβ
    simpa [f', g'] using hfg.comp_X_add_C r hα hβ
  rcases hNonneg hf'_pos hg'_pos hfnn hgnn hfg' with
    ⟨h', hf'h', hg'h'⟩
  let h : ℝ[X] := h'.comp (X - C r)
  have hh_comp : h.comp (X + C r) = h' := by
    simp [h, Polynomial.comp_assoc, sub_eq_add_neg, add_assoc, add_comm]
  have hfh : Prec f h := by
    have htranslated : Prec f' (h.comp (X + C r)) := by lia
    exact (prec_comp_X_add_C_iff (f := f) (g := h) r).1 htranslated
  have hgh : Prec g h := by
    have htranslated : Prec g' (h.comp (X + C r)) := by lia
    exact (prec_comp_X_add_C_iff (f := g) (g := h) r).1 htranslated
  grind

/-- Degree-bounded common-interleaver endpoint for positive-leading split
positive-combination pairs.  Translating both polynomials far enough makes the
shifted coefficients nonnegative without changing their degrees, so the
nonnegative unordered degree-bounded reduction applies to the shifted pair; the
resulting common right interleaver is translated back. -/
theorem posComboPairHasCommonInterleaver_of_natDegree_le_reduction_unordered_via_nonnegShift
    {N : ℕ}
    (hterminal :
      ∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        f.natDegree ≤ g.natDegree →
        g.natDegree ≤ f.natDegree + 1 →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        g.natDegree ≤ N →
        ∃ h : ℝ[X], Prec f h ∧ Prec g h)
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hf_splits : f.Splits)
    (hg_splits : g.Splits)
    (hfg : PosComboRealRooted f g)
    (hfdeg : f.natDegree ≤ N)
    (hgdeg : g.natDegree ≤ N) :
    ∃ h : ℝ[X], Prec f h ∧ Prec g h := by
  obtain ⟨rf, hrf⟩ := exists_root_upper_bound f
  obtain ⟨rg, hrg⟩ := exists_root_upper_bound g
  let r : ℝ := max rf rg
  let f' : ℝ[X] := f.comp (X + C r)
  let g' : ℝ[X] := g.comp (X + C r)
  have hf'_pos : HasPosLeadingCoeff f' := by
    simpa [f'] using hf_pos.comp_X_add_C r
  have hg'_pos : HasPosLeadingCoeff g' := by
    simpa [g'] using hg_pos.comp_X_add_C r
  have hfnn : HasNonnegCoeffs f' := by
    refine hasNonnegCoeffs_comp_X_add_C_of_roots_le hf_pos hf_splits ?_
    grind
  have hgnn : HasNonnegCoeffs g' := by
    refine hasNonnegCoeffs_comp_X_add_C_of_roots_le hg_pos hg_splits ?_
    grind
  have hfg' : PosComboRealRooted f' g' := by
    intro α β hα hβ
    simpa [f', g'] using hfg.comp_X_add_C r hα hβ
  have hfdeg' : f'.natDegree ≤ N := by
    have hdeg_eq : f'.natDegree = f.natDegree := by
      simp [f', Polynomial.natDegree_comp]
    lia
  have hgdeg' : g'.natDegree ≤ N := by
    have hdeg_eq : g'.natDegree = g.natDegree := by
      simp [g', Polynomial.natDegree_comp]
    lia
  rcases
      posComboPairHasCommonInterleaver_of_natDegree_le_reduction_unordered
        (N := N) hterminal hf'_pos hg'_pos hfnn hgnn hfg' hfdeg' hgdeg' with
    ⟨h', hf'h', hg'h'⟩
  let h : ℝ[X] := h'.comp (X - C r)
  have hh_comp : h.comp (X + C r) = h' := by
    simp [h, Polynomial.comp_assoc, sub_eq_add_neg, add_assoc, add_comm]
  have hfh : Prec f h := by
    have htranslated : Prec f' (h.comp (X + C r)) := by
      rw [hh_comp]
      exact hf'h'
    exact (prec_comp_X_add_C_iff (f := f) (g := h) r).1 htranslated
  have hgh : Prec g h := by
    have htranslated : Prec g' (h.comp (X + C r)) := by
      rw [hh_comp]
      exact hg'h'
    exact (prec_comp_X_add_C_iff (f := g) (g := h) r).1 htranslated
  exact ⟨h, hfh, hgh⟩

/-- Positive-combination degree-`≤ 2` pair endpoint.  Translate both
polynomials far enough to make the shifted roots nonpositive, apply the
nonnegative-coefficient degree-`≤ 2` endpoint, and translate the common right
interleaver back. -/
theorem posComboPairHasCommonInterleaver_of_natDegree_le_two
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hf_splits : f.Splits)
    (hg_splits : g.Splits)
    (hfg : PosComboRealRooted f g)
    (hfdeg : f.natDegree ≤ 2)
    (hgdeg : g.natDegree ≤ 2) :
    ∃ h : ℝ[X], Prec f h ∧ Prec g h :=
  posComboPairHasCommonInterleaver_of_natDegree_le_reduction_unordered_via_nonnegShift
    (N := 2)
    (fun {_f _g} hf_pos hg_pos hfnn hgnn hfg hdeg_lo hdeg_hi hno hgdeg =>
      posComboNoCommonPairHasCommonInterleaver_of_natDegree_le_two
        hf_pos hg_pos hfnn hgnn hfg hdeg_lo hdeg_hi hno hgdeg)
    hf_pos hg_pos hf_splits hg_splits hfg hfdeg hgdeg

/-- Compatibility-level degree-`≤ 2` two-polynomial Chudnovsky--Seymour
endpoint. -/
theorem compatiblePairHasCommonInterleaver_of_natDegree_le_two
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfg : Compatible f g)
    (hfdeg : f.natDegree ≤ 2)
    (hgdeg : g.natDegree ≤ 2) :
    ∃ h : ℝ[X], Prec f h ∧ Prec g h :=
  posComboPairHasCommonInterleaver_of_natDegree_le_two hf_pos hg_pos
    (hfg.isRealRooted_left hf_pos).2
    (hfg.isRealRooted_right hg_pos).2
    (hfg.toPosComboRealRooted hf_pos hg_pos) hfdeg hgdeg

/-- Translation reduces the full positive-leading compatibility bridge to the
repaired nonnegative-coefficient degree-split package.  This is the shifted
version whose same-degree input already has the common-right-interleaver
conclusion, rather than the stronger orientation alternative. -/
theorem posComboPairHasCommonInterleaver_of_pairDegreeSplit_via_nonnegShift
    (hsucc : PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement)
    {f g : ℝ[X]}
    (_hf_rr_ne : f ≠ 0) (hf_rr_splits : f.Splits)
    (_hg_rr_ne : g ≠ 0) (hg_rr_splits : g.Splits)
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfg : PosComboRealRooted f g) :
    ∃ h : ℝ[X], Prec f h ∧ Prec g h :=
  posComboPairHasCommonInterleaver_via_nonnegShift
    _hf_rr_ne hf_rr_splits _hg_rr_ne hg_rr_splits hf_pos hg_pos hfg
    (fun {F G} hF_pos hG_pos hFnn hGnn hFG =>
      posComboPairHasCommonInterleaver_of_pairDegreeSplit_and_nonnegCoeffs hsucc (f := F) (g := G) hF_pos hG_pos hFnn hGnn hFG)

/-- Translation reduces the full positive-leading compatibility bridge to the
nonnegative-coefficient degree-split package: shift both polynomials far enough
to the right so all roots become nonpositive, apply the nonnegative theorem,
then translate the common interleaver back. -/
theorem posComboPairHasCommonInterleaver_of_degreeSplit_via_nonnegShift
    (hsame : PosComboNoCommonSameDegreeOrientationAlternativeNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement)
    {f g : ℝ[X]}
    (_hf_rr_ne : f ≠ 0) (hf_rr_splits : f.Splits)
    (_hg_rr_ne : g ≠ 0) (hg_rr_splits : g.Splits)
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfg : PosComboRealRooted f g) :
    ∃ h : ℝ[X], Prec f h ∧ Prec g h :=
  posComboPairHasCommonInterleaver_of_pairDegreeSplit_via_nonnegShift hsucc _hf_rr_ne hf_rr_splits _hg_rr_ne hg_rr_splits hf_pos hg_pos hfg

private theorem compatiblePairHasCommonInterleaver_of_realRootedPosComboBridge
    (hbridge :
      ∀ ⦃f g : ℝ[X]⦄,
        f ≠ 0 →
        f.Splits →
        g ≠ 0 →
        g.Splits →
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        PosComboRealRooted f g →
        ∃ h : ℝ[X], Prec f h ∧ Prec g h) :
    CompatiblePairHasCommonInterleaverStatement := by
  intro f g hf_pos hg_pos hfg
  have hf_rr : (f ≠ 0 ∧ f.Splits) := hfg.isRealRooted_left hf_pos
  have hg_rr : (g ≠ 0 ∧ g.Splits) := hfg.isRealRooted_right hg_pos
  exact hbridge hf_rr.1 hf_rr.2 hg_rr.1 hg_rr.2 hf_pos hg_pos
    (hfg.toPosComboRealRooted hf_pos hg_pos)

/-- Shifted compatibility bridge using the repaired same-degree
common-interleaver branch directly. -/
theorem compatiblePairHasCommonInterleaver_of_pairDegreeSplit_via_nonnegShift
    (hsucc : PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement) :
    CompatiblePairHasCommonInterleaverStatement :=
  compatiblePairHasCommonInterleaver_of_realRootedPosComboBridge
    (fun {_ _} hf_ne hf_splits hg_ne hg_splits hf_pos hg_pos hfg =>
      posComboPairHasCommonInterleaver_of_pairDegreeSplit_via_nonnegShift hsucc hf_ne hf_splits hg_ne hg_splits hf_pos hg_pos hfg)

/-- Shifted compatibility bridge from the concrete slot-data endpoints for the
same-degree and succ-degree nonnegative branches. -/
theorem compatiblePairHasCommonInterleaver_of_slotData_via_nonnegShift
    (hsame : PosComboNoCommonSameDegreeSlotDataNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreeSlotDataNonnegStatement) :
    CompatiblePairHasCommonInterleaverStatement :=
  compatiblePairHasCommonInterleaver_of_pairDegreeSplit_via_nonnegShift (succDegreePairHasCommonInterleaver_nonneg_of_slotData hsucc)

/-- Shifted compatibility bridge from the root-crossing formulations of the
nonnegative same-degree and succ-degree branches.  The succ-degree branch also
needs the left-splitting input that is part of its slot-data decomposition. -/
theorem compatiblePairHasCommonInterleaver_of_rootCrossing_via_nonnegShift
    (hsame : PosComboNoCommonSameDegreeRootCrossingNonnegStatement)
    (hsplit : PosComboSuccDegreeLeftSplitsNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreeRootCrossingNonnegStatement) :
    CompatiblePairHasCommonInterleaverStatement :=
  compatiblePairHasCommonInterleaver_of_pairDegreeSplit_via_nonnegShift (succDegreePairHasCommonInterleaver_nonneg_of_leftSplits_and_rootCrossing
      hsplit hsucc)

/-- Shifted compatibility bridge from root-crossing formulations alone.  The
succ-degree left endpoint is supplied by the root-continuity theorem. -/
theorem compatiblePairHasCommonInterleaver_of_rootCrossing
    (hsame : PosComboNoCommonSameDegreeRootCrossingNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreeRootCrossingNonnegStatement) :
    CompatiblePairHasCommonInterleaverStatement :=
  compatiblePairHasCommonInterleaver_of_rootCrossing_via_nonnegShift
    hsame PosComboSuccDegreeLeftSplitsNonnegStatement_of_rootContinuity hsucc

/-- Shifted compatibility bridge from lower-threshold root-count
formulations.  The succ-degree left endpoint is supplied by the
root-continuity theorem before shifting. -/
theorem compatiblePairHasCommonInterleaver_of_rootCount
    (hsame : PosComboNoCommonSameDegreeRootCountNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreeRootCountNonnegStatement) :
    CompatiblePairHasCommonInterleaverStatement :=
  compatiblePairHasCommonInterleaver_of_rootCrossing
    (posComboNoCommonSameDegreeRootCrossing_of_rootCount hsame)
    (posComboNoCommonSuccDegreeRootCrossing_of_rootCount hsucc)

/-- Shifted compatibility bridge from same-degree lower-threshold root counts
and succ-degree upper-threshold root counts. -/
theorem compatiblePairHasCommonInterleaver_of_rootCountAbove
    (hsame : PosComboNoCommonSameDegreeRootCountNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreeRootCountAboveNonnegStatement) :
    CompatiblePairHasCommonInterleaverStatement :=
  compatiblePairHasCommonInterleaver_of_rootCrossing
    (posComboNoCommonSameDegreeRootCrossing_of_rootCount hsame)
    (posComboNoCommonSuccDegreeRootCrossing_of_rootCountAbove hsucc)

/-- Shifted compatibility bridge from same-degree upper-threshold root counts
and succ-degree lower-threshold root counts. -/
theorem compatiblePairHasCommonInterleaver_of_sameRootCountAbove
    (hsame : PosComboNoCommonSameDegreeRootCountAboveNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreeRootCountNonnegStatement) :
    CompatiblePairHasCommonInterleaverStatement :=
  compatiblePairHasCommonInterleaver_of_rootCrossing
    (posComboNoCommonSameDegreeRootCrossing_of_rootCountAbove hsame)
    (posComboNoCommonSuccDegreeRootCrossing_of_rootCount hsucc)

/-- Shifted compatibility bridge from upper-threshold root-count formulations
in both the same-degree and succ-degree branches. -/
theorem compatiblePairHasCommonInterleaver_of_rootCountAboveBoth
    (hsame : PosComboNoCommonSameDegreeRootCountAboveNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreeRootCountAboveNonnegStatement) :
    CompatiblePairHasCommonInterleaverStatement :=
  compatiblePairHasCommonInterleaver_of_rootCrossing
    (posComboNoCommonSameDegreeRootCrossing_of_rootCountAbove hsame)
    (posComboNoCommonSuccDegreeRootCrossing_of_rootCountAbove hsucc)

/-- Shifted compatibility bridge from common-non-root lower-threshold root-count
formulations in both branches. -/
theorem compatiblePairHasCommonInterleaver_of_rootCountNonRoot
    (hsame : PosComboNoCommonSameDegreeRootCountNonRootNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreeRootCountNonRootNonnegStatement) :
    CompatiblePairHasCommonInterleaverStatement :=
  compatiblePairHasCommonInterleaver_of_rootCrossing
    (posComboNoCommonSameDegreeRootCrossing_of_rootCountNonRoot hsame)
    (posComboNoCommonSuccDegreeRootCrossing_of_rootCountNonRoot hsucc)

/-- Shifted compatibility bridge from same-degree common-non-root
lower-threshold root counts and succ-degree common-non-root upper-threshold
root counts. -/
theorem compatiblePairHasCommonInterleaver_of_rootCountAboveNonRoot
    (hsame : PosComboNoCommonSameDegreeRootCountNonRootNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreeRootCountAboveNonRootNonnegStatement) :
    CompatiblePairHasCommonInterleaverStatement :=
  compatiblePairHasCommonInterleaver_of_rootCrossing
    (posComboNoCommonSameDegreeRootCrossing_of_rootCountNonRoot hsame)
    (posComboNoCommonSuccDegreeRootCrossing_of_rootCountAboveNonRoot hsucc)

/-- Shifted compatibility bridge from same-degree common-non-root
upper-threshold root counts and succ-degree common-non-root lower-threshold
root counts. -/
theorem compatiblePairHasCommonInterleaver_of_sameRootCountAboveNonRoot
    (hsame : PosComboNoCommonSameDegreeRootCountAboveNonRootNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreeRootCountNonRootNonnegStatement) :
    CompatiblePairHasCommonInterleaverStatement :=
  compatiblePairHasCommonInterleaver_of_rootCrossing
    (posComboNoCommonSameDegreeRootCrossing_of_rootCountAboveNonRoot hsame)
    (posComboNoCommonSuccDegreeRootCrossing_of_rootCountNonRoot hsucc)

/-- Shifted compatibility bridge from common-non-root upper-threshold root-count
formulations in both branches. -/
theorem compatiblePairHasCommonInterleaver_of_rootCountAboveBothNonRoot
    (hsame : PosComboNoCommonSameDegreeRootCountAboveNonRootNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreeRootCountAboveNonRootNonnegStatement) :
    CompatiblePairHasCommonInterleaverStatement :=
  compatiblePairHasCommonInterleaver_of_rootCrossing
    (posComboNoCommonSameDegreeRootCrossing_of_rootCountAboveNonRoot hsame)
    (posComboNoCommonSuccDegreeRootCrossing_of_rootCountAboveNonRoot hsucc)

/-- Shifted compatibility bridge from root-crossing formulations, with the
succ-degree left endpoint supplied by the PF/ASW route. -/
theorem compatiblePairHasCommonInterleaver_of_rootCrossing_and_forward_asw
    (hsame : PosComboNoCommonSameDegreeRootCrossingNonnegStatement)
    (hASW : aissenSchoenbergWhitneyForwardOrZeroStatement)
    (hsucc : PosComboNoCommonSuccDegreeRootCrossingNonnegStatement) :
    CompatiblePairHasCommonInterleaverStatement :=
  compatiblePairHasCommonInterleaver_of_rootCrossing_via_nonnegShift
    hsame (PosComboSuccDegreeLeftSplitsNonnegStatement_of_forward_asw hASW) hsucc

/-- Shifted compatibility bridge from root-crossing formulations, with the
succ-degree left endpoint supplied by the splitting-only ASW target. -/
theorem compatiblePairHasCommonInterleaver_of_rootCrossing_and_forward_asw_splits
    (hsame : PosComboNoCommonSameDegreeRootCrossingNonnegStatement)
    (hASW : aissenSchoenbergWhitneyForwardSplitsStatement)
    (hsucc : PosComboNoCommonSuccDegreeRootCrossingNonnegStatement) :
    CompatiblePairHasCommonInterleaverStatement :=
  compatiblePairHasCommonInterleaver_of_rootCrossing_and_forward_asw
    hsame (aissenSchoenbergWhitneyForwardOrZero_of_splits hASW) hsucc

/-- Translation reduces the full positive-leading compatibility bridge to the
nonnegative-coefficient degree-split package: shift both polynomials far enough
to the right so all roots become nonpositive, apply the nonnegative theorem,
then translate the common interleaver back. -/
theorem compatiblePairHasCommonInterleaver_of_degreeSplit_via_nonnegShift
    (hsame : PosComboNoCommonSameDegreeOrientationAlternativeNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement) :
    CompatiblePairHasCommonInterleaverStatement :=
  compatiblePairHasCommonInterleaver_of_pairDegreeSplit_via_nonnegShift hsucc

/-- Shifted positive-leading compatibility bridge with the succ-degree branch
discharged by the affine-family bridge.  This leaves only the same-degree
orientation alternative as an external hypothesis. -/
theorem compatiblePairHasCommonInterleaver_of_sameDegreeAlternative_and_affineFamily_via_nonnegShift
    (hsame : PosComboNoCommonSameDegreeOrientationAlternativeNonnegStatement)
    (haffBridge : PosComboNoCommonAffineFamilyStatement) :
    CompatiblePairHasCommonInterleaverStatement :=
  compatiblePairHasCommonInterleaver_of_degreeSplit_via_nonnegShift
    hsame
    (posComboNoCommonSuccDegreePairHasCommonInterleaver_of_affineFamily haffBridge)

/-- Shifted positive-leading compatibility bridge with the succ-degree branch
discharged by the affine-family bridge and the same-degree branch stated in the
repaired common-right-interleaver form. -/
theorem compatiblePairHasCommonInterleaver_of_sameDegreePair_and_affineFamily_via_nonnegShift
    (haffBridge : PosComboNoCommonAffineFamilyStatement) :
    CompatiblePairHasCommonInterleaverStatement :=
  compatiblePairHasCommonInterleaver_of_pairDegreeSplit_via_nonnegShift
    (posComboNoCommonSuccDegreePairHasCommonInterleaver_of_affineFamily haffBridge)

/-- The stronger boundary-right-pair orientation hypothesis already finishes
the positive-leading positive-combination bridge after the nonnegative shift
reduction, provided the summands are individually real-rooted. -/
theorem posComboPairHasCommonInterleaver_of_boundaryRightPairOrientation_via_nonnegShift
    (hboundary : PosComboNoCommonBoundaryRightPairOrientationStatement)
    {f g : ℝ[X]}
    (hf_rr_ne : f ≠ 0) (hf_rr_splits : f.Splits) (hg_rr_ne : g ≠ 0) (hg_rr_splits : g.Splits)
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfg : PosComboRealRooted f g) :
    ∃ h : ℝ[X], Prec f h ∧ Prec g h :=
  posComboPairHasCommonInterleaver_of_degreeSplit_via_nonnegShift
    (boundaryRightPairOrientation_implies_sameDegreeOrientationAlternative_nonneg
      hboundary)
    (succDegreePairHasCommonInterleaver_nonneg_of_boundaryRightPairOrientation
      hboundary)
    hf_rr_ne hf_rr_splits hg_rr_ne hg_rr_splits hf_pos hg_pos hfg

/-- The stronger boundary-right-pair orientation hypothesis already finishes
the full positive-leading compatibility bridge after the nonnegative shift
reduction. -/
theorem compatiblePairHasCommonInterleaver_of_boundaryRightPairOrientation_via_nonnegShift
    (hboundary : PosComboNoCommonBoundaryRightPairOrientationStatement) :
    CompatiblePairHasCommonInterleaverStatement :=
  compatiblePairHasCommonInterleaver_of_sameDegreeAlternative_and_affineFamily_via_nonnegShift
    (boundaryRightPairOrientation_implies_sameDegreeOrientationAlternative_nonneg
      hboundary)
    (posComboNoCommonAffineFamily_of_boundaryRightPairOrientation hboundary)

/-- Compatibility-to-common-interleaver bridge from the reduced positive-combo
ingredients (no-common orientation + degree closeness). -/
theorem compatiblePairHasCommonInterleaver_of_noCommonOrientation_and_degreeClose
    (hstep : PosComboNoCommonOrientationStatement)
    (hdegClose : PosComboNatDegreeCloseStatement) :
    CompatiblePairHasCommonInterleaverStatement :=
  compatiblePairHasCommonInterleaver_of_posComboPair
    (posComboPairHasCommonInterleaver_of_noCommonOrientation_and_degreeClose
      hstep hdegClose)
end RealRooted
