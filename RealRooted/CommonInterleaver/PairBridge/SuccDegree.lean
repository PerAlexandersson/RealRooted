import RealRooted.CommonInterleaver.PairBridge.Forward

/-!
# Pair bridge assembly: succ-degree branch

Root-count, root-crossing, and slot-data reductions for the succ-degree case.
-/

open Polynomial

noncomputable section

namespace RealRooted

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
        have hfder_lt : f.derivative.natDegree < n := by rwa [hfdeg_eq] at hfder_lt_self
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

/-- Succ-degree slot data from the proved ASW left endpoint and the
descending-root crossing inequalities. -/
theorem posComboNoCommonSuccDegreeSlotData_of_asw_and_rootCrossing
    (hcross : PosComboNoCommonSuccDegreeRootCrossingNonnegStatement) :
    PosComboNoCommonSuccDegreeSlotDataNonnegStatement :=
  posComboNoCommonSuccDegreeSlotData_of_leftSplits_and_rootCrossing
    PosComboSuccDegreeLeftSplitsNonnegStatement_of_asw hcross

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

/-- Succ-degree pair interleavers from the proved ASW left endpoint and the
descending-root crossing inequalities. -/
theorem succDegreePairHasCommonInterleaver_nonneg_of_asw_and_rootCrossing
    (hcross : PosComboNoCommonSuccDegreeRootCrossingNonnegStatement) :
    PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement :=
  succDegreePairHasCommonInterleaver_nonneg_of_leftSplits_and_rootCrossing
    PosComboSuccDegreeLeftSplitsNonnegStatement_of_asw hcross

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

end RealRooted
