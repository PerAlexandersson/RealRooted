import RealRooted.CommonInterleaver.PairBridge.Reduction.CommonRoot
import RealRooted.CommonInterleaver.PairBridge.SuccDegree.SlotData

/-!
# Pair bridge assembly: common-root reduction

Degree-split, common-root, and affine-family reductions before the final
compatibility assembly.
-/

open Polynomial

noncomputable section

namespace RealRooted

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

/-- Internal all-combinations orientation bridge for the endpoint layer. -/
protected lemma CommonInterleaver.PairBridge.prec_or_revPrec_of_allComboRealRooted_ordered
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
  have hdeg : f.natDegree + 1 = g.natDegree ∨ f.natDegree = g.natDegree := by lia
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
    CommonInterleaver.PairBridge.prec_or_revPrec_of_allComboRealRooted_ordered
      hf_pos hg_pos hall hdeg_lo hdeg_hi

/-- Repaired no-common degree-split reduction of the common-interleaver bridge
in the nonnegative regime: both same-degree and succ-degree branches are stated
directly with the common-right-interleaver conclusion needed downstream. -/
theorem posComboNoCommonPairHasCommonInterleaver_of_pairDegreeSplit_and_nonnegCoeffs
    (hsame : PosComboNoCommonSameDegreePairHasCommonInterleaverNonnegStatement)
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
  · exact hsame hf_pos hg_pos hfnn hgnn hfg hsame_deg hno
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
  posComboNoCommonPairHasCommonInterleaver_of_pairDegreeSplit_and_nonnegCoeffs
    (posComboNoCommonSameDegreePairHasCommonInterleaver_of_orientationAlternative_nonneg hsame)
    hsucc hf_pos hg_pos hfnn hgnn hfg hdeg_lo hdeg_hi hno

/-- Repaired no-common degree-split reduction with the succ-degree branch
discharged by the affine-family bridge.  After this reduction, the only
remaining local branch is the same-degree common-interleaver statement. -/
theorem posComboNoCommonPairHasCommonInterleaver_of_sameDegreePair_and_affineFamily_nonneg
    (hsame : PosComboNoCommonSameDegreePairHasCommonInterleaverNonnegStatement)
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
    hsame
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
    ∃ h : ℝ[X], Prec f h ∧ Prec g h :=
  PosComboRealRooted.induction_on_common_roots_nonneg
    (motive := fun f g => ∃ h : ℝ[X], Prec f h ∧ Prec g h)
    hterminal
    (fun {r f g} _ _ hfg => by
      obtain ⟨h, hf_prec, hg_prec⟩ := hfg
      exact
        ⟨(X - C r) * h,
          prec_mul_common_factor
            (isRealRooted_X_sub_C r).1 (isRealRooted_X_sub_C r).2 hf_prec,
          prec_mul_common_factor
            (isRealRooted_X_sub_C r).1 (isRealRooted_X_sub_C r).2 hg_prec⟩)
    hf_pos hg_pos hfnn hgnn hfg hdeg_lo hdeg_hi

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
    ∃ h : ℝ[X], Prec f h ∧ Prec g h :=
  PosComboRealRooted.induction_on_common_roots_nonneg
    (motive := fun f g => g.natDegree ≤ N → ∃ h : ℝ[X], Prec f h ∧ Prec g h)
    (fun {f g} hf_pos hg_pos hfnn hgnn hfg hdeg_lo hdeg_hi hno hgdeg =>
      hterminal hf_pos hg_pos hfnn hgnn hfg hdeg_lo hdeg_hi hno hgdeg)
    (fun {r f g} _ hg_pos ih hmul_deg => by
      have hgdeg : g.natDegree ≤ N := by
        rw [natDegree_mul (X_sub_C_ne_zero r) hg_pos.ne_zero, natDegree_X_sub_C]
          at hmul_deg
        lia
      obtain ⟨h, hf_prec, hg_prec⟩ := ih hgdeg
      exact
        ⟨(X - C r) * h,
          prec_mul_common_factor
            (isRealRooted_X_sub_C r).1 (isRealRooted_X_sub_C r).2 hf_prec,
          prec_mul_common_factor
            (isRealRooted_X_sub_C r).1 (isRealRooted_X_sub_C r).2 hg_prec⟩)
    hf_pos hg_pos hfnn hgnn hfg hdeg_lo hdeg_hi hgdeg

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

/-- Internal ordered degree-split bridge for the endpoint layer. -/
protected theorem
    CommonInterleaver.PairBridge.pairDegreeSplit_ordered
    (hsame : PosComboNoCommonSameDegreePairHasCommonInterleaverNonnegStatement)
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
      posComboNoCommonPairHasCommonInterleaver_of_pairDegreeSplit_and_nonnegCoeffs
        hsame hsucc (f := f) (g := g)
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
    AllComboRealRooted f g :=
  PosComboRealRooted.induction_on_common_roots_nonneg
    (motive := AllComboRealRooted)
    hterminal
    (fun {r} {_f _g} _ _ hall =>
      allComboRealRooted_mul_common_factor (isRealRooted_X_sub_C r).2 hall)
    hf_pos hg_pos hfnn hgnn hfg hdeg_lo hdeg_hi

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
  · have hdeg' : f.natDegree + 1 = g.natDegree ∨ f.natDegree = g.natDegree := by lia
    exact prec_of_allComboRealRooted hf_rr.1 hf_rr.2 hg_rr.1 hg_rr.2 hall hdeg'
  · have hdeg' : g.natDegree ≤ f.natDegree := le_of_not_ge hdeg
    have hdeg'' : g.natDegree + 1 = f.natDegree ∨ g.natDegree = f.natDegree := by lia
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

end RealRooted
