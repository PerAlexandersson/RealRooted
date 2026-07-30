/-
# Two-polynomial common interleaver converse

Bridge file for compatibility/common-interleaver statements:
- two-polynomial compatibility and pairwise compatibility on finite lists,
- easy directions from common left interleavers to compatibility,
- the reduction of Chudnovsky--Seymour to the missing two-polynomial converse
  together with the named finite-family common-interleaver upgrades.

This file sits between the positive-combination machinery (PosCombo) and
the list-level common-interleaver combinatorics (CommonInterleaverSeq).
-/
import RealRooted.Compatibility.InterleaverBridge
import RealRooted.CommonInterleaver.AffineBoundary
import RealRooted.CommonInterleaver.SuccDegreeEndpoint
import RealRooted.CommonInterleaver.RootCountCombinatorics
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

/-- In the succ-degree positive-leading setting, the derivative of every
closed-segment member is nonzero as soon as the lower-degree endpoint has
positive degree.

For `β > 0`, the `g.derivative` term has strictly larger degree than the
`f.derivative` term; for `β = 0`, this is just nonvanishing of
`f.derivative`. -/
theorem succDegree_closedSegment_derivative_ne_zero
    {f g : ℝ[X]}
    (hg_pos : HasPosLeadingCoeff g)
    (hdeg : g.natDegree = f.natDegree + 1)
    (hfdeg : f.natDegree ≠ 0)
    {β : ℝ} (hβ0 : 0 ≤ β) :
    C (1 - β) * f.derivative + C β * g.derivative ≠ 0 := by
  rcases lt_or_eq_of_le hβ0 with hβ_pos | hβ_zero
  · have hleft_lt :
        (C (1 - β) * f.derivative).natDegree <
          (C β * g.derivative).natDegree := by
      have hleft_le :
          (C (1 - β) * f.derivative).natDegree ≤ f.derivative.natDegree :=
        Polynomial.natDegree_C_mul_le _ _
      have hf'_deg : f.derivative.natDegree = f.natDegree - 1 :=
        f.natDegree_derivative
      have hright_deg :
          (C β * g.derivative).natDegree = g.derivative.natDegree := by
        rw [Polynomial.natDegree_C_mul hβ_pos.ne']
      have hg'_deg : g.derivative.natDegree = g.natDegree - 1 :=
        g.natDegree_derivative
      rw [hright_deg, hg'_deg, hdeg]
      lia
    have hg'_pos : HasPosLeadingCoeff g.derivative :=
      hg_pos.derivative (by rw [hdeg]; lia)
    have hright_pos : HasPosLeadingCoeff (C β * g.derivative) :=
      hasPosLeadingCoeff_C_mul hβ_pos hg'_pos
    exact (hasPosLeadingCoeff_add_of_natDegree_lt_right hleft_lt hright_pos).ne_zero
  · subst hβ_zero
    simpa using (Polynomial.derivative_ne_zero.mpr hfdeg)

/-- In the succ-degree positive-leading setting, derivative closed-segment
members inherit splitting from the original closed segment. -/
theorem succDegree_closedSegment_derivative_splits
    {f g : ℝ[X]}
    (hseg : ∀ {β : ℝ}, 0 ≤ β → β ≤ 1 →
      ((C (1 - β) * f + C β * g) ≠ 0 ∧
        (C (1 - β) * f + C β * g).Splits))
    (hg_pos : HasPosLeadingCoeff g)
    (hdeg : g.natDegree = f.natDegree + 1)
    (hfdeg : f.natDegree ≠ 0)
    {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) :
    (C (1 - β) * f.derivative + C β * g.derivative).Splits :=
  closedSegment_derivative_splits_of_ne hseg hβ0 hβ1
    (succDegree_closedSegment_derivative_ne_zero hg_pos hdeg hfdeg hβ0)

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

/-- Any two positive-leading polynomials of degree at most one already satisfy
the Obreschkoff alternative. This is the unconditional low-degree endpoint for
the current bridge search. -/
theorem prec_or_revPrec_of_natDegree_le_one
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hf_deg_le_one : f.natDegree ≤ 1)
    (hg_deg_le_one : g.natDegree ≤ 1) :
    Prec f g ∨ Prec g f := by
  have hf0 : f ≠ 0 := hf_pos.ne_zero
  have hg0 : g ≠ 0 := hg_pos.ne_zero
  by_cases hf_deg0 : f.natDegree = 0
  · have hf_rr : (f ≠ 0 ∧ f.Splits) := isRealRooted_of_deg_zero hf0 hf_deg0
    by_cases hg_deg0 : g.natDegree = 0
    · have hg_rr : (g ≠ 0 ∧ g.Splits) := isRealRooted_of_deg_zero hg0 hg_deg0
      exact Or.inl (prec_degree_zero_degree_zero hf_rr.1 hf_rr.2 hg_rr.1 hg_rr.2 hf_deg0 hg_deg0)
    · have hg_deg1 : g.natDegree = 1 := by lia
      have hg_rr : (g ≠ 0 ∧ g.Splits) := isRealRooted_of_degree_one hg_deg1
      exact Or.inl (prec_degree_zero_right_of_degree_one hf_rr.1 hf_rr.2 hg_rr.1 hg_rr.2
        hf_deg0 hg_deg1)
  · have hf_deg1 : f.natDegree = 1 := by lia
    by_cases hg_deg0 : g.natDegree = 0
    · have hg_rr : (g ≠ 0 ∧ g.Splits) := isRealRooted_of_deg_zero hg0 hg_deg0
      have hf_rr : (f ≠ 0 ∧ f.Splits) := isRealRooted_of_degree_one hf_deg1
      exact Or.inr (prec_degree_zero_right_of_degree_one hg_rr.1 hg_rr.2 hf_rr.1 hf_rr.2
        hg_deg0 hf_deg1)
    · have hg_deg1 : g.natDegree = 1 := by lia
      exact PosComboRealRooted.prec_or_revPrec_of_same_degree_one (by lia) hf_deg1

/-- A symmetric `Prec` orientation implies all real linear combinations are
real-rooted, after commuting the pair in the reversed case. -/
theorem allComboRealRooted_of_prec_or_revPrec
    {f g : ℝ[X]} :
    Prec f g ∨ Prec g f →
    AllComboRealRooted f g
  | Or.inl hprec => allComboRealRooted_of_prec hprec
  | Or.inr hprec => allComboRealRooted_comm (allComboRealRooted_of_prec hprec)

namespace Compatible

/-- All-real-combination real-rootedness implies Chudnovsky--Seymour
nonnegative compatibility. -/
lemma of_allComboRealRooted {f g : ℝ[X]}
    (h : AllComboRealRooted f g) :
    Compatible f g := by
  intro α β _hα _hβ
  by_cases hzero : C α * f + C β * g = 0
  · exact Or.inl hzero
  · exact Or.inr ⟨hzero, h α β⟩

/-- A `Prec` relation implies Chudnovsky--Seymour nonnegative compatibility. -/
lemma of_prec {f g : ℝ[X]} (h : Prec f g) :
    Compatible f g :=
  of_allComboRealRooted (allComboRealRooted_of_prec h)

/-- Either `Prec` orientation implies Chudnovsky--Seymour nonnegative
compatibility. -/
lemma of_prec_or_revPrec {f g : ℝ[X]} (h : Prec f g ∨ Prec g f) :
    Compatible f g :=
  of_allComboRealRooted (allComboRealRooted_of_prec_or_revPrec h)

end Compatible

/-- Therefore every positive-leading pair of degree at most one already
satisfies the all-combinations conclusion. -/
theorem allComboRealRooted_of_natDegree_le_one
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hf_deg_le_one : f.natDegree ≤ 1)
    (hg_deg_le_one : g.natDegree ≤ 1) :
    AllComboRealRooted f g :=
  allComboRealRooted_of_prec_or_revPrec <|
    prec_or_revPrec_of_natDegree_le_one
      hf_pos hg_pos hf_deg_le_one hg_deg_le_one

/-- A `Prec` relation immediately gives a common right interleaver: use the
right endpoint as the witness. -/
theorem pairHasCommonInterleaver_of_prec
    {f g : ℝ[X]} (hprec : Prec f g) :
    ∃ h : ℝ[X], Prec f h ∧ Prec g h :=
  ⟨g, hprec, prec_refl hprec.2.1.1 hprec.2.1.2⟩

/-- A reversed `Prec` relation immediately gives a common right interleaver:
use the left endpoint as the witness. -/
theorem pairHasCommonInterleaver_of_revPrec
    {f g : ℝ[X]} (hprec : Prec g f) :
    ∃ h : ℝ[X], Prec f h ∧ Prec g h :=
  ⟨f, prec_refl hprec.2.1.1 hprec.2.1.2, hprec⟩

/-- A symmetric `Prec` orientation immediately gives a common right
interleaver: use the larger polynomial in the chosen orientation as the
witness. -/
theorem pairHasCommonInterleaver_of_prec_or_revPrec
    {f g : ℝ[X]} :
    Prec f g ∨ Prec g f →
    ∃ h : ℝ[X], Prec f h ∧ Prec g h
  | Or.inl hprec => pairHasCommonInterleaver_of_prec hprec
  | Or.inr hprec => pairHasCommonInterleaver_of_revPrec hprec

/-- A `Prec` relation immediately gives a common left interleaver: use the
left endpoint as the witness. -/
theorem pairHasCommonLeftInterleaver_of_prec
    {f g : ℝ[X]} (hprec : Prec f g) :
    ∃ h : ℝ[X], Prec h f ∧ Prec h g :=
  ⟨f, prec_refl hprec.1.1 hprec.1.2, hprec⟩

/-- A reversed `Prec` relation immediately gives a common left interleaver:
use the right endpoint as the witness. -/
theorem pairHasCommonLeftInterleaver_of_revPrec
    {f g : ℝ[X]} (hprec : Prec g f) :
    ∃ h : ℝ[X], Prec h f ∧ Prec h g :=
  ⟨g, hprec, prec_refl hprec.1.1 hprec.1.2⟩

/-- A symmetric `Prec` orientation immediately gives a common left interleaver:
use the smaller polynomial in the chosen orientation as the witness. -/
theorem pairHasCommonLeftInterleaver_of_prec_or_revPrec
    {f g : ℝ[X]} :
    Prec f g ∨ Prec g f →
    ∃ h : ℝ[X], Prec h f ∧ Prec h g
  | Or.inl hprec => pairHasCommonLeftInterleaver_of_prec hprec
  | Or.inr hprec => pairHasCommonLeftInterleaver_of_revPrec hprec

/-- Two-polynomial common-interleaver endpoint in degree at most one. This is
the direct pair version used by the low-degree Chudnovsky--Seymour package. -/
theorem pairHasCommonInterleaver_of_natDegree_le_one
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hf_deg_le_one : f.natDegree ≤ 1)
    (hg_deg_le_one : g.natDegree ≤ 1) :
    ∃ h : ℝ[X], Prec f h ∧ Prec g h :=
  pairHasCommonInterleaver_of_prec_or_revPrec <|
    prec_or_revPrec_of_natDegree_le_one
      hf_pos hg_pos hf_deg_le_one hg_deg_le_one

/-- Two-polynomial common-left-interleaver endpoint in degree at most one. -/
theorem pairHasCommonLeftInterleaver_of_natDegree_le_one
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hf_deg_le_one : f.natDegree ≤ 1)
    (hg_deg_le_one : g.natDegree ≤ 1) :
    ∃ h : ℝ[X], Prec h f ∧ Prec h g :=
  pairHasCommonLeftInterleaver_of_prec_or_revPrec <|
    prec_or_revPrec_of_natDegree_le_one
      hf_pos hg_pos hf_deg_le_one hg_deg_le_one

/-- Same-degree specialization of the low-degree pair endpoint. -/
theorem pairHasCommonInterleaver_of_sameDegree_natDegree_le_one
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hdeg : g.natDegree = f.natDegree)
    (hf_deg_le_one : f.natDegree ≤ 1) :
    ∃ h : ℝ[X], Prec f h ∧ Prec g h :=
  pairHasCommonInterleaver_of_natDegree_le_one
    hf_pos hg_pos hf_deg_le_one (by lia)

/-- Same-degree specialization of the low-degree common-left pair endpoint. -/
theorem pairHasCommonLeftInterleaver_of_sameDegree_natDegree_le_one
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hdeg : g.natDegree = f.natDegree)
    (hf_deg_le_one : f.natDegree ≤ 1) :
    ∃ h : ℝ[X], Prec h f ∧ Prec h g :=
  pairHasCommonLeftInterleaver_of_natDegree_le_one
    hf_pos hg_pos hf_deg_le_one (by lia)

/-- Compatibility-level version of the low-degree common-interleaver endpoint.
In degree at most one the common interleaver exists without using the
compatibility hypothesis, but keeping it in the statement makes this theorem a
drop-in two-polynomial bridge. -/
theorem compatiblePairHasCommonInterleaver_of_natDegree_le_one
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hf_deg_le_one : f.natDegree ≤ 1)
    (hg_deg_le_one : g.natDegree ≤ 1) :
    ∃ h : ℝ[X], Prec f h ∧ Prec g h :=
  pairHasCommonInterleaver_of_natDegree_le_one
    hf_pos hg_pos hf_deg_le_one hg_deg_le_one

/-- Compatibility-level version of the low-degree common-left endpoint. -/
theorem compatiblePairHasCommonLeftInterleaver_of_natDegree_le_one
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hf_deg_le_one : f.natDegree ≤ 1)
    (hg_deg_le_one : g.natDegree ≤ 1) :
    ∃ h : ℝ[X], Prec h f ∧ Prec h g :=
  pairHasCommonLeftInterleaver_of_natDegree_le_one
    hf_pos hg_pos hf_deg_le_one hg_deg_le_one

/-- Same-degree branch of the honest no-common target is already unconditional
through degree one. -/
theorem posComboNoCommonSameDegreeOrientationAlternative_of_degree_le_one
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hdeg : g.natDegree = f.natDegree)
    (hf_deg_le_one : f.natDegree ≤ 1) :
    Prec f g ∨ Prec g f :=
  prec_or_revPrec_of_natDegree_le_one
    hf_pos hg_pos hf_deg_le_one (by lia)

/-- Degree-one base case for the honest same-degree branch: equal-degree linear
pairs automatically satisfy the Obreschkoff alternative. This is a reusable
base case for future same-degree no-common work. -/
theorem posComboNoCommonSameDegreeOrientationAlternative_of_degree_one
    {f g : ℝ[X]}
    (hdeg : g.natDegree = f.natDegree)
    (hf_deg1 : f.natDegree = 1) :
    Prec f g ∨ Prec g f :=
  PosComboRealRooted.prec_or_revPrec_of_same_degree_one hdeg hf_deg1

/-- The old same-degree orientation alternative, when available, still feeds
the repaired same-degree common-interleaver target. -/
theorem posComboNoCommonSameDegreePairHasCommonInterleaver_of_orientationAlternative_nonneg
    (hsame : PosComboNoCommonSameDegreeOrientationAlternativeNonnegStatement) :
    PosComboNoCommonSameDegreePairHasCommonInterleaverNonnegStatement := by
  intro f g hf_pos hg_pos hfnn hgnn hfg hdeg hno
  have hf_rr : (f ≠ 0 ∧ f.Splits) :=
      hfg.isRealRooted_left_of_sameDegree hf_pos hg_pos hdeg
  have hg_rr : (g ≠ 0 ∧ g.Splits) :=
      hfg.isRealRooted_right_of_sameDegree hf_pos hg_pos hdeg
  have hslot :
      ∀ j (hj : j < f.natDegree + 1),
        (rootSlotInterval (rootSeqDesc f)
            ⟨j, by simpa [rootSeqDesc_length hf_rr.2] using hj⟩ ∩
          rootSlotInterval (rootSeqDesc g)
            ⟨j, by
              have : j < g.natDegree + 1 := by lia
              simpa [rootSeqDesc_length hg_rr.2] using this⟩).Nonempty := by
    rcases hsame hf_pos hg_pos hfnn hgnn hfg hdeg hno with hprec | hprec
    · intro j hj
      exact
        rootSlotInterval_inter_nonempty_of_commonInterleaver hprec
          (prec_refl hprec.2.1.1 hprec.2.1.2) j
          (by lia)
          (by lia)
    · intro j hj
      exact
        rootSlotInterval_inter_nonempty_of_commonInterleaver
          (prec_refl hprec.2.1.1 hprec.2.1.2) hprec
          j
          (by lia)
          (by lia)
  exact
    pairHasCommonInterleaver_of_sameDegree_slotIntersections
      hf_rr.1 hg_rr.1 hf_rr.2 hg_rr.2 hdeg hslot

/-- Low-degree base case for the repaired same-degree no-common target.  Through
degree one, the common-right-interleaver conclusion is unconditional once the
two polynomials have positive leading coefficients and equal degree. -/
theorem posComboNoCommonSameDegreePairHasCommonInterleaver_of_degree_le_one
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hdeg : g.natDegree = f.natDegree)
    (hf_deg_le_one : f.natDegree ≤ 1) :
    ∃ h : ℝ[X], Prec f h ∧ Prec g h :=
  pairHasCommonInterleaver_of_sameDegree_natDegree_le_one
    hf_pos hg_pos hdeg hf_deg_le_one

/-- Low-degree base case for the same-degree root-slot data.  Through degree one,
the common-right-interleaver base case already supplies every matching slot
intersection. -/
theorem sameDegreeSlotData_of_natDegree_le_one
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hdeg : g.natDegree = f.natDegree)
    (hf_deg_le_one : f.natDegree ≤ 1) :
    ∀ j, j < f.natDegree + 1 →
      ∀ (hjf : j < (rootSeqDesc f).length + 1)
        (hjg : j < (rootSeqDesc g).length + 1),
        (rootSlotInterval (rootSeqDesc f) ⟨j, hjf⟩ ∩
          rootSlotInterval (rootSeqDesc g) ⟨j, hjg⟩).Nonempty := by
  obtain ⟨h, hfh, hgh⟩ :=
    posComboNoCommonSameDegreePairHasCommonInterleaver_of_degree_le_one
      hf_pos hg_pos hdeg hf_deg_le_one
  intro j hj _ _
  have hjg' : j < g.natDegree + 1 := by lia
  exact rootSlotInterval_inter_nonempty_of_commonInterleaver hfh hgh j hj hjg'

/-- Succ-degree branch of the honest no-common target is already unconditional
in the constant-vs-linear endpoint case. -/
theorem posComboNoCommonSuccDegreeOrientation_of_degree_zero
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hf_deg0 : f.natDegree = 0)
    (hsucc : g.natDegree = f.natDegree + 1) :
    Prec f g := by
  have hf0 : f ≠ 0 := hf_pos.ne_zero
  have hg0 : g ≠ 0 := hg_pos.ne_zero
  have hf_rr : (f ≠ 0 ∧ f.Splits) := isRealRooted_of_deg_zero hf0 hf_deg0
  have hg_deg1 : g.natDegree = 1 := by lia
  have hg_rr : (g ≠ 0 ∧ g.Splits) := isRealRooted_of_degree_one hg_deg1
  exact prec_degree_zero_right_of_degree_one hf_rr.1 hf_rr.2 hg_rr.1 hg_rr.2 hf_deg0 hg_deg1

/-- Any proof of the stronger fixed-orientation succ-degree statement can be
used immediately as input for the corrected succ-degree pair bridge. -/
theorem posComboNoCommonSuccDegreePairHasCommonInterleaver_of_orientation_nonneg
    (horient : PosComboNoCommonSuccDegreeOrientationNonnegStatement) :
    PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement :=
  fun {_ _} hf_pos hg_pos hfnn hgnn hfg hsucc hno =>
    pairHasCommonInterleaver_of_prec <|
      horient hf_pos hg_pos hfnn hgnn hfg hsucc hno

/-- The corrected succ-degree pair bridge is already unconditional in the
constant-vs-linear endpoint case. -/
theorem posComboNoCommonSuccDegreePairHasCommonInterleaver_of_degree_zero
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hf_deg0 : f.natDegree = 0)
    (hsucc : g.natDegree = f.natDegree + 1) :
    ∃ h : ℝ[X], Prec f h ∧ Prec g h :=
  pairHasCommonInterleaver_of_prec <|
    posComboNoCommonSuccDegreeOrientation_of_degree_zero
      hf_pos hg_pos hf_deg0 hsucc

/-- The common-left succ-degree pair bridge is already unconditional in the
constant-vs-linear endpoint case. -/
theorem posComboNoCommonSuccDegreeCommonLeftInterleaver_of_degree_zero
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hf_deg0 : f.natDegree = 0)
    (hsucc : g.natDegree = f.natDegree + 1) :
    ∃ h : ℝ[X], Prec h f ∧ Prec h g :=
  pairHasCommonLeftInterleaver_of_prec <|
    posComboNoCommonSuccDegreeOrientation_of_degree_zero
      hf_pos hg_pos hf_deg0 hsucc

/-- Degree-zero base case for the succ-degree root-slot data.  In the
constant-vs-linear endpoint, the unconditional common interleaver recovers both
the left real-rootedness and all matching slot intersections. -/
theorem succDegreeSlotData_of_natDegree_eq_zero
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hf_deg0 : f.natDegree = 0)
    (hsucc : g.natDegree = f.natDegree + 1) :
    (f ≠ 0 ∧ f.Splits) ∧
      ∀ j, j < f.natDegree + 1 →
        ∀ (hjf : j < (rootSeqDesc f).length + 1)
          (hjg : j < (rootSeqDesc g).length + 1),
          (rootSlotInterval (rootSeqDesc f) ⟨j, hjf⟩ ∩
            rootSlotInterval (rootSeqDesc g) ⟨j, hjg⟩).Nonempty := by
  obtain ⟨h, hfh, hgh⟩ :=
    posComboNoCommonSuccDegreePairHasCommonInterleaver_of_degree_zero
      hf_pos hg_pos hf_deg0 hsucc
  refine ⟨hfh.1, ?_⟩
  intro j hj _ _
  have hjg' : j < g.natDegree + 1 := by lia
  exact rootSlotInterval_inter_nonempty_of_commonInterleaver hfh hgh j hj hjg'

/-- Degree-one left-hand endpoint of the corrected succ-degree branch under
the affine-family bridge.  The public affine-family degree-one lemma gives the
stronger right-pair orientation `g ≪ X * f`, so `X * f` is the required common
right interleaver. -/
theorem posComboNoCommonSuccDegreePairHasCommonInterleaver_of_affineFamily_degree_one
    (haffBridge : PosComboNoCommonAffineFamilyStatement)
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g)
    (hf_deg1 : f.natDegree = 1)
    (hsucc : g.natDegree = f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    ∃ h : ℝ[X], Prec f h ∧ Prec g h := by
  have hf0 : f ≠ 0 := hf_pos.ne_zero
  have hg0 : g ≠ 0 := hg_pos.ne_zero
  have haff :
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        ((((C s * X + C t) * f) + g) ≠ 0 ∧
          (((C s * X + C t) * f) + g).Splits) :=
    fun {s t} hs ht =>
      haffBridge hf_pos hg_pos hfnn hgnn hfg (by lia) (by lia) hno hs ht
  have hright : Prec g (X * f) :=
    prec_right_pair_of_affine_family_nonneg_degree_one
      hf0 hg0 hfnn hgnn haff hf_deg1
  exact pairHasCommonInterleaver_of_prec_right_pair_nonneg hright hfnn

/-- The affine-family bridge proves the full corrected succ-degree
common-right-interleaver branch.  The affine-family right-pair theorem gives
`g ≪ X * f`, so `X * f` is a common right interleaver. -/
theorem posComboNoCommonSuccDegreePairHasCommonInterleaver_of_affineFamily
    (haffBridge : PosComboNoCommonAffineFamilyStatement) :
    PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement := by
  intro f g hf_pos hg_pos hfnn hgnn hfg hsucc hno
  have hf0 : f ≠ 0 := hf_pos.ne_zero
  have hg0 : g ≠ 0 := hg_pos.ne_zero
  have haff :
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        ((((C s * X + C t) * f) + g) ≠ 0 ∧
          (((C s * X + C t) * f) + g).Splits) :=
    fun {s t} hs ht =>
      haffBridge hf_pos hg_pos hfnn hgnn hfg (by lia) (by lia) hno hs ht
  have hright : Prec g (X * f) :=
    prec_right_pair_of_affine_family_nonneg
      hf0 hg0 hfnn hgnn haff
  exact pairHasCommonInterleaver_of_prec_right_pair_nonneg hright hfnn

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

/-- Closed-segment form of the exact gap-two obstruction.  This is the
continuity/count target left after the sign argument has shown that the fixed
threshold is never a root along the closed segment from `f` to `g`. -/
def CompatibleSuccDegreeClosedSegmentNoGapTwoStatement : Prop :=
  ∀ ⦃f g : ℝ[X]⦄,
    Compatible f g →
    HasPosLeadingCoeff f →
    HasPosLeadingCoeff g →
    g.natDegree = f.natDegree + 1 →
    f.Splits →
    ∀ x : ℝ, ¬ f.IsRoot x → ¬ g.IsRoot x →
      (∀ {β : ℝ}, 0 ≤ β → β ≤ 1 →
        ¬ (C (1 - β) * f + C β * g).IsRoot x) →
      ((f.roots.filter (x < ·)).card : ℤ) - (g.roots.filter (x < ·)).card ≠ 2 ∧
      ((g.roots.filter (x < ·)).card : ℤ) - (f.roots.filter (x < ·)).card ≠ 2

/-- Closed-segment endpoint count-equality formulation.  This is the precise
count-stability theorem suggested by the root-continuity route: if a fixed
threshold is never crossed along the closed segment from the lower-degree
endpoint to the higher-degree endpoint, then the endpoint upper root counts at
that threshold agree. -/
def CompatibleSuccDegreeClosedSegmentCountEqStatement : Prop :=
  ∀ ⦃f g : ℝ[X]⦄,
    Compatible f g →
    HasPosLeadingCoeff f →
    HasPosLeadingCoeff g →
    g.natDegree = f.natDegree + 1 →
    f.Splits →
    ∀ x : ℝ, ¬ f.IsRoot x → ¬ g.IsRoot x →
      (∀ {β : ℝ}, 0 ≤ β → β ≤ 1 →
        ¬ (C (1 - β) * f + C β * g).IsRoot x) →
      (f.roots.filter (x < ·)).card = (g.roots.filter (x < ·)).card

/-- Right-pencil form of the exact gap-two obstruction.  The closed-segment
form reduces to this by the change of variables `β = μ / (μ + 1)`. -/
def CompatibleSuccDegreeRightFamilyNoGapTwoStatement : Prop :=
  ∀ ⦃f g : ℝ[X]⦄,
    Compatible f g →
    HasPosLeadingCoeff f →
    HasPosLeadingCoeff g →
    g.natDegree = f.natDegree + 1 →
    f.Splits →
    ∀ x : ℝ, ¬ f.IsRoot x → ¬ g.IsRoot x →
      (∀ {μ : ℝ}, 0 ≤ μ → ¬ (f + C μ * g).IsRoot x) →
      ((f.roots.filter (x < ·)).card : ℤ) - (g.roots.filter (x < ·)).card ≠ 2 ∧
      ((g.roots.filter (x < ·)).card : ℤ) - (f.roots.filter (x < ·)).card ≠ 2

/-- Endpoint-sign form of the exact gap-two obstruction.  The right-pencil
no-root hypothesis is equivalent to this same-sign condition at a common
non-root threshold. -/
def CompatibleSuccDegreeEndpointSignNoGapTwoStatement : Prop :=
  ∀ ⦃f g : ℝ[X]⦄,
    Compatible f g →
    HasPosLeadingCoeff f →
    HasPosLeadingCoeff g →
    g.natDegree = f.natDegree + 1 →
    f.Splits →
    ∀ x : ℝ, ¬ f.IsRoot x → ¬ g.IsRoot x →
      0 < f.eval x * g.eval x →
      ((f.roots.filter (x < ·)).card : ℤ) - (g.roots.filter (x < ·)).card ≠ 2 ∧
      ((g.roots.filter (x < ·)).card : ℤ) - (f.roots.filter (x < ·)).card ≠ 2

/-- Coefficient-free compatible succ-degree all-combinations shortcut.  This
candidate direct Obreschkoff span statement is now known to be false; see
`CommonInterleaverExamples.not_compatibleSuccDegreeAllComboStatement`. -/
def CompatibleSuccDegreeAllComboStatement : Prop :=
  ∀ ⦃f g : ℝ[X]⦄,
    Compatible f g →
    HasPosLeadingCoeff f →
    HasPosLeadingCoeff g →
    g.natDegree = f.natDegree + 1 →
    f.Splits →
    AllComboRealRooted f g

/-- Signed right-pencil form of the compatible succ-degree all-combinations
shortcut.  By scaling, this one-parameter family is equivalent to the whole
real linear span, and it is likewise known to be false. -/
def CompatibleSuccDegreeSignedRightFamilyStatement : Prop :=
  ∀ ⦃f g : ℝ[X]⦄,
    Compatible f g →
    HasPosLeadingCoeff f →
    HasPosLeadingCoeff g →
    g.natDegree = f.natDegree + 1 →
    f.Splits →
    ∀ μ : ℝ, (f + C μ * g).Splits

/-- Negative right-pencil form of the compatible succ-degree all-combinations
shortcut.  Compatibility supplies the case `0 ≤ μ`, but the isolated negative
half-line is false in general. -/
def CompatibleSuccDegreeNegativeRightFamilyStatement : Prop :=
  ∀ ⦃f g : ℝ[X]⦄,
    Compatible f g →
    HasPosLeadingCoeff f →
    HasPosLeadingCoeff g →
    g.natDegree = f.natDegree + 1 →
    f.Splits →
    ∀ μ : ℝ, μ < 0 → (f + C μ * g).Splits

/-- Nonnegative-coefficient version of the negative right-pencil shortcut.
This candidate strengthening is false even before translating endpoints. -/
def CompatibleSuccDegreeNegativeRightFamilyNonnegStatement : Prop :=
  ∀ ⦃f g : ℝ[X]⦄,
    Compatible f g →
    HasPosLeadingCoeff f →
    HasPosLeadingCoeff g →
    HasNonnegCoeffs f →
    HasNonnegCoeffs g →
    g.natDegree = f.natDegree + 1 →
    f.Splits →
    ∀ μ : ℝ, μ < 0 → (f + C μ * g).Splits

/-- Coefficient-free compatible succ-degree orientation shortcut.  The forced
proper-position orientation `f ≪ g` is false in general; this statement remains
only as a named failed route. -/
def CompatibleSuccDegreePrecStatement : Prop :=
  ∀ ⦃f g : ℝ[X]⦄,
    Compatible f g →
    HasPosLeadingCoeff f →
    HasPosLeadingCoeff g →
    g.natDegree = f.natDegree + 1 →
    f.Splits →
    Prec f g

/-- Exact lower-threshold endpoint-sign comparison expected from the
left-endpoint/count-stability picture. -/
def CompatibleSuccDegreeEndpointSignLowerCountEqStatement : Prop :=
  ∀ ⦃f g : ℝ[X]⦄,
    Compatible f g →
    HasPosLeadingCoeff f →
    HasPosLeadingCoeff g →
    g.natDegree = f.natDegree + 1 →
    f.Splits →
    ∀ x : ℝ, ¬ f.IsRoot x → ¬ g.IsRoot x →
      0 < f.eval x * g.eval x →
      ((g.roots.filter (· ≤ x)).card : ℤ) - (f.roots.filter (· ≤ x)).card = 1

/-- Lower-threshold endpoint-sign form of the exact gap obstruction.  This is
weaker than the exact lower-count comparison, but it is equivalent to the
upper-threshold endpoint-sign target by complement-count arithmetic. -/
def CompatibleSuccDegreeEndpointSignLowerNoGapStatement : Prop :=
  ∀ ⦃f g : ℝ[X]⦄,
    Compatible f g →
    HasPosLeadingCoeff f →
    HasPosLeadingCoeff g →
    g.natDegree = f.natDegree + 1 →
    f.Splits →
    ∀ x : ℝ, ¬ f.IsRoot x → ¬ g.IsRoot x →
      0 < f.eval x * g.eval x →
      ((g.roots.filter (· ≤ x)).card : ℤ) - (f.roots.filter (· ≤ x)).card ≠ 3 ∧
      ((f.roots.filter (· ≤ x)).card : ℤ) - (g.roots.filter (· ≤ x)).card ≠ 1

/-- Degree-two succ-degree root-order leaf.

For roots listed as `a ≤ b` for the quadratic endpoint and `p ≤ q ≤ r` for
the cubic endpoint, these three inequalities are exactly the finite root-order
content needed to rule out the degree-two exact gap-two obstruction. -/
def SuccDegreeQuadraticCubicRootBoundsStatement : Prop :=
  ∀ ⦃f g : ℝ[X]⦄,
    HasPosLeadingCoeff f →
    HasPosLeadingCoeff g →
    f.Splits →
    g.Splits →
    f.natDegree = 2 →
    g.natDegree = 3 →
    PosComboRealRooted f g →
    ∀ a b p q r : ℝ,
      a ≤ b →
      p ≤ q →
      q ≤ r →
      f.roots = {a, b} →
      g.roots = {p, q, r} →
      p ≤ a ∧ q ≤ b ∧ a ≤ r

/-- Degree-two succ-degree obstruction to the first cubic root lying strictly
above the first quadratic root. -/
def SuccDegreeQuadraticCubicFirstAboveObstructionStatement : Prop :=
  ∀ ⦃f g : ℝ[X]⦄,
    HasPosLeadingCoeff f →
    HasPosLeadingCoeff g →
    f.Splits →
    g.Splits →
    f.natDegree = 2 →
    g.natDegree = 3 →
    PosComboRealRooted f g →
    ∀ a b p q r : ℝ,
      a ≤ b →
      p ≤ q →
      q ≤ r →
      f.roots = {a, b} →
      g.roots = {p, q, r} →
      a < p →
      False

/-- Degree-two succ-degree obstruction to the second cubic root lying strictly
above the second quadratic root. -/
def SuccDegreeQuadraticCubicSecondAboveObstructionStatement : Prop :=
  ∀ ⦃f g : ℝ[X]⦄,
    HasPosLeadingCoeff f →
    HasPosLeadingCoeff g →
    f.Splits →
    g.Splits →
    f.natDegree = 2 →
    g.natDegree = 3 →
    PosComboRealRooted f g →
    ∀ a b p q r : ℝ,
      a ≤ b →
      p ≤ q →
      q ≤ r →
      f.roots = {a, b} →
      g.roots = {p, q, r} →
      b < q →
      False

/-- Degree-two succ-degree obstruction to all cubic roots lying strictly below
the first quadratic root. -/
def SuccDegreeQuadraticCubicFullBelowObstructionStatement : Prop :=
  ∀ ⦃f g : ℝ[X]⦄,
    HasPosLeadingCoeff f →
    HasPosLeadingCoeff g →
    f.Splits →
    g.Splits →
    f.natDegree = 2 →
    g.natDegree = 3 →
    PosComboRealRooted f g →
    ∀ a b p q r : ℝ,
      a ≤ b →
      p ≤ q →
      q ≤ r →
      f.roots = {a, b} →
      g.roots = {p, q, r} →
      r < a →
      False

/-- Pure monic-pencil obstruction for the first-above quadratic/cubic
configuration. -/
def QuadraticCubicFirstAbovePencilObstructionStatement : Prop :=
  ∀ ⦃a b p q r : ℝ⦄,
    a ≤ b →
    p ≤ q →
    q ≤ r →
    a < p →
    ∃ t : ℝ, 0 < t ∧
      ¬ (((X - C a) * (X - C b) +
          C t * ((X - C p) * (X - C q) * (X - C r))) : ℝ[X]).Splits

/-- Pure monic-pencil obstruction for the second-above quadratic/cubic
configuration. -/
def QuadraticCubicSecondAbovePencilObstructionStatement : Prop :=
  ∀ ⦃a b p q r : ℝ⦄,
    a ≤ b →
    p ≤ q →
    q ≤ r →
    b < q →
    ∃ t : ℝ, 0 < t ∧
      ¬ (((X - C a) * (X - C b) +
          C t * ((X - C p) * (X - C q) * (X - C r))) : ℝ[X]).Splits

/-- Pure monic-pencil obstruction for the full-below quadratic/cubic
configuration. -/
def QuadraticCubicFullBelowPencilObstructionStatement : Prop :=
  ∀ ⦃a b p q r : ℝ⦄,
    a ≤ b →
    p ≤ q →
    q ≤ r →
    r < a →
    ∃ t : ℝ, 0 < t ∧
      ¬ (((X - C a) * (X - C b) +
          C t * ((X - C p) * (X - C q) * (X - C r))) : ℝ[X]).Splits

/-- The positive-combination splitting hypothesis on a positive scalar
multiple of a monic quadratic and a positive scalar multiple of a monic cubic
descends to the corresponding monic right pencil. -/
theorem quadraticCubic_monic_pencil_splits_of_posCombo
    {a b p q r A B : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hpc : ∀ {lam μ : ℝ}, 0 < lam → 0 < μ →
      (C lam * (C A * ((X - C a) * (X - C b))) +
          C μ * (C B * ((X - C p) * (X - C q) * (X - C r)))).Splits) :
    ∀ t : ℝ, 0 < t →
      (((X - C a) * (X - C b) +
          C t * ((X - C p) * (X - C q) * (X - C r))) : ℝ[X]).Splits := by
  intro t ht
  have hcombo := hpc (lam := 1) (μ := t * A / B) one_pos (by positivity)
  have key : C (1 : ℝ) * (C A * ((X - C a) * (X - C b))) +
        C (t * A / B) * (C B * ((X - C p) * (X - C q) * (X - C r))) =
      C A * ((X - C a) * (X - C b) +
        C t * ((X - C p) * (X - C q) * (X - C r))) := by
    apply Polynomial.funext
    intro x
    simp only [eval_add, eval_mul, eval_sub, eval_C, eval_X, one_mul]
    field_simp [hB.ne']
  rw [key] at hcombo
  exact (splits_C_mul_iff hA.ne' _).1 hcombo

/-- Factor a split quadratic through a specified two-root multiset. -/
theorem eq_C_leadingCoeff_mul_prod_two
    {f : ℝ[X]} (hf : f.Splits) (a b : ℝ) (hr : f.roots = {a, b}) :
    f = C f.leadingCoeff * ((X - C a) * (X - C b)) := by
  rw [Polynomial.Splits.eq_prod_roots hf, hr]
  simp [Multiset.map_cons, Multiset.prod_cons]

/-- Pure first-above monic-pencil obstruction implies the corresponding
polynomial obstruction leaf. -/
theorem succDegreeQuadraticCubicFirstAboveObstruction_of_pencil
    (hpencil : QuadraticCubicFirstAbovePencilObstructionStatement) :
    SuccDegreeQuadraticCubicFirstAboveObstructionStatement := by
  intro f g hf_pos hg_pos hf_split hg_split _hfdeg _hgdeg hfg
    a b p q r hab hpq hqr hfroots hgroots hap
  have hffac : f = C f.leadingCoeff * ((X - C a) * (X - C b)) :=
    eq_C_leadingCoeff_mul_prod_two hf_split a b hfroots
  have hgfac : g =
      C g.leadingCoeff * ((X - C p) * (X - C q) * (X - C r)) :=
    eq_C_leadingCoeff_mul_prod_three hg_split p q r hgroots
  have hpc' : ∀ {lam μ : ℝ}, 0 < lam → 0 < μ →
      (C lam * (C f.leadingCoeff * ((X - C a) * (X - C b))) +
          C μ * (C g.leadingCoeff *
            ((X - C p) * (X - C q) * (X - C r)))).Splits := by
    intro lam μ hlam hμ
    rw [← hffac, ← hgfac]
    exact (hfg (lam := lam) (μ := μ) hlam hμ).2
  obtain ⟨t, ht, hnot⟩ := hpencil hab hpq hqr hap
  exact hnot
    (quadraticCubic_monic_pencil_splits_of_posCombo
      hf_pos hg_pos hpc' t ht)

/-- Pure second-above monic-pencil obstruction implies the corresponding
polynomial obstruction leaf. -/
theorem succDegreeQuadraticCubicSecondAboveObstruction_of_pencil
    (hpencil : QuadraticCubicSecondAbovePencilObstructionStatement) :
    SuccDegreeQuadraticCubicSecondAboveObstructionStatement := by
  intro f g hf_pos hg_pos hf_split hg_split _hfdeg _hgdeg hfg
    a b p q r hab hpq hqr hfroots hgroots hbq
  have hffac : f = C f.leadingCoeff * ((X - C a) * (X - C b)) :=
    eq_C_leadingCoeff_mul_prod_two hf_split a b hfroots
  have hgfac : g =
      C g.leadingCoeff * ((X - C p) * (X - C q) * (X - C r)) :=
    eq_C_leadingCoeff_mul_prod_three hg_split p q r hgroots
  have hpc' : ∀ {lam μ : ℝ}, 0 < lam → 0 < μ →
      (C lam * (C f.leadingCoeff * ((X - C a) * (X - C b))) +
          C μ * (C g.leadingCoeff *
            ((X - C p) * (X - C q) * (X - C r)))).Splits := by
    intro lam μ hlam hμ
    rw [← hffac, ← hgfac]
    exact (hfg (lam := lam) (μ := μ) hlam hμ).2
  obtain ⟨t, ht, hnot⟩ := hpencil hab hpq hqr hbq
  exact hnot
    (quadraticCubic_monic_pencil_splits_of_posCombo
      hf_pos hg_pos hpc' t ht)

/-- Pure full-below monic-pencil obstruction implies the corresponding
polynomial obstruction leaf. -/
theorem succDegreeQuadraticCubicFullBelowObstruction_of_pencil
    (hpencil : QuadraticCubicFullBelowPencilObstructionStatement) :
    SuccDegreeQuadraticCubicFullBelowObstructionStatement := by
  intro f g hf_pos hg_pos hf_split hg_split _hfdeg _hgdeg hfg
    a b p q r hab hpq hqr hfroots hgroots hra
  have hffac : f = C f.leadingCoeff * ((X - C a) * (X - C b)) :=
    eq_C_leadingCoeff_mul_prod_two hf_split a b hfroots
  have hgfac : g =
      C g.leadingCoeff * ((X - C p) * (X - C q) * (X - C r)) :=
    eq_C_leadingCoeff_mul_prod_three hg_split p q r hgroots
  have hpc' : ∀ {lam μ : ℝ}, 0 < lam → 0 < μ →
      (C lam * (C f.leadingCoeff * ((X - C a) * (X - C b))) +
          C μ * (C g.leadingCoeff *
            ((X - C p) * (X - C q) * (X - C r)))).Splits := by
    intro lam μ hlam hμ
    rw [← hffac, ← hgfac]
    exact (hfg (lam := lam) (μ := μ) hlam hμ).2
  obtain ⟨t, ht, hnot⟩ := hpencil hab hpq hqr hra
  exact hnot
    (quadraticCubic_monic_pencil_splits_of_posCombo
      hf_pos hg_pos hpc' t ht)

/-- The three elementary quadratic/cubic obstruction leaves imply the
degree-two succ-degree root-order leaf. -/
theorem succDegreeQuadraticCubicRootBounds_of_obstructions
    (hfirst : SuccDegreeQuadraticCubicFirstAboveObstructionStatement)
    (hsecond : SuccDegreeQuadraticCubicSecondAboveObstructionStatement)
    (hbelow : SuccDegreeQuadraticCubicFullBelowObstructionStatement) :
    SuccDegreeQuadraticCubicRootBoundsStatement := by
  intro f g hf_pos hg_pos hf_split hg_split hfdeg hgdeg hfg
    a b p q r hab hpq hqr hfroots hgroots
  refine ⟨?_, ?_, ?_⟩
  · exact le_of_not_gt
      (fun hpa => hfirst hf_pos hg_pos hf_split hg_split hfdeg hgdeg hfg
        a b p q r hab hpq hqr hfroots hgroots hpa)
  · exact le_of_not_gt
      (fun hqb => hsecond hf_pos hg_pos hf_split hg_split hfdeg hgdeg hfg
        a b p q r hab hpq hqr hfroots hgroots hqb)
  · exact le_of_not_gt
      (fun har => hbelow hf_pos hg_pos hf_split hg_split hfdeg hgdeg hfg
        a b p q r hab hpq hqr hfroots hgroots har)

/-- Pure monic-pencil obstruction leaves imply the degree-two succ-degree
root-order leaf. -/
theorem succDegreeQuadraticCubicRootBounds_of_pencil_obstructions
    (hfirst : QuadraticCubicFirstAbovePencilObstructionStatement)
    (hsecond : QuadraticCubicSecondAbovePencilObstructionStatement)
    (hbelow : QuadraticCubicFullBelowPencilObstructionStatement) :
    SuccDegreeQuadraticCubicRootBoundsStatement :=
  succDegreeQuadraticCubicRootBounds_of_obstructions
    (succDegreeQuadraticCubicFirstAboveObstruction_of_pencil hfirst)
    (succDegreeQuadraticCubicSecondAboveObstruction_of_pencil hsecond)
    (succDegreeQuadraticCubicFullBelowObstruction_of_pencil hbelow)

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

/-- Succ-degree right-pencil parity bridge for upper root counts. -/
theorem succDegree_odd_roots_gt_count_sub_iff_exists_pos_isRoot_add_right
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfg : PosComboRealRooted f g) (hdeg : g.natDegree = f.natDegree + 1)
    (hf_split : f.Splits) {x : ℝ} (hxf : ¬ f.IsRoot x) (hxg : ¬ g.IsRoot x) :
    (Odd (((f.roots.filter (x < ·)).card : ℤ) -
        (g.roots.filter (x < ·)).card) ↔
      ∃ μ : ℝ, 0 < μ ∧ (f + C μ * g).IsRoot x) := by
  have hg_split : g.Splits :=
    (hfg.isRealRooted_right_of_succDegree hf_pos hg_pos hdeg).2
  exact sameDegree_odd_roots_gt_count_sub_iff_exists_pos_isRoot_add_right
    hf_split hg_split hf_pos hg_pos hxf hxg

/-- Succ-degree upper root-count parity in endpoint-sign form. -/
theorem succDegree_odd_roots_gt_count_sub_iff_eval_mul_neg
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfg : PosComboRealRooted f g) (hdeg : g.natDegree = f.natDegree + 1)
    (hf_split : f.Splits) {x : ℝ} (hxf : ¬ f.IsRoot x) (hxg : ¬ g.IsRoot x) :
    (Odd (((f.roots.filter (x < ·)).card : ℤ) -
        (g.roots.filter (x < ·)).card) ↔ f.eval x * g.eval x < 0) := by
  have hfx_eval : f.eval x ≠ 0 := by
    intro hfx
    exact hxf (by simpa [Polynomial.IsRoot.def] using hfx)
  exact (succDegree_odd_roots_gt_count_sub_iff_exists_pos_isRoot_add_right
    hf_pos hg_pos hfg hdeg hf_split hxf hxg).trans
    (exists_pos_isRoot_add_right_iff_eval_mul_neg hfx_eval)

/-- If the succ-degree upper root-count difference is not odd, then the
endpoint evaluations at that common non-root have the same sign. -/
theorem succDegree_eval_mul_pos_of_not_odd_roots_gt_count_sub
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfg : PosComboRealRooted f g) (hdeg : g.natDegree = f.natDegree + 1)
    (hf_split : f.Splits) {x : ℝ} (hxf : ¬ f.IsRoot x) (hxg : ¬ g.IsRoot x)
    (hnot_odd : ¬ Odd (((f.roots.filter (x < ·)).card : ℤ) -
        (g.roots.filter (x < ·)).card)) :
    0 < f.eval x * g.eval x := by
  have hnot_neg : ¬ f.eval x * g.eval x < 0 := by
    intro hneg
    exact hnot_odd
      ((succDegree_odd_roots_gt_count_sub_iff_eval_mul_neg
        hf_pos hg_pos hfg hdeg hf_split hxf hxg).mpr hneg)
  have hfx_eval : f.eval x ≠ 0 := by
    intro hfx
    exact hxf (by simpa [Polynomial.IsRoot.def] using hfx)
  have hgx_eval : g.eval x ≠ 0 := by
    intro hgx
    exact hxg (by simpa [Polynomial.IsRoot.def] using hgx)
  have hprod_ne : f.eval x * g.eval x ≠ 0 := mul_ne_zero hfx_eval hgx_eval
  exact lt_of_le_of_ne (le_of_not_gt hnot_neg) hprod_ne.symm

/-- A gap of exactly two in the forward upper root count forces same-sign
endpoint evaluations at a common non-root threshold. -/
theorem succDegree_eval_mul_pos_of_roots_gt_count_sub_eq_two
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfg : PosComboRealRooted f g) (hdeg : g.natDegree = f.natDegree + 1)
    (hf_split : f.Splits) {x : ℝ} (hxf : ¬ f.IsRoot x) (hxg : ¬ g.IsRoot x)
    (hcount : ((f.roots.filter (x < ·)).card : ℤ) -
        (g.roots.filter (x < ·)).card = 2) :
    0 < f.eval x * g.eval x :=
  succDegree_eval_mul_pos_of_not_odd_roots_gt_count_sub
    hf_pos hg_pos hfg hdeg hf_split hxf hxg (by rw [hcount]; norm_num)

/-- A gap of exactly two in the reverse upper root count forces same-sign
endpoint evaluations at a common non-root threshold. -/
theorem succDegree_eval_mul_pos_of_rev_roots_gt_count_sub_eq_two
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfg : PosComboRealRooted f g) (hdeg : g.natDegree = f.natDegree + 1)
    (hf_split : f.Splits) {x : ℝ} (hxf : ¬ f.IsRoot x) (hxg : ¬ g.IsRoot x)
    (hcount : ((g.roots.filter (x < ·)).card : ℤ) -
        (f.roots.filter (x < ·)).card = 2) :
    0 < f.eval x * g.eval x := by
  refine succDegree_eval_mul_pos_of_not_odd_roots_gt_count_sub
    hf_pos hg_pos hfg hdeg hf_split hxf hxg ?_
  rw [show ((f.roots.filter (x < ·)).card : ℤ) -
      (g.roots.filter (x < ·)).card = -2 by linarith]
  norm_num

/-- A forward upper root-count gap of two rules out roots at that threshold
throughout the closed segment between the endpoints. -/
theorem succDegree_closedSegment_not_isRoot_of_roots_gt_count_sub_eq_two
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfg : PosComboRealRooted f g) (hdeg : g.natDegree = f.natDegree + 1)
    (hf_split : f.Splits) {β x : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hxf : ¬ f.IsRoot x) (hxg : ¬ g.IsRoot x)
    (hcount : ((f.roots.filter (x < ·)).card : ℤ) -
        (g.roots.filter (x < ·)).card = 2) :
    ¬ (C (1 - β) * f + C β * g).IsRoot x :=
  closedSegment_not_isRoot_of_eval_mul_pos hβ0 hβ1 <|
    succDegree_eval_mul_pos_of_roots_gt_count_sub_eq_two
      hf_pos hg_pos hfg hdeg hf_split hxf hxg hcount

/-- A reverse upper root-count gap of two rules out roots at that threshold
throughout the closed segment between the endpoints. -/
theorem succDegree_closedSegment_not_isRoot_of_rev_roots_gt_count_sub_eq_two
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfg : PosComboRealRooted f g) (hdeg : g.natDegree = f.natDegree + 1)
    (hf_split : f.Splits) {β x : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hxf : ¬ f.IsRoot x) (hxg : ¬ g.IsRoot x)
    (hcount : ((g.roots.filter (x < ·)).card : ℤ) -
        (f.roots.filter (x < ·)).card = 2) :
    ¬ (C (1 - β) * f + C β * g).IsRoot x :=
  closedSegment_not_isRoot_of_eval_mul_pos hβ0 hβ1 <|
    succDegree_eval_mul_pos_of_rev_roots_gt_count_sub_eq_two
      hf_pos hg_pos hfg hdeg hf_split hxf hxg hcount

/-- Compatible-pair version of the forward gap-two endpoint-sign lemma. -/
theorem compatibleSuccDegree_eval_mul_pos_of_roots_gt_count_sub_eq_two
    {f g : ℝ[X]}
    (hcomp : Compatible f g)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hdeg : g.natDegree = f.natDegree + 1)
    (hf_split : f.Splits) {x : ℝ} (hxf : ¬ f.IsRoot x) (hxg : ¬ g.IsRoot x)
    (hcount : ((f.roots.filter (x < ·)).card : ℤ) -
        (g.roots.filter (x < ·)).card = 2) :
    0 < f.eval x * g.eval x :=
  succDegree_eval_mul_pos_of_roots_gt_count_sub_eq_two
    hf_pos hg_pos (hcomp.toPosComboRealRooted hf_pos hg_pos)
    hdeg hf_split hxf hxg hcount

/-- Compatible-pair version of the reverse gap-two endpoint-sign lemma. -/
theorem compatibleSuccDegree_eval_mul_pos_of_rev_roots_gt_count_sub_eq_two
    {f g : ℝ[X]}
    (hcomp : Compatible f g)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hdeg : g.natDegree = f.natDegree + 1)
    (hf_split : f.Splits) {x : ℝ} (hxf : ¬ f.IsRoot x) (hxg : ¬ g.IsRoot x)
    (hcount : ((g.roots.filter (x < ·)).card : ℤ) -
        (f.roots.filter (x < ·)).card = 2) :
    0 < f.eval x * g.eval x :=
  succDegree_eval_mul_pos_of_rev_roots_gt_count_sub_eq_two
    hf_pos hg_pos (hcomp.toPosComboRealRooted hf_pos hg_pos)
    hdeg hf_split hxf hxg hcount

/-- Compatible-pair version of the forward gap-two closed-segment
nonvanishing lemma. -/
theorem compatibleSuccDegree_closedSegment_not_isRoot_of_roots_gt_count_sub_eq_two
    {f g : ℝ[X]}
    (hcomp : Compatible f g)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hdeg : g.natDegree = f.natDegree + 1)
    (hf_split : f.Splits) {β x : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hxf : ¬ f.IsRoot x) (hxg : ¬ g.IsRoot x)
    (hcount : ((f.roots.filter (x < ·)).card : ℤ) -
        (g.roots.filter (x < ·)).card = 2) :
    ¬ (C (1 - β) * f + C β * g).IsRoot x :=
  succDegree_closedSegment_not_isRoot_of_roots_gt_count_sub_eq_two
    hf_pos hg_pos (hcomp.toPosComboRealRooted hf_pos hg_pos)
    hdeg hf_split hβ0 hβ1 hxf hxg hcount

/-- Compatible-pair version of the reverse gap-two closed-segment
nonvanishing lemma. -/
theorem compatibleSuccDegree_closedSegment_not_isRoot_of_rev_roots_gt_count_sub_eq_two
    {f g : ℝ[X]}
    (hcomp : Compatible f g)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hdeg : g.natDegree = f.natDegree + 1)
    (hf_split : f.Splits) {β x : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hxf : ¬ f.IsRoot x) (hxg : ¬ g.IsRoot x)
    (hcount : ((g.roots.filter (x < ·)).card : ℤ) -
        (f.roots.filter (x < ·)).card = 2) :
    ¬ (C (1 - β) * f + C β * g).IsRoot x :=
  succDegree_closedSegment_not_isRoot_of_rev_roots_gt_count_sub_eq_two
    hf_pos hg_pos (hcomp.toPosComboRealRooted hf_pos hg_pos)
    hdeg hf_split hβ0 hβ1 hxf hxg hcount

/-- Positive closed-segment members of a succ-degree pair keep the larger
endpoint degree. -/
theorem succDegree_closedSegment_natDegree_eq_right_of_pos
    {f g : ℝ[X]}
    (hg_pos : HasPosLeadingCoeff g)
    (hdeg : g.natDegree = f.natDegree + 1)
    {β : ℝ} (hβ : 0 < β) :
    (C (1 - β) * f + C β * g).natDegree = g.natDegree := by
  have hleft_le : (C (1 - β) * f).natDegree ≤ f.natDegree :=
    Polynomial.natDegree_C_mul_le _ _
  have hright_deg : (C β * g).natDegree = g.natDegree := by
    rw [Polynomial.natDegree_C_mul hβ.ne']
  have hlt : (C (1 - β) * f).natDegree < (C β * g).natDegree := by
    rw [hright_deg, hdeg]
    exact Nat.lt_succ_of_le hleft_le
  exact
    (natDegree_add_eq_right_of_natDegree_lt_of_posLeadingCoeff hlt
      (hasPosLeadingCoeff_C_mul hβ hg_pos)).trans hright_deg

/-- Positive closed-segment members of a succ-degree pair have positive
leading coefficient. -/
theorem succDegree_closedSegment_hasPosLeadingCoeff_of_pos
    {f g : ℝ[X]}
    (hg_pos : HasPosLeadingCoeff g)
    (hdeg : g.natDegree = f.natDegree + 1)
    {β : ℝ} (hβ : 0 < β) :
    HasPosLeadingCoeff (C (1 - β) * f + C β * g) := by
  have hleft_le : (C (1 - β) * f).natDegree ≤ f.natDegree :=
    Polynomial.natDegree_C_mul_le _ _
  have hright_deg : (C β * g).natDegree = g.natDegree := by
    rw [Polynomial.natDegree_C_mul hβ.ne']
  have hlt : (C (1 - β) * f).natDegree < (C β * g).natDegree := by
    rw [hright_deg, hdeg]
    exact Nat.lt_succ_of_le hleft_le
  exact
    hasPosLeadingCoeff_add_of_natDegree_lt_right hlt
      (hasPosLeadingCoeff_C_mul hβ hg_pos)

/-- Positive closed-segment members of a compatible succ-degree pair are
nonzero and split. -/
theorem compatibleSuccDegree_closedSegment_isRealRooted_of_pos
    {f g : ℝ[X]}
    (hcomp : Compatible f g)
    (hg_pos : HasPosLeadingCoeff g)
    (hdeg : g.natDegree = f.natDegree + 1)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1) :
    (C (1 - β) * f + C β * g) ≠ 0 ∧
      (C (1 - β) * f + C β * g).Splits := by
  have hleft_nonneg : 0 ≤ 1 - β := by linarith
  rcases hcomp (1 - β) β hleft_nonneg hβ0.le with hzero | hrr
  · exact False.elim <|
      (succDegree_closedSegment_hasPosLeadingCoeff_of_pos hg_pos hdeg hβ0).ne_zero
        hzero
  · exact hrr

/-- Positive closed-segment members of a compatible succ-degree pair have
exactly the larger endpoint number of roots. -/
theorem compatibleSuccDegree_closedSegment_roots_card_eq_right_of_pos
    {f g : ℝ[X]}
    (hcomp : Compatible f g)
    (hg_pos : HasPosLeadingCoeff g)
    (hdeg : g.natDegree = f.natDegree + 1)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1) :
    (C (1 - β) * f + C β * g).roots.card = g.natDegree := by
  rw [card_roots_of_splits
    (compatibleSuccDegree_closedSegment_isRealRooted_of_pos
      hcomp hg_pos hdeg hβ0 hβ1).2]
  exact succDegree_closedSegment_natDegree_eq_right_of_pos hg_pos hdeg hβ0

/-- Positive closed-segment members of a compatible succ-degree pair have one
more root than the lower-degree endpoint. -/
theorem compatibleSuccDegree_closedSegment_roots_card_eq_succ_of_pos
    {f g : ℝ[X]}
    (hcomp : Compatible f g)
    (hg_pos : HasPosLeadingCoeff g)
    (hdeg : g.natDegree = f.natDegree + 1)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1) :
    (C (1 - β) * f + C β * g).roots.card = f.natDegree + 1 := by
  rw [compatibleSuccDegree_closedSegment_roots_card_eq_right_of_pos
    hcomp hg_pos hdeg hβ0 hβ1, hdeg]

/-- Interior closed-segment members are nonzero scalar multiples of the right
pencil `f + μ g`, with `μ = β / (1 - β)`. -/
theorem closedSegment_eq_C_mul_add_right
    {f g : ℝ[X]} {β : ℝ} (hβ : β < 1) :
    C (1 - β) * f + C β * g =
      C (1 - β) * (f + C (β / (1 - β)) * g) := by
  have hden : 1 - β ≠ 0 := by linarith
  rw [mul_add, ← mul_assoc, ← C_mul]
  have hmul : (1 - β) * (β / (1 - β)) = β := by
    field_simp [hden]
  rw [hmul]

/-- Passing from an interior closed-segment member to the corresponding right
pencil preserves the root multiset. -/
theorem closedSegment_roots_eq_add_right_of_lt_one
    {f g : ℝ[X]} {β : ℝ} (hβ : β < 1) :
    (C (1 - β) * f + C β * g).roots =
      (f + C (β / (1 - β)) * g).roots := by
  rw [closedSegment_eq_C_mul_add_right hβ,
    Polynomial.roots_C_mul _ (by linarith : 1 - β ≠ 0)]

/-- Passing from an interior closed-segment member to the corresponding right
pencil preserves the root predicate at every threshold. -/
theorem closedSegment_isRoot_iff_add_right_of_lt_one
    {f g : ℝ[X]} {β x : ℝ} (hβ : β < 1) :
    (C (1 - β) * f + C β * g).IsRoot x ↔
      (f + C (β / (1 - β)) * g).IsRoot x := by
  rw [closedSegment_eq_C_mul_add_right hβ]
  simp [Polynomial.IsRoot.def, (by linarith : 1 - β ≠ 0)]

/-- Multiplying by a nonzero scalar preserves simple real roots. -/
theorem HasSimpleRoots.C_mul {p : ℝ[X]} {c : ℝ}
    (hp : HasSimpleRoots p) (hc : c ≠ 0) :
    HasSimpleRoots (C c * p) := by
  intro x hx
  have hp_ne : p ≠ 0 := hp.ne_zero
  have hcp_ne : C c * p ≠ 0 := mul_ne_zero (C_ne_zero.mpr hc) hp_ne
  rw [Polynomial.rootMultiplicity_mul hcp_ne, Polynomial.rootMultiplicity_C]
  have hroot_p : p.IsRoot x := by
    simpa [Polynomial.IsRoot.def, eval_mul, eval_C, hc] using hx
  rw [hp x hroot_p]

private lemma div_one_sub_inj_of_lt_one {β γ : ℝ}
    (hβ : β < 1) (hγ : γ < 1)
    (h : β / (1 - β) = γ / (1 - γ)) :
    β = γ := by
  have hβne : 1 - β ≠ 0 := by linarith
  have hγne : 1 - γ ≠ 0 := by linarith
  have hmul : β * (1 - γ) = γ * (1 - β) :=
    (div_eq_div_iff hβne hγne).mp h
  linarith

/-- Positive interior closed-segment form of the no-common right-pencil
parameter formula. -/
theorem closedSegment_isRoot_iff_parameter_eq_of_no_common
    {f g : ℝ[X]}
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    {β x : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    (C (1 - β) * f + C β * g).IsRoot x ↔
      β / (1 - β) = -f.eval x / g.eval x := by
  rw [closedSegment_isRoot_iff_add_right_of_lt_one hβ1]
  exact isRoot_add_right_iff_parameter_eq_of_no_common hno
    (div_pos hβ0 (sub_pos.mpr hβ1))

/-- Every interior closed-segment member of a no-common positive-combination
family has simple roots. -/
theorem PosComboRealRooted.hasSimpleRoots_closedSegment
    {f g : ℝ[X]}
    (hfg : PosComboRealRooted f g)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    HasSimpleRoots (C (1 - β) * f + C β * g) := by
  rw [closedSegment_eq_C_mul_add_right hβ1]
  exact
    (hfg.hasSimpleRoots_add_right hno (div_pos hβ0 (sub_pos.mpr hβ1))).C_mul
      (by linarith : 1 - β ≠ 0)

/-- A fixed threshold can be a root of a no-common closed-segment family for
at most one parameter below the right endpoint. -/
theorem closedSegment_parameter_unique_of_isRoot_of_no_common
    {f g : ℝ[X]}
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    {β γ x : ℝ}
    (hβ : β < 1) (hγ : γ < 1)
    (hrootβ : (C (1 - β) * f + C β * g).IsRoot x)
    (hrootγ : (C (1 - γ) * f + C γ * g).IsRoot x) :
    β = γ := by
  have hrootβ_right :
      (f + C (β / (1 - β)) * g).IsRoot x :=
    (closedSegment_isRoot_iff_add_right_of_lt_one hβ).mp hrootβ
  have hrootγ_right :
      (f + C (γ / (1 - γ)) * g).IsRoot x :=
    (closedSegment_isRoot_iff_add_right_of_lt_one hγ).mp hrootγ
  exact div_one_sub_inj_of_lt_one hβ hγ <|
    pencil_parameter_unique_of_isRoot_of_no_common hno hrootβ_right hrootγ_right

/-- A root of an interior no-common closed-segment member carries the same
endpoint nonvanishing, parameter formula, and simple-crossing derivative data
as the corresponding right-pencil member. -/
theorem PosComboRealRooted.root_crossing_data_closedSegment
    {f g : ℝ[X]}
    (hfg : PosComboRealRooted f g)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    {β x : ℝ}
    (hβ0 : 0 < β) (hβ1 : β < 1)
    (hroot : (C (1 - β) * f + C β * g).IsRoot x) :
    g.eval x ≠ 0 ∧ f.eval x ≠ 0 ∧
      β / (1 - β) = -f.eval x / g.eval x ∧
      (C (1 - β) * f + C β * g).derivative.eval x ≠ 0 := by
  have hμ_pos : 0 < β / (1 - β) := div_pos hβ0 (sub_pos.mpr hβ1)
  have hroot_right :
      (f + C (β / (1 - β)) * g).IsRoot x :=
    (closedSegment_isRoot_iff_add_right_of_lt_one hβ1).mp hroot
  rcases hfg.root_crossing_data_add_right hno hμ_pos hroot_right with
    ⟨hgx, hfx, hμ_eq, hder_right⟩
  refine ⟨hgx, hfx, hμ_eq, ?_⟩
  have hscale :
      (C (1 - β) * f + C β * g).derivative =
        C (1 - β) * (f + C (β / (1 - β)) * g).derivative := by
    rw [closedSegment_eq_C_mul_add_right hβ1, derivative_C_mul]
  intro hder
  apply hder_right
  have hscaled_eval :
      (1 - β) * (f + C (β / (1 - β)) * g).derivative.eval x = 0 := by
    rw [hscale] at hder
    simpa [hscale, eval_mul, eval_C] using hder
  exact (mul_eq_zero.mp hscaled_eval).resolve_left (by linarith : 1 - β ≠ 0)

/-- The change of variables `β = μ / (μ + 1)` turns a nonnegative right-pencil
parameter into an interior closed-segment parameter and preserves the root
predicate. -/
theorem closedSegment_isRoot_iff_add_right_of_nonneg
    {f g : ℝ[X]} {μ x : ℝ} (hμ : 0 ≤ μ) :
    (C (1 - μ / (μ + 1)) * f + C (μ / (μ + 1)) * g).IsRoot x ↔
      (f + C μ * g).IsRoot x := by
  have hden_pos : 0 < μ + 1 := by linarith
  have hβlt : μ / (μ + 1) < 1 := by
    rw [div_lt_one hden_pos]
    linarith
  have hratio : (μ / (μ + 1)) / (1 - μ / (μ + 1)) = μ := by
    field_simp [hden_pos.ne']
    ring
  rw [closedSegment_isRoot_iff_add_right_of_lt_one hβlt, hratio]

/-- The change of variables `β = μ / (μ + 1)` preserves the root multiset
between a nonnegative right-pencil member and its closed-segment representative. -/
theorem closedSegment_roots_eq_add_right_of_nonneg
    {f g : ℝ[X]} {μ : ℝ} (hμ : 0 ≤ μ) :
    (C (1 - μ / (μ + 1)) * f + C (μ / (μ + 1)) * g).roots =
      (f + C μ * g).roots := by
  have hden_pos : 0 < μ + 1 := by linarith
  have hβlt : μ / (μ + 1) < 1 := by
    rw [div_lt_one hden_pos]
    linarith
  have hratio : (μ / (μ + 1)) / (1 - μ / (μ + 1)) = μ := by
    field_simp [hden_pos.ne']
    ring
  rw [closedSegment_roots_eq_add_right_of_lt_one hβlt, hratio]

/-- The change of variables `β = μ / (μ + 1)` preserves upper-threshold root
counts between a nonnegative right-pencil member and its closed-segment
representative. -/
theorem closedSegment_roots_gt_card_eq_add_right_of_nonneg
    {f g : ℝ[X]} {μ x : ℝ} (hμ : 0 ≤ μ) :
    ((C (1 - μ / (μ + 1)) * f + C (μ / (μ + 1)) * g).roots.filter
      (x < ·)).card =
      ((f + C μ * g).roots.filter (x < ·)).card := by
  rw [closedSegment_roots_eq_add_right_of_nonneg (f := f) (g := g) hμ]

/-- A no-root hypothesis on the nonnegative right family also controls the
reciprocal family near the larger-degree endpoint. -/
theorem rightFamily_not_isRoot_add_left_of_pos
    {f g : ℝ[X]} {ν x : ℝ} (hν : 0 < ν)
    (hno : ∀ {μ : ℝ}, 0 ≤ μ → ¬ (f + C μ * g).IsRoot x) :
    ¬ (g + C ν * f).IsRoot x := by
  intro hroot
  have hroot' : (f + C ν⁻¹ * g).IsRoot x :=
    (add_right_isRoot_iff_add_left_inv (f := g) (g := f)
      (μ := ν) (x := x) hν.ne').1 hroot
  exact hno (μ := ν⁻¹) (inv_nonneg.mpr hν.le) hroot'

/-- Same-sign endpoint evaluations rule out nonnegative right-family roots at
that threshold. -/
theorem rightFamily_not_isRoot_of_eval_mul_pos
    {f g : ℝ[X]} {x μ : ℝ} (hμ : 0 ≤ μ)
    (hprod : 0 < f.eval x * g.eval x) :
    ¬ (f + C μ * g).IsRoot x := by
  intro hroot
  have hroot_eval : f.eval x + μ * g.eval x = 0 := by
    simpa [Polynomial.IsRoot.def, eval_add, eval_mul, eval_C] using hroot
  have hf_ne : f.eval x ≠ 0 := by
    intro hf
    rw [hf, zero_mul] at hprod
    linarith
  by_cases hf_pos : 0 < f.eval x
  · have hg_pos : 0 < g.eval x := by nlinarith
    have hpos : 0 < f.eval x + μ * g.eval x := by nlinarith
    linarith
  · have hf_neg : f.eval x < 0 :=
      lt_of_le_of_ne (le_of_not_gt hf_pos) hf_ne
    have hg_neg : g.eval x < 0 := by nlinarith
    have hneg : f.eval x + μ * g.eval x < 0 := by nlinarith
    linarith

/-- If a common non-root threshold is never a root of the nonnegative
right-family, then the endpoint evaluations have the same sign. -/
theorem eval_mul_pos_of_no_rightFamily_isRoot
    {f g : ℝ[X]} {x : ℝ} (hxf : ¬ f.IsRoot x) (hxg : ¬ g.IsRoot x)
    (hno : ∀ {μ : ℝ}, 0 ≤ μ → ¬ (f + C μ * g).IsRoot x) :
    0 < f.eval x * g.eval x := by
  have hfx_eval : f.eval x ≠ 0 := by
    intro hfx
    exact hxf (by simpa [Polynomial.IsRoot.def] using hfx)
  have hgx_eval : g.eval x ≠ 0 := by
    intro hgx
    exact hxg (by simpa [Polynomial.IsRoot.def] using hgx)
  have hno_pos : ¬ ∃ μ : ℝ, 0 < μ ∧ (f + C μ * g).IsRoot x := by
    rintro ⟨μ, hμ, hroot⟩
    exact hno hμ.le hroot
  have hsign :
      (0 < f.eval x ↔ 0 < g.eval x) :=
    (not_exists_pos_isRoot_add_right_iff_eval_pos_iff hfx_eval hgx_eval).mp hno_pos
  rcases lt_or_gt_of_ne hfx_eval with hf_neg | hf_pos
  · have hg_neg : g.eval x < 0 := by
      by_contra hnot
      have hg_pos : 0 < g.eval x := lt_of_le_of_ne (le_of_not_gt hnot) hgx_eval.symm
      exact (not_lt_of_ge (le_of_lt hf_neg)) (hsign.mpr hg_pos)
    exact mul_pos_of_neg_of_neg hf_neg hg_neg
  · exact mul_pos hf_pos (hsign.mp hf_pos)

/-- If a common non-root threshold is never a root of the positive right-family,
then the endpoint evaluations have the same sign. -/
theorem eval_mul_pos_of_no_pos_rightFamily_isRoot
    {f g : ℝ[X]} {x : ℝ} (hxf : ¬ f.IsRoot x) (hxg : ¬ g.IsRoot x)
    (hno : ∀ μ : ℝ, 0 < μ → ¬ (f + C μ * g).IsRoot x) :
    0 < f.eval x * g.eval x := by
  refine eval_mul_pos_of_no_rightFamily_isRoot hxf hxg ?_
  intro μ hμ
  by_cases hμ0 : μ = 0
  · subst μ
    simpa using hxf
  · exact hno μ (lt_of_le_of_ne hμ (Ne.symm hμ0))

/-- At a common non-root threshold, nonvanishing of the nonnegative right
family is equivalent to same-sign endpoint evaluations. -/
theorem no_rightFamily_isRoot_iff_eval_mul_pos
    {f g : ℝ[X]} {x : ℝ} (hxf : ¬ f.IsRoot x) (hxg : ¬ g.IsRoot x) :
    (∀ {μ : ℝ}, 0 ≤ μ → ¬ (f + C μ * g).IsRoot x) ↔
      0 < f.eval x * g.eval x :=
  ⟨eval_mul_pos_of_no_rightFamily_isRoot hxf hxg,
    fun hprod {_} hμ => rightFamily_not_isRoot_of_eval_mul_pos hμ hprod⟩

/-- If a threshold is not a root anywhere on the closed segment, then it is
not a root of any nonnegative right-pencil member. -/
theorem closedSegment_not_isRoot_add_right_of_nonneg
    {f g : ℝ[X]} {μ x : ℝ} (hμ : 0 ≤ μ)
    (hseg : ∀ {β : ℝ}, 0 ≤ β → β ≤ 1 →
      ¬ (C (1 - β) * f + C β * g).IsRoot x) :
    ¬ (f + C μ * g).IsRoot x := by
  have hden_pos : 0 < μ + 1 := by linarith
  have hβ0 : 0 ≤ μ / (μ + 1) := div_nonneg hμ hden_pos.le
  have hβ1 : μ / (μ + 1) ≤ 1 := by
    rw [div_le_one hden_pos]
    linarith
  intro hroot
  have hseg_root : (C (1 - μ / (μ + 1)) * f + C (μ / (μ + 1)) * g).IsRoot x := by
    exact (closedSegment_isRoot_iff_add_right_of_nonneg (f := f) (g := g)
      (x := x) hμ).2 hroot
  exact hseg hβ0 hβ1 hseg_root

/-- At a common non-root threshold, closed-segment nonvanishing is equivalent
to same-sign endpoint evaluations. -/
theorem closedSegment_forall_not_isRoot_iff_eval_mul_pos
    {f g : ℝ[X]} {x : ℝ} (hxf : ¬ f.IsRoot x) (hxg : ¬ g.IsRoot x) :
    (∀ {β : ℝ}, 0 ≤ β → β ≤ 1 →
      ¬ (C (1 - β) * f + C β * g).IsRoot x) ↔
      0 < f.eval x * g.eval x := by
  constructor
  · intro hseg
    have hno : ∀ {μ : ℝ}, 0 ≤ μ → ¬ (f + C μ * g).IsRoot x := by
      intro μ hμ
      exact closedSegment_not_isRoot_add_right_of_nonneg hμ hseg
    exact eval_mul_pos_of_no_rightFamily_isRoot hxf hxg hno
  · intro hprod β hβ0 hβ1
    exact closedSegment_not_isRoot_of_eval_mul_pos hβ0 hβ1 hprod

/-- The right-pencil no-gap-two theorem implies the closed-segment no-gap-two
theorem by the parameter change `β = μ / (μ + 1)`. -/
theorem compatibleSuccDegreeClosedSegmentNoGapTwo_of_rightFamily
    (hright : CompatibleSuccDegreeRightFamilyNoGapTwoStatement) :
    CompatibleSuccDegreeClosedSegmentNoGapTwoStatement := by
  intro f g hcomp hf_pos hg_pos hdeg hf_split x hxf hxg hseg
  exact hright hcomp hf_pos hg_pos hdeg hf_split x hxf hxg
    (fun {_} hμ => closedSegment_not_isRoot_add_right_of_nonneg hμ hseg)

/-- The endpoint-sign no-gap-two theorem implies the right-family no-gap-two
theorem because the right-family no-root hypothesis is exactly same-sign
endpoint evaluation at a common non-root threshold. -/
theorem compatibleSuccDegreeRightFamilyNoGapTwo_of_endpointSign
    (hsign : CompatibleSuccDegreeEndpointSignNoGapTwoStatement) :
    CompatibleSuccDegreeRightFamilyNoGapTwoStatement := by
  intro f g hcomp hf_pos hg_pos hdeg hf_split x hxf hxg hno
  exact hsign hcomp hf_pos hg_pos hdeg hf_split x hxf hxg
    (eval_mul_pos_of_no_rightFamily_isRoot hxf hxg hno)

/-- The right-family no-gap-two theorem implies the endpoint-sign no-gap-two
theorem because same-sign endpoint evaluations rule out nonnegative
right-family roots at the fixed threshold. -/
theorem compatibleSuccDegreeEndpointSignNoGapTwo_of_rightFamily
    (hright : CompatibleSuccDegreeRightFamilyNoGapTwoStatement) :
    CompatibleSuccDegreeEndpointSignNoGapTwoStatement := by
  intro f g hcomp hf_pos hg_pos hdeg hf_split x hxf hxg hprod
  exact hright hcomp hf_pos hg_pos hdeg hf_split x hxf hxg
    (fun {_} hμ => rightFamily_not_isRoot_of_eval_mul_pos hμ hprod)

/-- The right-family and endpoint-sign no-gap-two targets are equivalent. -/
theorem compatibleSuccDegreeRightFamilyNoGapTwo_iff_endpointSign :
    CompatibleSuccDegreeRightFamilyNoGapTwoStatement ↔
      CompatibleSuccDegreeEndpointSignNoGapTwoStatement :=
  ⟨compatibleSuccDegreeEndpointSignNoGapTwo_of_rightFamily,
    compatibleSuccDegreeRightFamilyNoGapTwo_of_endpointSign⟩

/-- The all-combinations target contains the signed right-pencil family. -/
theorem compatibleSuccDegreeSignedRightFamily_of_allCombo
    (hallTarget : CompatibleSuccDegreeAllComboStatement) :
    CompatibleSuccDegreeSignedRightFamilyStatement := by
  intro f g hcomp hf_pos hg_pos hdeg hf_split μ
  simpa using hallTarget hcomp hf_pos hg_pos hdeg hf_split 1 μ

/-- The all-combinations target implies the negative right-pencil target. -/
theorem compatibleSuccDegreeNegativeRightFamily_of_allCombo
    (hallTarget : CompatibleSuccDegreeAllComboStatement) :
    CompatibleSuccDegreeNegativeRightFamilyStatement := by
  intro f g hcomp hf_pos hg_pos hdeg hf_split μ _
  exact compatibleSuccDegreeSignedRightFamily_of_allCombo hallTarget
    hcomp hf_pos hg_pos hdeg hf_split μ

/-- The all-combinations target implies the nonnegative-coefficient negative
right-pencil target. -/
theorem compatibleSuccDegreeNegativeRightFamilyNonneg_of_allCombo
    (hallTarget : CompatibleSuccDegreeAllComboStatement) :
    CompatibleSuccDegreeNegativeRightFamilyNonnegStatement := by
  intro f g hcomp hf_pos hg_pos _ _ hdeg hf_split μ hμ
  exact compatibleSuccDegreeNegativeRightFamily_of_allCombo hallTarget
    hcomp hf_pos hg_pos hdeg hf_split μ hμ

/-- Degree-zero base case for the nonnegative-coefficient negative right-pencil
target.  If the lower-degree endpoint is constant, the pencil has degree at
most one for every parameter. -/
theorem compatibleSuccDegreeNegativeRightFamilyNonneg_of_natDegree_eq_zero
    {f g : ℝ[X]}
    (_hcomp : Compatible f g)
    (_hf_pos : HasPosLeadingCoeff f)
    (_hg_pos : HasPosLeadingCoeff g)
    (_hfnn : HasNonnegCoeffs f)
    (_hgnn : HasNonnegCoeffs g)
    (hdeg : g.natDegree = f.natDegree + 1)
    (_hf_split : f.Splits)
    (hfdeg : f.natDegree = 0)
    (μ : ℝ) (_hμ : μ < 0) :
    (f + C μ * g).Splits := by
  apply Polynomial.Splits.of_natDegree_le_one
  calc
    (f + C μ * g).natDegree ≤ max f.natDegree (C μ * g).natDegree :=
      Polynomial.natDegree_add_le _ _
    _ ≤ 1 := by
      have hmul : (C μ * g).natDegree ≤ g.natDegree :=
        Polynomial.natDegree_C_mul_le μ g
      rw [hdeg, hfdeg] at hmul
      rw [hfdeg]
      exact max_le (by norm_num) (by simpa using hmul)

/-- The signed right-pencil family gives the whole all-combinations target by
scaling every nonzero left coefficient to `1`. -/
theorem compatibleSuccDegreeAllCombo_of_signedRightFamily
    (hsigned : CompatibleSuccDegreeSignedRightFamilyStatement) :
    CompatibleSuccDegreeAllComboStatement := by
  intro f g hcomp hf_pos hg_pos hdeg hf_split α β
  by_cases hα : α = 0
  · have hfg : PosComboRealRooted f g :=
      hcomp.toPosComboRealRooted hf_pos hg_pos
    have hg_split : g.Splits :=
      (hfg.isRealRooted_right_of_succDegree hf_pos hg_pos hdeg).2
    simpa [hα] using (Polynomial.Splits.C (R := ℝ) β).mul hg_split
  · have hright : (f + C (β / α) * g).Splits :=
      hsigned hcomp hf_pos hg_pos hdeg hf_split (β / α)
    have hscale : C α * (f + C (β / α) * g) = C α * f + C β * g := by
      rw [mul_add]
      congr 1
      have hαβ : α * (β / α) = β := by
        field_simp [hα]
      calc
        C α * (C (β / α) * g) = C (α * (β / α)) * g := by grind
        _ = C β * g := by rw [hαβ]
    rw [← hscale]
    exact (Polynomial.Splits.C (R := ℝ) α).mul hright

/-- It is enough to prove the negative half of the right pencil: compatibility
already gives the nonnegative half. -/
theorem compatibleSuccDegreeSignedRightFamily_of_negativeRightFamily
    (hneg : CompatibleSuccDegreeNegativeRightFamilyStatement) :
    CompatibleSuccDegreeSignedRightFamilyStatement := by
  intro f g hcomp hf_pos hg_pos hdeg hf_split μ
  by_cases hμ : 0 ≤ μ
  · rcases hcomp 1 μ zero_le_one hμ with hzero | hrr
    · have htarget_zero : f + C μ * g = 0 := by simpa using hzero
      simp [htarget_zero]
    · simpa using hrr.2
  · exact hneg hcomp hf_pos hg_pos hdeg hf_split μ (lt_of_not_ge hμ)

/-- Splitting descends through translation by `X + r`. -/
lemma splits_of_comp_X_add_C_splits
    {p : ℝ[X]} (r : ℝ) (hp : (p.comp (X + C r)).Splits) :
    p.Splits := by
  by_cases hp0 : p = 0
  · simp [hp0]
  · have hq0 : p.comp (X + C r) ≠ 0 := (Polynomial.comp_X_add_C_ne_zero_iff).2 hp0
    have hback := isRealRooted_comp_X_add_C hq0 hp (-r)
    simpa [Polynomial.comp_assoc, add_assoc, add_left_comm, add_comm, sub_eq_add_neg]
      using hback.2

/-- The coefficient-free negative right-pencil target reduces to the
nonnegative-coefficient target by translating both endpoints far enough that
their roots are nonpositive. -/
theorem compatibleSuccDegreeNegativeRightFamily_of_nonnegShift
    (hneg : CompatibleSuccDegreeNegativeRightFamilyNonnegStatement) :
    CompatibleSuccDegreeNegativeRightFamilyStatement := by
  intro f g hcomp hf_pos hg_pos hdeg hf_split μ hμ
  have hfg : PosComboRealRooted f g :=
    hcomp.toPosComboRealRooted hf_pos hg_pos
  have hg_split : g.Splits :=
    (hfg.isRealRooted_right_of_succDegree hf_pos hg_pos hdeg).2
  obtain ⟨rf, hrf⟩ := exists_root_upper_bound f
  obtain ⟨rg, hrg⟩ := exists_root_upper_bound g
  let r : ℝ := max rf rg
  let f' : ℝ[X] := f.comp (X + C r)
  let g' : ℝ[X] := g.comp (X + C r)
  have hcomp' : Compatible f' g' := by
    simpa [f', g'] using hcomp.comp_X_add_C r
  have hf'_pos : HasPosLeadingCoeff f' := by
    simpa [f'] using hf_pos.comp_X_add_C r
  have hg'_pos : HasPosLeadingCoeff g' := by
    simpa [g'] using hg_pos.comp_X_add_C r
  have hfnn : HasNonnegCoeffs f' := by
    refine hasNonnegCoeffs_comp_X_add_C_of_roots_le hf_pos hf_split ?_
    grind
  have hgnn : HasNonnegCoeffs g' := by
    refine hasNonnegCoeffs_comp_X_add_C_of_roots_le hg_pos hg_split ?_
    grind
  have hdeg' : g'.natDegree = f'.natDegree + 1 := by
    simpa [f', g', Polynomial.natDegree_comp] using hdeg
  have hf'_split : f'.Splits :=
    (isRealRooted_comp_X_add_C hf_pos.ne_zero hf_split r).2
  have hshift : (f' + C μ * g').Splits :=
    hneg hcomp' hf'_pos hg'_pos hfnn hgnn hdeg' hf'_split μ hμ
  have htranslate :
      (f + C μ * g).comp (X + C r) = f' + C μ * g' := by
    simp [f', g']
  exact splits_of_comp_X_add_C_splits r (by simpa [htranslate] using hshift)

/-- The negative right-pencil target implies the all-combinations target. -/
theorem compatibleSuccDegreeAllCombo_of_negativeRightFamily
    (hneg : CompatibleSuccDegreeNegativeRightFamilyStatement) :
    CompatibleSuccDegreeAllComboStatement :=
  compatibleSuccDegreeAllCombo_of_signedRightFamily
    (compatibleSuccDegreeSignedRightFamily_of_negativeRightFamily hneg)

/-- The nonnegative-coefficient negative right-pencil target implies the
all-combinations target. -/
theorem compatibleSuccDegreeAllCombo_of_negativeRightFamily_nonnegShift
    (hneg : CompatibleSuccDegreeNegativeRightFamilyNonnegStatement) :
    CompatibleSuccDegreeAllComboStatement :=
  compatibleSuccDegreeAllCombo_of_negativeRightFamily
    (compatibleSuccDegreeNegativeRightFamily_of_nonnegShift hneg)

/-- The compatible succ-degree all-combinations target implies the forced
proper-position orientation, by Obreschkoff's converse and degree orientation.
-/
theorem compatibleSuccDegreePrec_of_allCombo
    (hallTarget : CompatibleSuccDegreeAllComboStatement) :
    CompatibleSuccDegreePrecStatement := by
  intro f g hcomp hf_pos hg_pos hdeg hf_split
  have hall : AllComboRealRooted f g :=
    hallTarget hcomp hf_pos hg_pos hdeg hf_split
  have hg_rr : (g ≠ 0 ∧ g.Splits) :=
    hall.isRealRooted_right hg_pos.ne_zero
  have horient : Prec f g ∨ Prec g f :=
    prec_of_allComboRealRooted
      hf_pos.ne_zero hf_split hg_rr.1 hg_rr.2 hall (Or.inl hdeg.symm)
  exact prec_forward_of_orientation_of_succDegree hdeg horient

/-- The signed right-pencil target implies the forced succ-degree
orientation. -/
theorem compatibleSuccDegreePrec_of_signedRightFamily
    (hsigned : CompatibleSuccDegreeSignedRightFamilyStatement) :
    CompatibleSuccDegreePrecStatement :=
  compatibleSuccDegreePrec_of_allCombo
    (compatibleSuccDegreeAllCombo_of_signedRightFamily hsigned)

/-- The negative right-pencil target implies the forced succ-degree
orientation. -/
theorem compatibleSuccDegreePrec_of_negativeRightFamily
    (hneg : CompatibleSuccDegreeNegativeRightFamilyStatement) :
    CompatibleSuccDegreePrecStatement :=
  compatibleSuccDegreePrec_of_allCombo
    (compatibleSuccDegreeAllCombo_of_negativeRightFamily hneg)

/-- The nonnegative-coefficient negative right-pencil target implies the forced
succ-degree orientation. -/
theorem compatibleSuccDegreePrec_of_negativeRightFamily_nonnegShift
    (hneg : CompatibleSuccDegreeNegativeRightFamilyNonnegStatement) :
    CompatibleSuccDegreePrecStatement :=
  compatibleSuccDegreePrec_of_negativeRightFamily
    (compatibleSuccDegreeNegativeRightFamily_of_nonnegShift hneg)

/-- The no-common positive-combination orientation core implies the
coefficient-free compatible succ-degree orientation target.  Shared roots are
handled by the existing positive-combination common-root induction, and the
succ-degree hypothesis selects the forward orientation. -/
theorem compatibleSuccDegreePrec_of_noCommonOrientation
    (hstep : PosComboNoCommonOrientationStatement) :
    CompatibleSuccDegreePrecStatement := by
  intro f g hcomp hf_pos hg_pos hdeg _hf_split
  have hfg : PosComboRealRooted f g :=
    hcomp.toPosComboRealRooted hf_pos hg_pos
  have horient : Prec f g ∨ Prec g f :=
    PosComboRealRooted.prec_or_revPrec_of_posComboRealRooted_of_no_common
      (hstep := fun {f g} hfg hf_pos hg_pos hdeg_lo hdeg_hi hno =>
        hstep hfg hf_pos hg_pos hdeg_lo hdeg_hi hno)
      hfg hf_pos hg_pos (by lia) (by lia)
  exact prec_forward_of_orientation_of_succDegree hdeg horient

/-- The exact lower-count endpoint comparison implies the lower-threshold
endpoint-sign exact gap obstruction. -/
theorem compatibleSuccDegreeEndpointSignLowerNoGap_of_lowerCountEq
    (hcount : CompatibleSuccDegreeEndpointSignLowerCountEqStatement) :
    CompatibleSuccDegreeEndpointSignLowerNoGapStatement := by
  intro f g hcomp hf_pos hg_pos hdeg hf_split x hxf hxg hprod
  have hgf :=
    hcount hcomp hf_pos hg_pos hdeg hf_split x hxf hxg hprod
  constructor <;> intro hbad <;> linarith

/-- The lower-threshold endpoint-sign target implies the upper-threshold
endpoint-sign target by exact complement-count arithmetic. -/
theorem compatibleSuccDegreeEndpointSignNoGapTwo_of_lower
    (hlower : CompatibleSuccDegreeEndpointSignLowerNoGapStatement) :
    CompatibleSuccDegreeEndpointSignNoGapTwoStatement := by
  intro f g hcomp hf_pos hg_pos hdeg hf_split x hxf hxg hprod
  have hg_split : g.Splits := (hcomp.isRealRooted_right hg_pos).2
  obtain ⟨hgf_ne3, hfg_ne1⟩ :=
    hlower hcomp hf_pos hg_pos hdeg hf_split x hxf hxg hprod
  constructor
  · intro hcount
    exact hgf_ne3 <|
      (succDegree_roots_gt_count_sub_eq_two_iff_roots_le_rev_sub_eq_three
        hf_split hg_split hdeg x).mp hcount
  · intro hcount
    exact hfg_ne1 <|
      (succDegree_rev_roots_gt_count_sub_eq_two_iff_roots_le_sub_eq_one
        hf_split hg_split hdeg x).mp hcount

/-- The exact lower-count endpoint comparison implies the upper-threshold
endpoint-sign exact gap-two obstruction. -/
theorem compatibleSuccDegreeEndpointSignNoGapTwo_of_lowerCountEq
    (hcount : CompatibleSuccDegreeEndpointSignLowerCountEqStatement) :
    CompatibleSuccDegreeEndpointSignNoGapTwoStatement :=
  compatibleSuccDegreeEndpointSignNoGapTwo_of_lower
    (compatibleSuccDegreeEndpointSignLowerNoGap_of_lowerCountEq hcount)

/-- The lower-threshold endpoint-sign target implies the right-family
no-gap-two theorem. -/
theorem compatibleSuccDegreeRightFamilyNoGapTwo_of_endpointSignLower
    (hlower : CompatibleSuccDegreeEndpointSignLowerNoGapStatement) :
    CompatibleSuccDegreeRightFamilyNoGapTwoStatement :=
  compatibleSuccDegreeRightFamilyNoGapTwo_of_endpointSign
    (compatibleSuccDegreeEndpointSignNoGapTwo_of_lower hlower)

/-- The exact lower-count endpoint comparison implies the right-family
no-gap-two theorem. -/
theorem compatibleSuccDegreeRightFamilyNoGapTwo_of_lowerCountEq
    (hcount : CompatibleSuccDegreeEndpointSignLowerCountEqStatement) :
    CompatibleSuccDegreeRightFamilyNoGapTwoStatement :=
  compatibleSuccDegreeRightFamilyNoGapTwo_of_endpointSign
    (compatibleSuccDegreeEndpointSignNoGapTwo_of_lowerCountEq hcount)

/-- The endpoint-sign no-gap-two theorem implies the closed-segment
no-gap-two theorem. -/
theorem compatibleSuccDegreeClosedSegmentNoGapTwo_of_endpointSign
    (hsign : CompatibleSuccDegreeEndpointSignNoGapTwoStatement) :
    CompatibleSuccDegreeClosedSegmentNoGapTwoStatement := by
  intro f g hcomp hf_pos hg_pos hdeg hf_split x hxf hxg hseg
  exact hsign hcomp hf_pos hg_pos hdeg hf_split x hxf hxg <|
    (closedSegment_forall_not_isRoot_iff_eval_mul_pos hxf hxg).mp hseg

/-- The closed-segment no-gap-two theorem implies the endpoint-sign
no-gap-two theorem because same-sign endpoint evaluations rule out
closed-segment roots at the fixed threshold. -/
theorem compatibleSuccDegreeEndpointSignNoGapTwo_of_closedSegment
    (hclosed : CompatibleSuccDegreeClosedSegmentNoGapTwoStatement) :
    CompatibleSuccDegreeEndpointSignNoGapTwoStatement := by
  intro f g hcomp hf_pos hg_pos hdeg hf_split x hxf hxg hprod
  exact hclosed hcomp hf_pos hg_pos hdeg hf_split x hxf hxg
    (fun {_} hβ0 hβ1 => closedSegment_not_isRoot_of_eval_mul_pos hβ0 hβ1 hprod)

/-- The closed-segment and endpoint-sign no-gap-two targets are equivalent. -/
theorem compatibleSuccDegreeClosedSegmentNoGapTwo_iff_endpointSign :
    CompatibleSuccDegreeClosedSegmentNoGapTwoStatement ↔
      CompatibleSuccDegreeEndpointSignNoGapTwoStatement :=
  ⟨compatibleSuccDegreeEndpointSignNoGapTwo_of_closedSegment,
    compatibleSuccDegreeClosedSegmentNoGapTwo_of_endpointSign⟩

/-- The lower-threshold endpoint-sign target implies the closed-segment
no-gap-two theorem. -/
theorem compatibleSuccDegreeClosedSegmentNoGapTwo_of_endpointSignLower
    (hlower : CompatibleSuccDegreeEndpointSignLowerNoGapStatement) :
    CompatibleSuccDegreeClosedSegmentNoGapTwoStatement :=
  compatibleSuccDegreeClosedSegmentNoGapTwo_of_endpointSign
    (compatibleSuccDegreeEndpointSignNoGapTwo_of_lower hlower)

/-- The exact lower-count endpoint comparison implies the closed-segment
no-gap-two theorem. -/
theorem compatibleSuccDegreeClosedSegmentNoGapTwo_of_lowerCountEq
    (hcount : CompatibleSuccDegreeEndpointSignLowerCountEqStatement) :
    CompatibleSuccDegreeClosedSegmentNoGapTwoStatement :=
  compatibleSuccDegreeClosedSegmentNoGapTwo_of_endpointSign
    (compatibleSuccDegreeEndpointSignNoGapTwo_of_lowerCountEq hcount)

/-- Closed-segment endpoint count equality excludes both exact upper
root-count gaps of two. -/
theorem compatibleSuccDegreeClosedSegmentNoGapTwo_of_countEq
    (hcount : CompatibleSuccDegreeClosedSegmentCountEqStatement) :
    CompatibleSuccDegreeClosedSegmentNoGapTwoStatement := by
  intro f g hcomp hf_pos hg_pos hdeg hf_split x hxf hxg hseg
  have hcard := hcount hcomp hf_pos hg_pos hdeg hf_split x hxf hxg hseg
  have hcard_int :
      ((f.roots.filter (x < ·)).card : ℤ) =
        (g.roots.filter (x < ·)).card := by
    exact_mod_cast hcard
  constructor <;> intro hgap <;> linarith

/-- Closed-segment endpoint count equality implies the exact lower-threshold
endpoint-sign comparison. -/
theorem compatibleSuccDegreeEndpointSignLowerCountEq_of_closedSegmentCountEq
    (hcount : CompatibleSuccDegreeClosedSegmentCountEqStatement) :
    CompatibleSuccDegreeEndpointSignLowerCountEqStatement := by
  intro f g hcomp hf_pos hg_pos hdeg hf_split x hxf hxg hprod
  have hseg : ∀ {β : ℝ}, 0 ≤ β → β ≤ 1 →
      ¬ (C (1 - β) * f + C β * g).IsRoot x := by
    intro β hβ0 hβ1
    exact closedSegment_not_isRoot_of_eval_mul_pos hβ0 hβ1 hprod
  have hgt := hcount hcomp hf_pos hg_pos hdeg hf_split x hxf hxg hseg
  have hg_split : g.Splits := (hcomp.isRealRooted_right hg_pos).2
  have hfpart := card_roots_filter_gt_add_le_of_splits hf_split x
  have hgpart := card_roots_filter_gt_add_le_of_splits hg_split x
  have hgtZ :
      ((f.roots.filter (x < ·)).card : ℤ) =
        (g.roots.filter (x < ·)).card := by
    exact_mod_cast hgt
  have hfpartZ :
      ((f.roots.filter (x < ·)).card : ℤ) +
          (f.roots.filter (· ≤ x)).card =
        f.natDegree := by
    exact_mod_cast hfpart
  have hgpartZ :
      ((g.roots.filter (x < ·)).card : ℤ) +
          (g.roots.filter (· ≤ x)).card =
        g.natDegree := by
    exact_mod_cast hgpart
  have hdegZ : (g.natDegree : ℤ) = (f.natDegree : ℤ) + 1 := by
    exact_mod_cast hdeg
  linarith

/-- The exact lower-threshold endpoint-sign comparison implies closed-segment
endpoint count equality. -/
theorem compatibleSuccDegreeClosedSegmentCountEq_of_lowerCountEq
    (hcount : CompatibleSuccDegreeEndpointSignLowerCountEqStatement) :
    CompatibleSuccDegreeClosedSegmentCountEqStatement := by
  intro f g hcomp hf_pos hg_pos hdeg hf_split x hxf hxg hseg
  have hprod : 0 < f.eval x * g.eval x :=
    (closedSegment_forall_not_isRoot_iff_eval_mul_pos hxf hxg).mp hseg
  have hle := hcount hcomp hf_pos hg_pos hdeg hf_split x hxf hxg hprod
  have hg_split : g.Splits := (hcomp.isRealRooted_right hg_pos).2
  have hfpart := card_roots_filter_gt_add_le_of_splits hf_split x
  have hgpart := card_roots_filter_gt_add_le_of_splits hg_split x
  have hfpartZ :
      ((f.roots.filter (x < ·)).card : ℤ) +
          (f.roots.filter (· ≤ x)).card =
        f.natDegree := by
    exact_mod_cast hfpart
  have hgpartZ :
      ((g.roots.filter (x < ·)).card : ℤ) +
          (g.roots.filter (· ≤ x)).card =
        g.natDegree := by
    exact_mod_cast hgpart
  have hdegZ : (g.natDegree : ℤ) = (f.natDegree : ℤ) + 1 := by
    exact_mod_cast hdeg
  have hgtZ :
      ((f.roots.filter (x < ·)).card : ℤ) =
        (g.roots.filter (x < ·)).card := by
    linarith
  exact_mod_cast hgtZ

/-- The closed-segment endpoint count-equality target is equivalent to the
exact lower-threshold endpoint-sign count target. -/
theorem compatibleSuccDegreeClosedSegmentCountEq_iff_lowerCountEq :
    CompatibleSuccDegreeClosedSegmentCountEqStatement ↔
      CompatibleSuccDegreeEndpointSignLowerCountEqStatement :=
  ⟨compatibleSuccDegreeEndpointSignLowerCountEq_of_closedSegmentCountEq,
    compatibleSuccDegreeClosedSegmentCountEq_of_lowerCountEq⟩

/-- Closed-segment endpoint count equality gives interval count equality
between any two common non-root thresholds that are not crossed by the closed
segment.  This is the interval-count bookkeeping used in the
Chudnovsky--Seymour `3.3` route. -/
theorem compatibleSuccDegree_roots_Ioo_eq_of_closedSegmentCountEq
    (hcount : CompatibleSuccDegreeClosedSegmentCountEqStatement)
    {f g : ℝ[X]}
    (hcomp : Compatible f g)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hdeg : g.natDegree = f.natDegree + 1)
    (hf_split : f.Splits)
    {a b : ℝ} (hab : a ≤ b)
    (hfa : ¬ f.IsRoot a) (hga : ¬ g.IsRoot a)
    (hfb : ¬ f.IsRoot b) (hgb : ¬ g.IsRoot b)
    (hsega : ∀ {β : ℝ}, 0 ≤ β → β ≤ 1 →
      ¬ (C (1 - β) * f + C β * g).IsRoot a)
    (hsegb : ∀ {β : ℝ}, 0 ≤ β → β ≤ 1 →
      ¬ (C (1 - β) * f + C β * g).IsRoot b) :
    (f.roots.filter (fun r => a < r ∧ r < b)).card =
      (g.roots.filter (fun r => a < r ∧ r < b)).card :=
  card_roots_filter_Ioo_eq_of_card_filter_gt_eq
    hf_pos.ne_zero hg_pos.ne_zero hab hfb hgb
    (hcount hcomp hf_pos hg_pos hdeg hf_split a hfa hga hsega)
    (hcount hcomp hf_pos hg_pos hdeg hf_split b hfb hgb hsegb)

/-- The closed-segment no-gap-two theorem implies the compatible exact
gap-two obstruction, since an assumed exact gap two supplies the required
closed-segment nonvanishing by the endpoint sign lemma. -/
theorem compatibleSuccDegreeRootCountAboveNoGapTwo_of_closedSegment
    (hclosed : CompatibleSuccDegreeClosedSegmentNoGapTwoStatement) :
    CompatibleSuccDegreeRootCountAboveNoGapTwoStatement := by
  intro f g hcomp hf_pos hg_pos hdeg hf_split x hxf hxg
  constructor
  · intro hcount
    have hseg : ∀ {β : ℝ}, 0 ≤ β → β ≤ 1 →
        ¬ (C (1 - β) * f + C β * g).IsRoot x := by
      intro β hβ0 hβ1
      exact
        compatibleSuccDegree_closedSegment_not_isRoot_of_roots_gt_count_sub_eq_two
          hcomp hf_pos hg_pos hdeg hf_split hβ0 hβ1 hxf hxg hcount
    exact (hclosed hcomp hf_pos hg_pos hdeg hf_split x hxf hxg hseg).1 hcount
  · intro hcount
    have hseg : ∀ {β : ℝ}, 0 ≤ β → β ≤ 1 →
        ¬ (C (1 - β) * f + C β * g).IsRoot x := by
      intro β hβ0 hβ1
      exact
        compatibleSuccDegree_closedSegment_not_isRoot_of_rev_roots_gt_count_sub_eq_two
          hcomp hf_pos hg_pos hdeg hf_split hβ0 hβ1 hxf hxg hcount
    exact (hclosed hcomp hf_pos hg_pos hdeg hf_split x hxf hxg hseg).2 hcount

/-- A gap-at-most-two theorem plus the closed-segment no-gap-two theorem gives
the compatible succ-degree common-non-root upper root-count leaf. -/
theorem compatibleSuccDegreeRootCountAboveNonRoot_of_leTwo_of_closedSegment
    (hle2 : CompatibleSuccDegreeRootCountAboveLeTwoStatement)
    (hclosed : CompatibleSuccDegreeClosedSegmentNoGapTwoStatement) :
    CompatibleSuccDegreeRootCountAboveNonRootStatement :=
  compatibleSuccDegreeRootCountAboveNonRoot_of_leTwo_of_noGapTwo hle2
    (compatibleSuccDegreeRootCountAboveNoGapTwo_of_closedSegment hclosed)

/-- The right-pencil no-gap-two theorem implies the compatible exact gap-two
obstruction. -/
theorem compatibleSuccDegreeRootCountAboveNoGapTwo_of_rightFamily
    (hright : CompatibleSuccDegreeRightFamilyNoGapTwoStatement) :
    CompatibleSuccDegreeRootCountAboveNoGapTwoStatement :=
  compatibleSuccDegreeRootCountAboveNoGapTwo_of_closedSegment
    (compatibleSuccDegreeClosedSegmentNoGapTwo_of_rightFamily hright)

/-- The endpoint-sign no-gap-two theorem implies the compatible exact gap-two
obstruction. -/
theorem compatibleSuccDegreeRootCountAboveNoGapTwo_of_endpointSign
    (hsign : CompatibleSuccDegreeEndpointSignNoGapTwoStatement) :
    CompatibleSuccDegreeRootCountAboveNoGapTwoStatement :=
  compatibleSuccDegreeRootCountAboveNoGapTwo_of_rightFamily
    (compatibleSuccDegreeRightFamilyNoGapTwo_of_endpointSign hsign)

/-- The lower-threshold endpoint-sign target implies the compatible exact
gap-two obstruction. -/
theorem compatibleSuccDegreeRootCountAboveNoGapTwo_of_endpointSignLower
    (hlower : CompatibleSuccDegreeEndpointSignLowerNoGapStatement) :
    CompatibleSuccDegreeRootCountAboveNoGapTwoStatement :=
  compatibleSuccDegreeRootCountAboveNoGapTwo_of_endpointSign
    (compatibleSuccDegreeEndpointSignNoGapTwo_of_lower hlower)

/-- The exact lower-count endpoint comparison implies the compatible exact
gap-two obstruction. -/
theorem compatibleSuccDegreeRootCountAboveNoGapTwo_of_lowerCountEq
    (hcount : CompatibleSuccDegreeEndpointSignLowerCountEqStatement) :
    CompatibleSuccDegreeRootCountAboveNoGapTwoStatement :=
  compatibleSuccDegreeRootCountAboveNoGapTwo_of_endpointSign
    (compatibleSuccDegreeEndpointSignNoGapTwo_of_lowerCountEq hcount)

/-- Closed-segment endpoint count equality implies the compatible exact
gap-two obstruction. -/
theorem compatibleSuccDegreeRootCountAboveNoGapTwo_of_closedSegmentCountEq
    (hcount : CompatibleSuccDegreeClosedSegmentCountEqStatement) :
    CompatibleSuccDegreeRootCountAboveNoGapTwoStatement :=
  compatibleSuccDegreeRootCountAboveNoGapTwo_of_closedSegment
    (compatibleSuccDegreeClosedSegmentNoGapTwo_of_countEq hcount)

/-- A gap-at-most-two theorem plus the right-pencil no-gap-two theorem gives
the compatible succ-degree common-non-root upper root-count leaf. -/
theorem compatibleSuccDegreeRootCountAboveNonRoot_of_leTwo_of_rightFamily
    (hle2 : CompatibleSuccDegreeRootCountAboveLeTwoStatement)
    (hright : CompatibleSuccDegreeRightFamilyNoGapTwoStatement) :
    CompatibleSuccDegreeRootCountAboveNonRootStatement :=
  compatibleSuccDegreeRootCountAboveNonRoot_of_leTwo_of_noGapTwo hle2
    (compatibleSuccDegreeRootCountAboveNoGapTwo_of_rightFamily hright)

/-- A gap-at-most-two theorem plus the endpoint-sign no-gap-two theorem gives
the compatible succ-degree common-non-root upper root-count leaf. -/
theorem compatibleSuccDegreeRootCountAboveNonRoot_of_leTwo_of_endpointSign
    (hle2 : CompatibleSuccDegreeRootCountAboveLeTwoStatement)
    (hsign : CompatibleSuccDegreeEndpointSignNoGapTwoStatement) :
    CompatibleSuccDegreeRootCountAboveNonRootStatement :=
  compatibleSuccDegreeRootCountAboveNonRoot_of_leTwo_of_noGapTwo hle2
    (compatibleSuccDegreeRootCountAboveNoGapTwo_of_endpointSign hsign)

/-- A gap-at-most-two theorem plus the lower-threshold endpoint-sign target
gives the compatible succ-degree common-non-root upper root-count leaf. -/
theorem compatibleSuccDegreeRootCountAboveNonRoot_of_leTwo_of_endpointSignLower
    (hle2 : CompatibleSuccDegreeRootCountAboveLeTwoStatement)
    (hlower : CompatibleSuccDegreeEndpointSignLowerNoGapStatement) :
    CompatibleSuccDegreeRootCountAboveNonRootStatement :=
  compatibleSuccDegreeRootCountAboveNonRoot_of_leTwo_of_endpointSign hle2
    (compatibleSuccDegreeEndpointSignNoGapTwo_of_lower hlower)

/-- A gap-at-most-two theorem plus the exact lower-count endpoint comparison
gives the compatible succ-degree common-non-root upper root-count leaf. -/
theorem compatibleSuccDegreeRootCountAboveNonRoot_of_leTwo_of_lowerCountEq
    (hle2 : CompatibleSuccDegreeRootCountAboveLeTwoStatement)
    (hcount : CompatibleSuccDegreeEndpointSignLowerCountEqStatement) :
    CompatibleSuccDegreeRootCountAboveNonRootStatement :=
  compatibleSuccDegreeRootCountAboveNonRoot_of_leTwo_of_endpointSign hle2
    (compatibleSuccDegreeEndpointSignNoGapTwo_of_lowerCountEq hcount)

/-- If the threshold is never a root of a nonnegative right-pencil member, then
the forward upper root-count difference has even parity. -/
theorem succDegree_even_roots_gt_count_sub_of_no_rightFamily_isRoot
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfg : PosComboRealRooted f g) (hdeg : g.natDegree = f.natDegree + 1)
    (hf_split : f.Splits) {x : ℝ} (hxf : ¬ f.IsRoot x) (hxg : ¬ g.IsRoot x)
    (hno : ∀ {μ : ℝ}, 0 ≤ μ → ¬ (f + C μ * g).IsRoot x) :
    Even (((f.roots.filter (x < ·)).card : ℤ) -
        (g.roots.filter (x < ·)).card) := by
  rw [← Int.not_odd_iff_even]
  intro hodd
  obtain ⟨μ, hμ, hroot⟩ :=
    (succDegree_odd_roots_gt_count_sub_iff_exists_pos_isRoot_add_right
      hf_pos hg_pos hfg hdeg hf_split hxf hxg).mp hodd
  exact hno hμ.le hroot

/-- If the threshold is never a root of a nonnegative right-pencil member, then
the reverse upper root-count difference has even parity. -/
theorem succDegree_even_rev_roots_gt_count_sub_of_no_rightFamily_isRoot
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfg : PosComboRealRooted f g) (hdeg : g.natDegree = f.natDegree + 1)
    (hf_split : f.Splits) {x : ℝ} (hxf : ¬ f.IsRoot x) (hxg : ¬ g.IsRoot x)
    (hno : ∀ {μ : ℝ}, 0 ≤ μ → ¬ (f + C μ * g).IsRoot x) :
    Even (((g.roots.filter (x < ·)).card : ℤ) -
        (f.roots.filter (x < ·)).card) := by
  have h := succDegree_even_roots_gt_count_sub_of_no_rightFamily_isRoot
    hf_pos hg_pos hfg hdeg hf_split hxf hxg hno
  simpa [sub_eq_add_neg, add_comm] using h.neg

/-- Compatible-pair version of
`succDegree_even_roots_gt_count_sub_of_no_rightFamily_isRoot`. -/
theorem compatibleSuccDegree_even_roots_gt_count_sub_of_no_rightFamily_isRoot
    {f g : ℝ[X]}
    (hcomp : Compatible f g)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hdeg : g.natDegree = f.natDegree + 1)
    (hf_split : f.Splits) {x : ℝ} (hxf : ¬ f.IsRoot x) (hxg : ¬ g.IsRoot x)
    (hno : ∀ {μ : ℝ}, 0 ≤ μ → ¬ (f + C μ * g).IsRoot x) :
    Even (((f.roots.filter (x < ·)).card : ℤ) -
        (g.roots.filter (x < ·)).card) :=
  succDegree_even_roots_gt_count_sub_of_no_rightFamily_isRoot
    hf_pos hg_pos (hcomp.toPosComboRealRooted hf_pos hg_pos)
    hdeg hf_split hxf hxg hno

/-- Compatible-pair version of
`succDegree_even_rev_roots_gt_count_sub_of_no_rightFamily_isRoot`. -/
theorem compatibleSuccDegree_even_rev_roots_gt_count_sub_of_no_rightFamily_isRoot
    {f g : ℝ[X]}
    (hcomp : Compatible f g)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hdeg : g.natDegree = f.natDegree + 1)
    (hf_split : f.Splits) {x : ℝ} (hxf : ¬ f.IsRoot x) (hxg : ¬ g.IsRoot x)
    (hno : ∀ {μ : ℝ}, 0 ≤ μ → ¬ (f + C μ * g).IsRoot x) :
    Even (((g.roots.filter (x < ·)).card : ℤ) -
        (f.roots.filter (x < ·)).card) :=
  succDegree_even_rev_roots_gt_count_sub_of_no_rightFamily_isRoot
    hf_pos hg_pos (hcomp.toPosComboRealRooted hf_pos hg_pos)
    hdeg hf_split hxf hxg hno

/-- Succ-degree right-pencil parity bridge for lower root counts. Since `g` has
one more root than `f`, the lower root-count difference has even parity exactly
when the right pencil crosses zero at the threshold. -/
theorem succDegree_even_roots_le_count_sub_iff_exists_pos_isRoot_add_right
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfg : PosComboRealRooted f g) (hdeg : g.natDegree = f.natDegree + 1)
    (hf_split : f.Splits) {x : ℝ} (hxf : ¬ f.IsRoot x) (hxg : ¬ g.IsRoot x) :
    (Even (((f.roots.filter (· ≤ x)).card : ℤ) -
        (g.roots.filter (· ≤ x)).card) ↔
      ∃ μ : ℝ, 0 < μ ∧ (f + C μ * g).IsRoot x) := by
  have hg_split : g.Splits :=
    (hfg.isRealRooted_right_of_succDegree hf_pos hg_pos hdeg).2
  rw [even_int_nat_sub_iff_even_add]
  have hfpart := card_roots_filter_gt_add_le_of_splits hf_split x
  have hgpart :
      (g.roots.filter (x < ·)).card + (g.roots.filter (· ≤ x)).card =
        f.natDegree + 1 := by
    rw [card_roots_filter_gt_add_le_of_splits hg_split x, hdeg]
  exact (even_add_iff_odd_add_of_add_eq_succ hfpart hgpart).trans
    (sameDegree_odd_card_roots_gt_add_iff_exists_pos_isRoot_add_right
      hf_split hg_split hf_pos hg_pos hxf hxg)

/-- Succ-degree lower root-count parity in endpoint-sign form. -/
theorem succDegree_even_roots_le_count_sub_iff_eval_mul_neg
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfg : PosComboRealRooted f g) (hdeg : g.natDegree = f.natDegree + 1)
    (hf_split : f.Splits) {x : ℝ} (hxf : ¬ f.IsRoot x) (hxg : ¬ g.IsRoot x) :
    (Even (((f.roots.filter (· ≤ x)).card : ℤ) -
        (g.roots.filter (· ≤ x)).card) ↔ f.eval x * g.eval x < 0) := by
  have hfx_eval : f.eval x ≠ 0 := by
    intro hfx
    exact hxf (by simpa [Polynomial.IsRoot.def] using hfx)
  exact (succDegree_even_roots_le_count_sub_iff_exists_pos_isRoot_add_right
    hf_pos hg_pos hfg hdeg hf_split hxf hxg).trans
    (exists_pos_isRoot_add_right_iff_eval_mul_neg hfx_eval)

/-- The compatible succ-degree orientation target implies the exact
lower-count endpoint comparison.  The oriented `Prec` count bounds leave only
the cases `g_le - f_le = 0` and `g_le - f_le = 1`; same-sign endpoint
evaluations rule out the even zero case by the succ-degree lower-count parity
bridge. -/
theorem compatibleSuccDegreeEndpointSignLowerCountEq_of_prec
    (hprecTarget : CompatibleSuccDegreePrecStatement) :
    CompatibleSuccDegreeEndpointSignLowerCountEqStatement := by
  intro f g hcomp hf_pos hg_pos hdeg hf_split x hxf hxg hprod
  have hprec : Prec f g :=
    hprecTarget hcomp hf_pos hg_pos hdeg hf_split
  obtain ⟨hfg_le, hgf_le⟩ :=
    succDegreeRootCountLowerOriented_of_prec hprec hdeg x
  have hnot_even :
      ¬ Even (((f.roots.filter (· ≤ x)).card : ℤ) -
        (g.roots.filter (· ≤ x)).card) := by
    intro heven
    have hneg :=
      (succDegree_even_roots_le_count_sub_iff_eval_mul_neg
        hf_pos hg_pos (hcomp.toPosComboRealRooted hf_pos hg_pos)
        hdeg hf_split hxf hxg).mp heven
    linarith
  by_contra hne
  let d : ℤ :=
    ((g.roots.filter (· ≤ x)).card : ℤ) - (f.roots.filter (· ≤ x)).card
  have hd_nonneg : 0 ≤ d := by
    dsimp [d]
    linarith
  have hd_le_one : d ≤ 1 := by
    dsimp [d]
    linarith
  have hd_ne_one : d ≠ 1 := by
    simpa [d] using hne
  have hd_le_zero : d ≤ 0 :=
    Int.lt_add_one_iff.mp (lt_of_le_of_ne hd_le_one hd_ne_one)
  have hd_zero : d = 0 := le_antisymm hd_le_zero hd_nonneg
  have hfg_zero :
      ((f.roots.filter (· ≤ x)).card : ℤ) -
        (g.roots.filter (· ≤ x)).card = 0 := by
    dsimp [d] at hd_zero
    linarith
  exact hnot_even (by rw [hfg_zero]; norm_num)

/-- The compatible succ-degree all-combinations target implies the exact
lower-count endpoint comparison. -/
theorem compatibleSuccDegreeEndpointSignLowerCountEq_of_allCombo
    (hallTarget : CompatibleSuccDegreeAllComboStatement) :
    CompatibleSuccDegreeEndpointSignLowerCountEqStatement :=
  compatibleSuccDegreeEndpointSignLowerCountEq_of_prec
    (compatibleSuccDegreePrec_of_allCombo hallTarget)

/-- The signed right-pencil target implies the exact lower-count endpoint
comparison. -/
theorem compatibleSuccDegreeEndpointSignLowerCountEq_of_signedRightFamily
    (hsigned : CompatibleSuccDegreeSignedRightFamilyStatement) :
    CompatibleSuccDegreeEndpointSignLowerCountEqStatement :=
  compatibleSuccDegreeEndpointSignLowerCountEq_of_allCombo
    (compatibleSuccDegreeAllCombo_of_signedRightFamily hsigned)

/-- The negative right-pencil target implies the exact lower-count endpoint
comparison. -/
theorem compatibleSuccDegreeEndpointSignLowerCountEq_of_negativeRightFamily
    (hneg : CompatibleSuccDegreeNegativeRightFamilyStatement) :
    CompatibleSuccDegreeEndpointSignLowerCountEqStatement :=
  compatibleSuccDegreeEndpointSignLowerCountEq_of_allCombo
    (compatibleSuccDegreeAllCombo_of_negativeRightFamily hneg)

/-- The nonnegative-coefficient negative right-pencil target implies the exact
lower-count endpoint comparison. -/
theorem compatibleSuccDegreeEndpointSignLowerCountEq_of_negativeRightFamily_nonnegShift
    (hneg : CompatibleSuccDegreeNegativeRightFamilyNonnegStatement) :
    CompatibleSuccDegreeEndpointSignLowerCountEqStatement :=
  compatibleSuccDegreeEndpointSignLowerCountEq_of_negativeRightFamily
    (compatibleSuccDegreeNegativeRightFamily_of_nonnegShift hneg)

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

/-- Degree-zero base case for the succ-degree root-count formulation.

If `f` has degree zero and `g` has degree one, then the lower-threshold count
for `f` is always zero and the lower-threshold count for `g` is at most one. -/
theorem succDegreeRootCount_of_natDegree_eq_zero
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hdeg : g.natDegree = f.natDegree + 1) (hfdeg : f.natDegree = 0) (x : ℝ) :
      ((f.roots.filter (· ≤ x)).card : ℤ) - (g.roots.filter (· ≤ x)).card ≤ 0 ∧
      ((g.roots.filter (· ≤ x)).card : ℤ) - (f.roots.filter (· ≤ x)).card ≤ 2 := by
  have hfcard_nat : (f.roots.filter (· ≤ x)).card = 0 := by
    have hle : (f.roots.filter (· ≤ x)).card ≤ 0 := by
      calc
        (f.roots.filter (· ≤ x)).card ≤ f.roots.card :=
          Multiset.card_le_card (Multiset.filter_le _ _)
        _ = f.natDegree := card_roots_of_splits hf
        _ = 0 := hfdeg
    exact Nat.eq_zero_of_le_zero hle
  have hgcard_nat : (g.roots.filter (· ≤ x)).card ≤ 1 := by
    calc
      (g.roots.filter (· ≤ x)).card ≤ g.roots.card :=
        Multiset.card_le_card (Multiset.filter_le _ _)
      _ = g.natDegree := card_roots_of_splits hg
      _ = f.natDegree + 1 := hdeg
      _ = 1 := by rw [hfdeg]
  have hfcard : ((f.roots.filter (· ≤ x)).card : ℤ) = 0 := by
    exact_mod_cast hfcard_nat
  have hgcard : ((g.roots.filter (· ≤ x)).card : ℤ) ≤ 1 := by
    exact_mod_cast hgcard_nat
  have hgnonneg : (0 : ℤ) ≤ (g.roots.filter (· ≤ x)).card := by
    exact_mod_cast Nat.zero_le (g.roots.filter (· ≤ x)).card
  constructor <;> lia

/-- Degree-zero base case for the succ-degree analytic root-count target in
the positive-combination/no-common setting. -/
theorem succDegreeRootCount_of_posCombo_natDegree_eq_zero
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (_hfnn : HasNonnegCoeffs f) (_hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g)
    (hdeg : g.natDegree = f.natDegree + 1)
    (_hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hf_split : f.Splits) (hfdeg : f.natDegree = 0) (x : ℝ) :
      ((f.roots.filter (· ≤ x)).card : ℤ) - (g.roots.filter (· ≤ x)).card ≤ 0 ∧
      ((g.roots.filter (· ≤ x)).card : ℤ) - (f.roots.filter (· ≤ x)).card ≤ 2 := by
  have hg_split : g.Splits :=
    (hfg.isRealRooted_right_of_succDegree hf_pos hg_pos hdeg).2
  exact succDegreeRootCount_of_natDegree_eq_zero hf_split hg_split hdeg hfdeg x

/-- Degree-zero base case for the upper-threshold succ-degree root-count
formulation. -/
theorem succDegreeRootCountAbove_of_natDegree_eq_zero
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hdeg : g.natDegree = f.natDegree + 1) (hfdeg : f.natDegree = 0) (x : ℝ) :
      ((f.roots.filter (x < ·)).card : ℤ) - (g.roots.filter (x < ·)).card ≤ 1 ∧
      ((g.roots.filter (x < ·)).card : ℤ) - (f.roots.filter (x < ·)).card ≤ 1 := by
  exact (succDegreeRootCountAbove_of_rootCount hf hg hdeg
    (fun y => succDegreeRootCount_of_natDegree_eq_zero hf hg hdeg hfdeg y)) x

/-- Degree-zero base case for the upper-threshold succ-degree analytic
root-count target in the positive-combination/no-common setting. -/
theorem succDegreeRootCountAbove_of_posCombo_natDegree_eq_zero
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (_hfnn : HasNonnegCoeffs f) (_hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g)
    (hdeg : g.natDegree = f.natDegree + 1)
    (_hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hf_split : f.Splits) (hfdeg : f.natDegree = 0) (x : ℝ) :
      ((f.roots.filter (x < ·)).card : ℤ) - (g.roots.filter (x < ·)).card ≤ 1 ∧
      ((g.roots.filter (x < ·)).card : ℤ) - (f.roots.filter (x < ·)).card ≤ 1 := by
  have hg_split : g.Splits :=
    (hfg.isRealRooted_right_of_succDegree hf_pos hg_pos hdeg).2
  exact succDegreeRootCountAbove_of_natDegree_eq_zero hf_split hg_split hdeg hfdeg x

/-- A positive-leading, splitting, degree-one polynomial factors as
`C a * (X - C α)` with `0 < a`, and its single root is `α`. -/
private lemma exists_linear_factor_of_natDegree_one
    {f : ℝ[X]} (hf_pos : HasPosLeadingCoeff f) (hf_split : f.Splits)
    (hfdeg : f.natDegree = 1) :
    ∃ a α : ℝ, 0 < a ∧ f.roots = {α} ∧ f = C a * (X - C α) := by
  obtain ⟨α, hα⟩ : ∃ α, f.roots = {α} :=
    Multiset.card_eq_one.mp (by rw [card_roots_of_splits hf_split, hfdeg])
  refine ⟨f.leadingCoeff, α, hf_pos, hα, ?_⟩
  have hprod := hf_split.eq_prod_roots
  rw [hα] at hprod
  simpa using hprod

/-- A positive-leading, splitting, degree-two polynomial factors as
`C b * ((X - C β) * (X - C γ))` with `0 < b` and `γ ≤ β`. -/
private lemma exists_quadratic_factor_of_natDegree_two
    {g : ℝ[X]} (hg_pos : HasPosLeadingCoeff g) (hg_split : g.Splits)
    (hgdeg : g.natDegree = 2) :
    ∃ b β γ : ℝ, 0 < b ∧ γ ≤ β ∧ g.roots = {β, γ} ∧
      g = C b * ((X - C β) * (X - C γ)) := by
  obtain ⟨r, s, hrs⟩ : ∃ r s, g.roots = {r, s} :=
    Multiset.card_eq_two.mp (by rw [card_roots_of_splits hg_split, hgdeg])
  have hprod := hg_split.eq_prod_roots
  rcases le_total s r with hle | hle
  · refine ⟨g.leadingCoeff, r, s, hg_pos, hle, hrs, ?_⟩
    rw [hrs] at hprod
    simpa [Multiset.insert_eq_cons, mul_comm] using hprod
  · refine ⟨g.leadingCoeff, s, r, hg_pos, hle, ?_, ?_⟩
    · rw [hrs]
      exact Multiset.pair_comm r s
    · rw [hrs] at hprod
      simpa [Multiset.insert_eq_cons, mul_comm] using hprod

/-- Normal-form core of the degree-one succ-degree base case: for a degree-one
`f` and degree-two `g` in a positive-combination family, the smaller root `γ`
of `g` lies to the left of the root `α` of `f`. -/
theorem smallRoot_le_of_posCombo_natDegree_eq_one
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfg : PosComboRealRooted f g)
    (hdeg : g.natDegree = f.natDegree + 1)
    (hf_split : f.Splits) (hfdeg : f.natDegree = 1) :
    ∃ a α : ℝ, 0 < a ∧ f.roots = {α} ∧
      ∃ b β γ : ℝ, 0 < b ∧ γ ≤ β ∧ g.roots = {β, γ} ∧ γ ≤ α := by
  have hgdeg : g.natDegree = 2 := by rw [hdeg, hfdeg]
  have hg_split : g.Splits :=
    (hfg.isRealRooted_right_of_succDegree hf_pos hg_pos hdeg).2
  obtain ⟨a, α, ha, hαroots, hfeq⟩ :=
    exists_linear_factor_of_natDegree_one hf_pos hf_split hfdeg
  obtain ⟨b, β, γ, hb, hβγ, hgroots, hgeq⟩ :=
    exists_quadratic_factor_of_natDegree_two hg_pos hg_split hgdeg
  refine ⟨a, α, ha, hαroots, b, β, γ, hb, hβγ, hgroots, ?_⟩
  apply root_le_of_posCombo_deg1 hβγ
  intro lam mu hlam hmu
  have hL : C (lam / a) * f = C lam * (X - C α) := by
    rw [hfeq, ← mul_assoc, ← C_mul, div_mul_cancel₀ _ ha.ne']
  have hR : C (mu / b) * g = C mu * ((X - C β) * (X - C γ)) := by
    rw [hgeq, ← mul_assoc, ← C_mul, div_mul_cancel₀ _ hb.ne']
  have hcombo :
      C lam * (X - C α) + C mu * ((X - C β) * (X - C γ)) =
        C (lam / a) * f + C (mu / b) * g := by
    rw [hL, hR]
  rw [hcombo]
  exact (hfg (div_pos hlam ha) (div_pos hmu hb)).2

/-- Counting core (upper threshold): for a singleton `{α}` and an ordered pair
`{β, γ}` with `γ ≤ α`, the numbers of elements strictly above any `x` differ
by at most one in each direction. -/
private lemma count_above_singleton_pair_le
    {α β γ x : ℝ} (hγα : γ ≤ α) :
    ((({α} : Multiset ℝ).filter (x < ·)).card : ℤ) -
        (({β, γ} : Multiset ℝ).filter (x < ·)).card ≤ 1 ∧
    ((({β, γ} : Multiset ℝ).filter (x < ·)).card : ℤ) -
        (({α} : Multiset ℝ).filter (x < ·)).card ≤ 1 := by
  simp only [Multiset.insert_eq_cons, Multiset.filter_cons, Multiset.filter_singleton]
  split_ifs <;> (first | linarith | simp_all)

/-- Counting core (lower threshold): for a singleton `{α}` and an ordered pair
`{β, γ}` with `γ ≤ α`, the singleton never has more elements `≤ x` than the
pair, and the pair has at most two more. -/
private lemma count_below_singleton_pair_le
    {α β γ x : ℝ} (hγα : γ ≤ α) :
    ((({α} : Multiset ℝ).filter (· ≤ x)).card : ℤ) -
        (({β, γ} : Multiset ℝ).filter (· ≤ x)).card ≤ 0 ∧
    ((({β, γ} : Multiset ℝ).filter (· ≤ x)).card : ℤ) -
        (({α} : Multiset ℝ).filter (· ≤ x)).card ≤ 2 := by
  simp only [Multiset.insert_eq_cons, Multiset.filter_cons, Multiset.filter_singleton]
  split_ifs <;> (first | linarith | simp_all)

/-- Degree-one base case for the upper-threshold succ-degree root-count
formulation in the positive-combination / no-common-root setting.

With `f` of degree one and `g` of degree two, the smaller root of `g` lies to
the left of the root of `f`, so the numbers of roots above any threshold `x`
differ by at most one in each direction. -/
theorem succDegreeRootCountAbove_of_posCombo_natDegree_eq_one
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (_hfnn : HasNonnegCoeffs f) (_hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g)
    (hdeg : g.natDegree = f.natDegree + 1)
    (_hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hf_split : f.Splits) (hfdeg : f.natDegree = 1) (x : ℝ) :
      ((f.roots.filter (x < ·)).card : ℤ) - (g.roots.filter (x < ·)).card ≤ 1 ∧
      ((g.roots.filter (x < ·)).card : ℤ) - (f.roots.filter (x < ·)).card ≤ 1 := by
  obtain ⟨_a, α, _ha, hαroots, _b, β, γ, _hb, _hβγ, hgroots, hγα⟩ :=
    smallRoot_le_of_posCombo_natDegree_eq_one hf_pos hg_pos hfg hdeg hf_split hfdeg
  rw [hαroots, hgroots]
  exact count_above_singleton_pair_le hγα

/-- Degree-one base case for the lower-threshold succ-degree root-count
formulation in the positive-combination / no-common-root setting. -/
theorem succDegreeRootCount_of_posCombo_natDegree_eq_one
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (_hfnn : HasNonnegCoeffs f) (_hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g)
    (hdeg : g.natDegree = f.natDegree + 1)
    (_hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hf_split : f.Splits) (hfdeg : f.natDegree = 1) (x : ℝ) :
      ((f.roots.filter (· ≤ x)).card : ℤ) - (g.roots.filter (· ≤ x)).card ≤ 0 ∧
      ((g.roots.filter (· ≤ x)).card : ℤ) - (f.roots.filter (· ≤ x)).card ≤ 2 := by
  obtain ⟨_a, α, _ha, hαroots, _b, β, γ, _hb, _hβγ, hgroots, hγα⟩ :=
    smallRoot_le_of_posCombo_natDegree_eq_one hf_pos hg_pos hfg hdeg hf_split hfdeg
  rw [hαroots, hgroots]
  exact count_below_singleton_pair_le hγα

/-- Degree-one base case for the succ-degree root-crossing target in the
positive-combination / no-common-root setting, obtained from the
upper-threshold root count via `succDegreeRootCrossing_of_rootCountAbove`. -/
theorem succDegreeRootCrossing_of_posCombo_natDegree_eq_one
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f) (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g)
    (hdeg : g.natDegree = f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hf_split : f.Splits) (hfdeg : f.natDegree = 1) :
    (∀ j, 1 ≤ j → j ≤ f.natDegree →
        (rootSeqDesc g).getD j 0 ≤ (rootSeqDesc f).getD (j - 1) 0) ∧
    (∀ j, 1 ≤ j → j < f.natDegree →
        (rootSeqDesc f).getD j 0 ≤ (rootSeqDesc g).getD (j - 1) 0) := by
  have hg_split : g.Splits :=
    (hfg.isRealRooted_right_of_succDegree hf_pos hg_pos hdeg).2
  exact succDegreeRootCrossing_of_rootCountAbove hf_split hg_split hdeg
    (fun x =>
      succDegreeRootCountAbove_of_posCombo_natDegree_eq_one hf_pos hg_pos hfnn hgnn
        hfg hdeg hno hf_split hfdeg x)

/-- A natural number bounded by one is zero or one. -/
private lemma nat_eq_zero_or_eq_one_of_le_one {n : ℕ} (hn : n ≤ 1) :
    n = 0 ∨ n = 1 := by
  rcases n with _ | n
  · exact Or.inl rfl
  · have hn0 : n = 0 := by
      exact Nat.eq_zero_of_le_zero (Nat.succ_le_succ_iff.mp hn)
    exact Or.inr (by rw [hn0])

/-- Low-degree base case for the upper-threshold succ-degree root-count
formulation in the positive-combination / no-common-root setting. -/
theorem succDegreeRootCountAbove_of_posCombo_natDegree_le_one
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f) (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g)
    (hdeg : g.natDegree = f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hf_split : f.Splits) (hfdeg : f.natDegree ≤ 1) (x : ℝ) :
      ((f.roots.filter (x < ·)).card : ℤ) - (g.roots.filter (x < ·)).card ≤ 1 ∧
      ((g.roots.filter (x < ·)).card : ℤ) - (f.roots.filter (x < ·)).card ≤ 1 := by
  rcases nat_eq_zero_or_eq_one_of_le_one hfdeg with hf0 | hf1
  · exact succDegreeRootCountAbove_of_posCombo_natDegree_eq_zero
      hf_pos hg_pos hfnn hgnn hfg hdeg hno hf_split hf0 x
  · exact succDegreeRootCountAbove_of_posCombo_natDegree_eq_one
      hf_pos hg_pos hfnn hgnn hfg hdeg hno hf_split hf1 x

/-- Degree-zero compatible-pair base case for the upper-threshold succ-degree
root-count formulation. -/
theorem compatibleSuccDegreeRootCountAbove_of_natDegree_eq_zero
    {f g : ℝ[X]}
    (hcomp : Compatible f g)
    (_hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hdeg : g.natDegree = f.natDegree + 1)
    (hf_split : f.Splits) (hfdeg : f.natDegree = 0) (x : ℝ) :
      ((f.roots.filter (x < ·)).card : ℤ) - (g.roots.filter (x < ·)).card ≤ 1 ∧
      ((g.roots.filter (x < ·)).card : ℤ) - (f.roots.filter (x < ·)).card ≤ 1 := by
  exact succDegreeRootCountAbove_of_natDegree_eq_zero hf_split
    (hcomp.isRealRooted_right hg_pos).2 hdeg hfdeg x

/-- Degree-one compatible-pair base case for the upper-threshold succ-degree
root-count formulation. -/
theorem compatibleSuccDegreeRootCountAbove_of_natDegree_eq_one
    {f g : ℝ[X]}
    (hcomp : Compatible f g)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hdeg : g.natDegree = f.natDegree + 1)
    (hf_split : f.Splits) (hfdeg : f.natDegree = 1) (x : ℝ) :
      ((f.roots.filter (x < ·)).card : ℤ) - (g.roots.filter (x < ·)).card ≤ 1 ∧
      ((g.roots.filter (x < ·)).card : ℤ) - (f.roots.filter (x < ·)).card ≤ 1 := by
  obtain ⟨_a, α, _ha, hαroots, _b, β, γ, _hb, _hβγ, hgroots, hγα⟩ :=
    smallRoot_le_of_posCombo_natDegree_eq_one hf_pos hg_pos
      (hcomp.toPosComboRealRooted hf_pos hg_pos) hdeg hf_split hfdeg
  rw [hαroots, hgroots]
  exact count_above_singleton_pair_le hγα

/-- Low-degree compatible-pair base case for the upper-threshold succ-degree
root-count formulation. -/
theorem compatibleSuccDegreeRootCountAbove_of_natDegree_le_one
    {f g : ℝ[X]}
    (hcomp : Compatible f g)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hdeg : g.natDegree = f.natDegree + 1)
    (hf_split : f.Splits) (hfdeg : f.natDegree ≤ 1) (x : ℝ) :
      ((f.roots.filter (x < ·)).card : ℤ) - (g.roots.filter (x < ·)).card ≤ 1 ∧
      ((g.roots.filter (x < ·)).card : ℤ) - (f.roots.filter (x < ·)).card ≤ 1 := by
  rcases nat_eq_zero_or_eq_one_of_le_one hfdeg with hf0 | hf1
  · exact compatibleSuccDegreeRootCountAbove_of_natDegree_eq_zero
      hcomp hf_pos hg_pos hdeg hf_split hf0 x
  · exact compatibleSuccDegreeRootCountAbove_of_natDegree_eq_one
      hcomp hf_pos hg_pos hdeg hf_split hf1 x

/-- Degree-`≤ 2` compatible-pair base case for the upper-threshold
succ-degree root-count gap-at-most-two formulation. -/
theorem compatibleSuccDegreeRootCountAbove_le_two_of_natDegree_le_two
    {f g : ℝ[X]}
    (hcomp : Compatible f g)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hdeg : g.natDegree = f.natDegree + 1)
    (hf_split : f.Splits) (hfdeg : f.natDegree ≤ 2) (x : ℝ) :
      ((f.roots.filter (x < ·)).card : ℤ) -
          (g.roots.filter (x < ·)).card ≤ 2 ∧
      ((g.roots.filter (x < ·)).card : ℤ) -
          (f.roots.filter (x < ·)).card ≤ 2 := by
  by_cases hfdeg_two : 2 ≤ f.natDegree
  · have hder_bound :
        ∀ y : ℝ,
          ¬ f.derivative.IsRoot y → ¬ g.derivative.IsRoot y →
            ((f.derivative.roots.filter (y < ·)).card : ℤ) -
                (g.derivative.roots.filter (y < ·)).card ≤ 1 ∧
            ((g.derivative.roots.filter (y < ·)).card : ℤ) -
                (f.derivative.roots.filter (y < ·)).card ≤ 1 := by
      intro y _hyf _hyg
      have hf'_pos : HasPosLeadingCoeff f.derivative :=
        hf_pos.derivative (by lia)
      have hg'_pos : HasPosLeadingCoeff g.derivative :=
        hg_pos.derivative (by rw [hdeg]; lia)
      have hdeg' : g.derivative.natDegree = f.derivative.natDegree + 1 :=
        succDegree_derivative_natDegree_eq hdeg (by lia)
      have hf'_split : f.derivative.Splits :=
        (derivative_interlaces hf_split hfdeg_two).2.1.2
      have hf'_deg : f.derivative.natDegree ≤ 1 := by
        rw [f.natDegree_derivative]
        lia
      exact
        compatibleSuccDegreeRootCountAbove_of_natDegree_le_one
          hcomp.derivative hf'_pos hg'_pos hdeg' hf'_split hf'_deg y
    exact
      compatibleSuccDegreeRootCountAbove_le_two_of_derivative_bound
        hcomp hf_pos hg_pos hdeg hf_split hfdeg_two hder_bound x
  · have hfdeg_le_one : f.natDegree ≤ 1 :=
      Nat.lt_succ_iff.mp (Nat.lt_of_not_ge hfdeg_two)
    obtain ⟨hfg_le, hgf_le⟩ :=
      compatibleSuccDegreeRootCountAbove_of_natDegree_le_one
        hcomp hf_pos hg_pos hdeg hf_split hfdeg_le_one x
    constructor <;> linarith

/-- Low-degree base case for the compatible exact gap-two obstruction.  When
the lower endpoint has degree at most one, the explicit upper root-count bound
already rules out an endpoint count difference equal to two. -/
theorem compatibleSuccDegreeRootCountAboveNoGapTwo_of_natDegree_le_one
    {f g : ℝ[X]}
    (hcomp : Compatible f g)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hdeg : g.natDegree = f.natDegree + 1)
    (hf_split : f.Splits) (hfdeg : f.natDegree ≤ 1) (x : ℝ) :
      ((f.roots.filter (x < ·)).card : ℤ) -
          (g.roots.filter (x < ·)).card ≠ 2 ∧
      ((g.roots.filter (x < ·)).card : ℤ) -
          (f.roots.filter (x < ·)).card ≠ 2 := by
  obtain ⟨hfg_le, hgf_le⟩ :=
    compatibleSuccDegreeRootCountAbove_of_natDegree_le_one
      hcomp hf_pos hg_pos hdeg hf_split hfdeg x
  constructor <;> intro hgap <;> linarith

/-- Finite count core for the degree-two succ-degree root-order leaf. -/
private lemma count_below_pair_triple_of_succ_bounds
    {a b p q r x : ℝ}
    (hab : a ≤ b) (hpq : p ≤ q) (hqr : q ≤ r)
    (hpa : p ≤ a) (hqb : q ≤ b) (har : a ≤ r) :
    ((({a, b} : Multiset ℝ).filter (· ≤ x)).card : ℤ) -
        (({p, q, r} : Multiset ℝ).filter (· ≤ x)).card ≤ 0 ∧
    ((({p, q, r} : Multiset ℝ).filter (· ≤ x)).card : ℤ) -
        (({a, b} : Multiset ℝ).filter (· ≤ x)).card ≤ 2 := by
  rw [card_filter_le_pair, card_filter_le_triple]
  push_cast
  constructor <;> grind

/-- Degree-two base case for the lower-threshold succ-degree root-count
formulation, reduced to the quadratic/cubic root-order leaf. -/
theorem succDegreeRootCount_of_posCombo_natDegree_eq_two_of_rootBounds
    (hbound : SuccDegreeQuadraticCubicRootBoundsStatement)
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfg : PosComboRealRooted f g)
    (hdeg : g.natDegree = f.natDegree + 1)
    (hf_split : f.Splits) (hfdeg : f.natDegree = 2) (x : ℝ) :
      ((f.roots.filter (· ≤ x)).card : ℤ) - (g.roots.filter (· ≤ x)).card ≤ 0 ∧
      ((g.roots.filter (· ≤ x)).card : ℤ) - (f.roots.filter (· ≤ x)).card ≤ 2 := by
  have hgdeg : g.natDegree = 3 := by rw [hdeg, hfdeg]
  have hg_split : g.Splits :=
    (hfg.isRealRooted_right_of_succDegree hf_pos hg_pos hdeg).2
  obtain ⟨a, b, hab, hfroots, _hffac⟩ :=
    exists_roots_pair_of_splits_natDegree_two hf_split hfdeg
  obtain ⟨p, q, r, hpq, hqr, hgroots, _hgfac⟩ :=
    exists_roots_triple_of_splits_natDegree_three hg_split hgdeg
  obtain ⟨hpa, hqb, har⟩ :=
    hbound hf_pos hg_pos hf_split hg_split hfdeg hgdeg hfg
      a b p q r hab hpq hqr hfroots hgroots
  rw [hfroots, hgroots]
  exact count_below_pair_triple_of_succ_bounds hab hpq hqr hpa hqb har

/-- Degree-two base case for the upper-threshold succ-degree root-count
formulation, reduced to the quadratic/cubic root-order leaf. -/
theorem succDegreeRootCountAbove_of_posCombo_natDegree_eq_two_of_rootBounds
    (hbound : SuccDegreeQuadraticCubicRootBoundsStatement)
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfg : PosComboRealRooted f g)
    (hdeg : g.natDegree = f.natDegree + 1)
    (hf_split : f.Splits) (hfdeg : f.natDegree = 2) (x : ℝ) :
      ((f.roots.filter (x < ·)).card : ℤ) - (g.roots.filter (x < ·)).card ≤ 1 ∧
      ((g.roots.filter (x < ·)).card : ℤ) - (f.roots.filter (x < ·)).card ≤ 1 := by
  have hg_split : g.Splits :=
    (hfg.isRealRooted_right_of_succDegree hf_pos hg_pos hdeg).2
  exact succDegreeRootCountAbove_of_rootCount hf_split hg_split hdeg
    (fun y =>
      succDegreeRootCount_of_posCombo_natDegree_eq_two_of_rootBounds
        hbound hf_pos hg_pos hfg hdeg hf_split hfdeg y)
    x

/-- Compatible-pair degree-two no-gap base, reduced to the quadratic/cubic
root-order leaf. -/
theorem compatibleSuccDegreeRootCountAboveNoGapTwo_of_natDegree_eq_two_of_rootBounds
    (hbound : SuccDegreeQuadraticCubicRootBoundsStatement)
    {f g : ℝ[X]}
    (hcomp : Compatible f g)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hdeg : g.natDegree = f.natDegree + 1)
    (hf_split : f.Splits) (hfdeg : f.natDegree = 2) (x : ℝ) :
      ((f.roots.filter (x < ·)).card : ℤ) -
          (g.roots.filter (x < ·)).card ≠ 2 ∧
      ((g.roots.filter (x < ·)).card : ℤ) -
          (f.roots.filter (x < ·)).card ≠ 2 := by
  obtain ⟨hfg_le, hgf_le⟩ :=
    succDegreeRootCountAbove_of_posCombo_natDegree_eq_two_of_rootBounds
      hbound hf_pos hg_pos (hcomp.toPosComboRealRooted hf_pos hg_pos)
      hdeg hf_split hfdeg x
  constructor <;> intro hgap <;> linarith

/-- Compatible-pair no-gap base through lower endpoint degree two, reduced to
the quadratic/cubic root-order leaf. -/
theorem compatibleSuccDegreeRootCountAboveNoGapTwo_of_natDegree_le_two_of_rootBounds
    (hbound : SuccDegreeQuadraticCubicRootBoundsStatement)
    {f g : ℝ[X]}
    (hcomp : Compatible f g)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hdeg : g.natDegree = f.natDegree + 1)
    (hf_split : f.Splits) (hfdeg : f.natDegree ≤ 2) (x : ℝ) :
      ((f.roots.filter (x < ·)).card : ℤ) -
          (g.roots.filter (x < ·)).card ≠ 2 ∧
      ((g.roots.filter (x < ·)).card : ℤ) -
          (f.roots.filter (x < ·)).card ≠ 2 := by
  by_cases hle : f.natDegree ≤ 1
  · exact compatibleSuccDegreeRootCountAboveNoGapTwo_of_natDegree_le_one
      hcomp hf_pos hg_pos hdeg hf_split hle x
  · have htwo : f.natDegree = 2 := by lia
    exact compatibleSuccDegreeRootCountAboveNoGapTwo_of_natDegree_eq_two_of_rootBounds
      hbound hcomp hf_pos hg_pos hdeg hf_split htwo x

/-- The three quadratic/cubic obstruction leaves close the compatible
succ-degree exact no-gap base through lower endpoint degree two. -/
theorem compatibleSuccDegreeRootCountAboveNoGapTwo_of_natDegree_le_two_of_obstructions
    (hfirst : SuccDegreeQuadraticCubicFirstAboveObstructionStatement)
    (hsecond : SuccDegreeQuadraticCubicSecondAboveObstructionStatement)
    (hbelow : SuccDegreeQuadraticCubicFullBelowObstructionStatement)
    {f g : ℝ[X]}
    (hcomp : Compatible f g)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hdeg : g.natDegree = f.natDegree + 1)
    (hf_split : f.Splits) (hfdeg : f.natDegree ≤ 2) (x : ℝ) :
      ((f.roots.filter (x < ·)).card : ℤ) -
          (g.roots.filter (x < ·)).card ≠ 2 ∧
      ((g.roots.filter (x < ·)).card : ℤ) -
          (f.roots.filter (x < ·)).card ≠ 2 :=
  compatibleSuccDegreeRootCountAboveNoGapTwo_of_natDegree_le_two_of_rootBounds
    (succDegreeQuadraticCubicRootBounds_of_obstructions hfirst hsecond hbelow)
    hcomp hf_pos hg_pos hdeg hf_split hfdeg x

/-- Pure monic-pencil obstruction leaves close the compatible succ-degree
exact no-gap base through lower endpoint degree two. -/
theorem compatibleSuccDegreeRootCountAboveNoGapTwo_of_natDegree_le_two_of_pencil_obstructions
    (hfirst : QuadraticCubicFirstAbovePencilObstructionStatement)
    (hsecond : QuadraticCubicSecondAbovePencilObstructionStatement)
    (hbelow : QuadraticCubicFullBelowPencilObstructionStatement)
    {f g : ℝ[X]}
    (hcomp : Compatible f g)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hdeg : g.natDegree = f.natDegree + 1)
    (hf_split : f.Splits) (hfdeg : f.natDegree ≤ 2) (x : ℝ) :
      ((f.roots.filter (x < ·)).card : ℤ) -
          (g.roots.filter (x < ·)).card ≠ 2 ∧
      ((g.roots.filter (x < ·)).card : ℤ) -
          (f.roots.filter (x < ·)).card ≠ 2 :=
  compatibleSuccDegreeRootCountAboveNoGapTwo_of_natDegree_le_two_of_rootBounds
    (succDegreeQuadraticCubicRootBounds_of_pencil_obstructions
      hfirst hsecond hbelow)
    hcomp hf_pos hg_pos hdeg hf_split hfdeg x

/-- An even integer between `-1` and `1` is zero. -/
private lemma int_eq_zero_of_even_of_le_one_of_neg_le_one {z : ℤ}
    (hz_even : Even z) (hz_le : z ≤ 1) (hneg_le : -z ≤ 1) :
    z = 0 := by
  rcases hz_even with ⟨k, hk⟩
  have hk_le : k ≤ 0 := by
    linarith
  have hk_nonneg : 0 ≤ k := by
    linarith
  have hk_zero : k = 0 := le_antisymm hk_le hk_nonneg
  rw [hk, hk_zero]
  norm_num

/-- A local count-bounds package for the closed-segment count-stability
target.  If the two endpoint upper-count differences are already bounded by
one and the threshold is never crossed on the closed segment, then the endpoint
upper counts are equal. -/
theorem compatibleSuccDegreeClosedSegmentCountEq_of_rootCountAbove_bounds
    {f g : ℝ[X]}
    (hcomp : Compatible f g)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hdeg : g.natDegree = f.natDegree + 1)
    (hf_split : f.Splits)
    {x : ℝ} (hxf : ¬ f.IsRoot x) (hxg : ¬ g.IsRoot x)
    (hseg : ∀ {β : ℝ}, 0 ≤ β → β ≤ 1 →
      ¬ (C (1 - β) * f + C β * g).IsRoot x)
    (hfg_le :
      ((f.roots.filter (x < ·)).card : ℤ) -
        (g.roots.filter (x < ·)).card ≤ 1)
    (hgf_le :
      ((g.roots.filter (x < ·)).card : ℤ) -
        (f.roots.filter (x < ·)).card ≤ 1) :
    (f.roots.filter (x < ·)).card = (g.roots.filter (x < ·)).card := by
  have hno : ∀ {μ : ℝ}, 0 ≤ μ → ¬ (f + C μ * g).IsRoot x := by
    intro μ hμ
    exact closedSegment_not_isRoot_add_right_of_nonneg hμ hseg
  have heven :
      Even (((f.roots.filter (x < ·)).card : ℤ) -
        (g.roots.filter (x < ·)).card) :=
    compatibleSuccDegree_even_roots_gt_count_sub_of_no_rightFamily_isRoot
      hcomp hf_pos hg_pos hdeg hf_split hxf hxg hno
  have hdiff_zero :
      ((f.roots.filter (x < ·)).card : ℤ) -
        (g.roots.filter (x < ·)).card = 0 :=
    int_eq_zero_of_even_of_le_one_of_neg_le_one heven hfg_le (by linarith)
  have hcard_int :
      ((f.roots.filter (x < ·)).card : ℤ) =
        (g.roots.filter (x < ·)).card := by
    linarith
  exact_mod_cast hcard_int

/-- Low-degree base case for closed-segment endpoint count equality.  When
`f.natDegree ≤ 1`, the explicit compatible-pair root-count bound gives
absolute difference at most one, while the no-crossing hypothesis forces the
upper-count difference to be even. -/
theorem compatibleSuccDegreeClosedSegmentCountEq_of_natDegree_le_one
    {f g : ℝ[X]}
    (hcomp : Compatible f g)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hdeg : g.natDegree = f.natDegree + 1)
    (hf_split : f.Splits) (hfdeg : f.natDegree ≤ 1)
    {x : ℝ} (hxf : ¬ f.IsRoot x) (hxg : ¬ g.IsRoot x)
    (hseg : ∀ {β : ℝ}, 0 ≤ β → β ≤ 1 →
      ¬ (C (1 - β) * f + C β * g).IsRoot x) :
    (f.roots.filter (x < ·)).card = (g.roots.filter (x < ·)).card := by
  obtain ⟨hfg_le, hgf_le⟩ :=
    compatibleSuccDegreeRootCountAbove_of_natDegree_le_one
      hcomp hf_pos hg_pos hdeg hf_split hfdeg x
  exact
    compatibleSuccDegreeClosedSegmentCountEq_of_rootCountAbove_bounds
      hcomp hf_pos hg_pos hdeg hf_split hxf hxg hseg hfg_le hgf_le

/-- Low-degree base case for the exact lower-threshold endpoint-sign count
comparison.  When `f.natDegree ≤ 1`, positivity of the endpoint product at the
fixed threshold rules out any closed-segment crossing, so the unconditional
low-degree closed-segment count equality applies; complement-count arithmetic
then converts the equal upper counts into the exact lower-count difference
`= 1`. -/
theorem compatibleSuccDegreeEndpointSignLowerCountEq_of_natDegree_le_one
    {f g : ℝ[X]}
    (hcomp : Compatible f g)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hdeg : g.natDegree = f.natDegree + 1)
    (hf_split : f.Splits) (hfdeg : f.natDegree ≤ 1)
    {x : ℝ} (hxf : ¬ f.IsRoot x) (hxg : ¬ g.IsRoot x)
    (hprod : 0 < f.eval x * g.eval x) :
    ((g.roots.filter (· ≤ x)).card : ℤ) - (f.roots.filter (· ≤ x)).card = 1 := by
  have hseg : ∀ {β : ℝ}, 0 ≤ β → β ≤ 1 →
      ¬ (C (1 - β) * f + C β * g).IsRoot x := by
    intro β hβ0 hβ1
    exact closedSegment_not_isRoot_of_eval_mul_pos hβ0 hβ1 hprod
  have hgt :=
    compatibleSuccDegreeClosedSegmentCountEq_of_natDegree_le_one
      hcomp hf_pos hg_pos hdeg hf_split hfdeg hxf hxg hseg
  have hg_split : g.Splits := (hcomp.isRealRooted_right hg_pos).2
  have hfpart := card_roots_filter_gt_add_le_of_splits hf_split x
  have hgpart := card_roots_filter_gt_add_le_of_splits hg_split x
  have hgtZ :
      ((f.roots.filter (x < ·)).card : ℤ) =
        (g.roots.filter (x < ·)).card := by
    exact_mod_cast hgt
  have hfpartZ :
      ((f.roots.filter (x < ·)).card : ℤ) +
          (f.roots.filter (· ≤ x)).card =
        f.natDegree := by
    exact_mod_cast hfpart
  have hgpartZ :
      ((g.roots.filter (x < ·)).card : ℤ) +
          (g.roots.filter (· ≤ x)).card =
        g.natDegree := by
    exact_mod_cast hgpart
  have hdegZ : (g.natDegree : ℤ) = (f.natDegree : ℤ) + 1 := by
    exact_mod_cast hdeg
  linarith

/-- Low-degree base case for closed-segment endpoint count equality through
degree two, reduced to the quadratic/cubic root-order leaf. -/
theorem compatibleSuccDegreeClosedSegmentCountEq_of_natDegree_le_two_of_rootBounds
    (hbound : SuccDegreeQuadraticCubicRootBoundsStatement)
    {f g : ℝ[X]}
    (hcomp : Compatible f g)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hdeg : g.natDegree = f.natDegree + 1)
    (hf_split : f.Splits) (hfdeg : f.natDegree ≤ 2)
    {x : ℝ} (hxf : ¬ f.IsRoot x) (hxg : ¬ g.IsRoot x)
    (hseg : ∀ {β : ℝ}, 0 ≤ β → β ≤ 1 →
      ¬ (C (1 - β) * f + C β * g).IsRoot x) :
    (f.roots.filter (x < ·)).card = (g.roots.filter (x < ·)).card := by
  by_cases hle : f.natDegree ≤ 1
  · exact compatibleSuccDegreeClosedSegmentCountEq_of_natDegree_le_one
      hcomp hf_pos hg_pos hdeg hf_split hle hxf hxg hseg
  · have hfdeg_eq : f.natDegree = 2 := by lia
    obtain ⟨hfg_le, hgf_le⟩ :=
      succDegreeRootCountAbove_of_posCombo_natDegree_eq_two_of_rootBounds
        hbound hf_pos hg_pos (hcomp.toPosComboRealRooted hf_pos hg_pos)
        hdeg hf_split hfdeg_eq x
    exact compatibleSuccDegreeClosedSegmentCountEq_of_rootCountAbove_bounds
      hcomp hf_pos hg_pos hdeg hf_split hxf hxg hseg hfg_le hgf_le

/-- The three quadratic/cubic obstruction leaves close the closed-segment
count-equality base through lower endpoint degree two. -/
theorem compatibleSuccDegreeClosedSegmentCountEq_of_natDegree_le_two_of_obstructions
    (hfirst : SuccDegreeQuadraticCubicFirstAboveObstructionStatement)
    (hsecond : SuccDegreeQuadraticCubicSecondAboveObstructionStatement)
    (hbelow : SuccDegreeQuadraticCubicFullBelowObstructionStatement)
    {f g : ℝ[X]}
    (hcomp : Compatible f g)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hdeg : g.natDegree = f.natDegree + 1)
    (hf_split : f.Splits) (hfdeg : f.natDegree ≤ 2)
    {x : ℝ} (hxf : ¬ f.IsRoot x) (hxg : ¬ g.IsRoot x)
    (hseg : ∀ {β : ℝ}, 0 ≤ β → β ≤ 1 →
      ¬ (C (1 - β) * f + C β * g).IsRoot x) :
    (f.roots.filter (x < ·)).card = (g.roots.filter (x < ·)).card :=
  compatibleSuccDegreeClosedSegmentCountEq_of_natDegree_le_two_of_rootBounds
    (succDegreeQuadraticCubicRootBounds_of_obstructions hfirst hsecond hbelow)
    hcomp hf_pos hg_pos hdeg hf_split hfdeg hxf hxg hseg

/-- Pure monic-pencil obstruction leaves close the closed-segment
count-equality base through lower endpoint degree two. -/
theorem compatibleSuccDegreeClosedSegmentCountEq_of_natDegree_le_two_of_pencil_obstructions
    (hfirst : QuadraticCubicFirstAbovePencilObstructionStatement)
    (hsecond : QuadraticCubicSecondAbovePencilObstructionStatement)
    (hbelow : QuadraticCubicFullBelowPencilObstructionStatement)
    {f g : ℝ[X]}
    (hcomp : Compatible f g)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hdeg : g.natDegree = f.natDegree + 1)
    (hf_split : f.Splits) (hfdeg : f.natDegree ≤ 2)
    {x : ℝ} (hxf : ¬ f.IsRoot x) (hxg : ¬ g.IsRoot x)
    (hseg : ∀ {β : ℝ}, 0 ≤ β → β ≤ 1 →
      ¬ (C (1 - β) * f + C β * g).IsRoot x) :
    (f.roots.filter (x < ·)).card = (g.roots.filter (x < ·)).card :=
  compatibleSuccDegreeClosedSegmentCountEq_of_natDegree_le_two_of_rootBounds
    (succDegreeQuadraticCubicRootBounds_of_pencil_obstructions
      hfirst hsecond hbelow)
    hcomp hf_pos hg_pos hdeg hf_split hfdeg hxf hxg hseg

/-- The exact no-gap-two upper-count leaf closes the low-degree closed-segment
endpoint count-equality base. -/
theorem compatibleSuccDegreeClosedSegmentCountEq_of_natDegree_le_two_of_noGapTwo
    (hgap : CompatibleSuccDegreeRootCountAboveNoGapTwoStatement)
    {f g : ℝ[X]}
    (hcomp : Compatible f g)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hdeg : g.natDegree = f.natDegree + 1)
    (hf_split : f.Splits) (hfdeg : f.natDegree ≤ 2)
    {x : ℝ} (hxf : ¬ f.IsRoot x) (hxg : ¬ g.IsRoot x)
    (hseg : ∀ {β : ℝ}, 0 ≤ β → β ≤ 1 →
      ¬ (C (1 - β) * f + C β * g).IsRoot x) :
    (f.roots.filter (x < ·)).card = (g.roots.filter (x < ·)).card := by
  obtain ⟨hfg_le2, hgf_le2⟩ :=
    compatibleSuccDegreeRootCountAbove_le_two_of_natDegree_le_two
      hcomp hf_pos hg_pos hdeg hf_split hfdeg x
  obtain ⟨hfg_ne2, hgf_ne2⟩ :=
    hgap hcomp hf_pos hg_pos hdeg hf_split x hxf hxg
  exact
    compatibleSuccDegreeClosedSegmentCountEq_of_rootCountAbove_bounds
      hcomp hf_pos hg_pos hdeg hf_split hxf hxg hseg
      (int_le_one_of_le_two_ne_two hfg_le2 hfg_ne2)
      (int_le_one_of_le_two_ne_two hgf_le2 hgf_ne2)

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

/-- Low-degree base case for the lower-threshold succ-degree root-count
formulation in the positive-combination / no-common-root setting. -/
theorem succDegreeRootCount_of_posCombo_natDegree_le_one
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f) (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g)
    (hdeg : g.natDegree = f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hf_split : f.Splits) (hfdeg : f.natDegree ≤ 1) (x : ℝ) :
      ((f.roots.filter (· ≤ x)).card : ℤ) - (g.roots.filter (· ≤ x)).card ≤ 0 ∧
      ((g.roots.filter (· ≤ x)).card : ℤ) - (f.roots.filter (· ≤ x)).card ≤ 2 := by
  rcases nat_eq_zero_or_eq_one_of_le_one hfdeg with hf0 | hf1
  · exact succDegreeRootCount_of_posCombo_natDegree_eq_zero
      hf_pos hg_pos hfnn hgnn hfg hdeg hno hf_split hf0 x
  · exact succDegreeRootCount_of_posCombo_natDegree_eq_one
      hf_pos hg_pos hfnn hgnn hfg hdeg hno hf_split hf1 x

/-- Low-degree base case for the succ-degree root-crossing target in the
positive-combination / no-common-root setting. -/
theorem succDegreeRootCrossing_of_posCombo_natDegree_le_one
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f) (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g)
    (hdeg : g.natDegree = f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hf_split : f.Splits) (hfdeg : f.natDegree ≤ 1) :
    (∀ j, 1 ≤ j → j ≤ f.natDegree →
        (rootSeqDesc g).getD j 0 ≤ (rootSeqDesc f).getD (j - 1) 0) ∧
    (∀ j, 1 ≤ j → j < f.natDegree →
        (rootSeqDesc f).getD j 0 ≤ (rootSeqDesc g).getD (j - 1) 0) := by
  rcases nat_eq_zero_or_eq_one_of_le_one hfdeg with hf0 | hf1
  · have hg_split : g.Splits :=
      (hfg.isRealRooted_right_of_succDegree hf_pos hg_pos hdeg).2
    exact succDegreeRootCrossing_of_rootCountAbove hf_split hg_split hdeg
      (fun x =>
        succDegreeRootCountAbove_of_posCombo_natDegree_eq_zero
          hf_pos hg_pos hfnn hgnn hfg hdeg hno hf_split hf0 x)
  · exact succDegreeRootCrossing_of_posCombo_natDegree_eq_one
      hf_pos hg_pos hfnn hgnn hfg hdeg hno hf_split hf1

/-- Low-degree base case for the succ-degree root-slot data in the
positive-combination / no-common-root setting.  Root continuity supplies the
left endpoint, and the low-degree root-crossing wrapper supplies the slot
intersections. -/
theorem succDegreeSlotData_of_posCombo_natDegree_le_one
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f) (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g)
    (hdeg : g.natDegree = f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hfdeg : f.natDegree ≤ 1) :
    (f ≠ 0 ∧ f.Splits) ∧
      ∀ j, j < f.natDegree + 1 →
        ∀ (hjf : j < (rootSeqDesc f).length + 1)
          (hjg : j < (rootSeqDesc g).length + 1),
          (rootSlotInterval (rootSeqDesc f) ⟨j, hjf⟩ ∩
            rootSlotInterval (rootSeqDesc g) ⟨j, hjg⟩).Nonempty := by
  have hf_split : f.Splits :=
    PosComboSuccDegreeLeftSplitsNonnegStatement_of_rootContinuity
      hf_pos hg_pos hfnn hgnn hfg hdeg
  have hg_split : g.Splits :=
    (hfg.isRealRooted_right_of_succDegree hf_pos hg_pos hdeg).2
  refine ⟨⟨hf_pos.ne_zero, hf_split⟩, ?_⟩
  obtain ⟨hc1, hc2⟩ :=
    succDegreeRootCrossing_of_posCombo_natDegree_le_one
      hf_pos hg_pos hfnn hgnn hfg hdeg hno hf_split hfdeg
  have hlenf : (rootSeqDesc f).length = f.natDegree := rootSeqDesc_length hf_split
  have hleng : (rootSeqDesc g).length = g.natDegree := rootSeqDesc_length hg_split
  intro j _ hjf hjg
  exact
    rootSlotInterval_inter_nonempty_of_crossing (rootSeqDesc f) (rootSeqDesc g)
      rootSeqDesc_pairwise rootSeqDesc_pairwise
      (by rw [hleng, hlenf, hdeg])
      (fun k hk1 hk2 => hc1 k hk1 (by rw [hlenf] at hk2; exact hk2))
      (fun k hk1 hk2 => hc2 k hk1 (by rw [hlenf] at hk2; exact hk2))
      j hjf hjg

/-- Low-degree base case for the repaired succ-degree common-right-interleaver
endpoint in the positive-combination / no-common-root setting. -/
theorem posComboNoCommonSuccDegreePairHasCommonInterleaver_of_natDegree_le_one
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f) (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g)
    (hdeg : g.natDegree = f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hfdeg : f.natDegree ≤ 1) :
    ∃ h : ℝ[X], Prec f h ∧ Prec g h := by
  obtain ⟨hf_rr, hslot⟩ :=
    succDegreeSlotData_of_posCombo_natDegree_le_one
      hf_pos hg_pos hfnn hgnn hfg hdeg hno hfdeg
  have hg_split : g.Splits :=
    (hfg.isRealRooted_right_of_succDegree hf_pos hg_pos hdeg).2
  exact
    pairHasCommonInterleaver_of_succDegree_slotIntersections
      hf_rr.1 hg_pos.ne_zero hf_rr.2 hg_split hdeg
      (fun j hj => hslot j hj _ _)

/-- Degree-`≤ 2` common-right-interleaver base case without the
nonnegative-coefficient or no-common-root hypotheses. -/
theorem posComboSameDegreePairHasCommonInterleaver_of_natDegree_le_two
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfg : PosComboRealRooted f g)
    (hdeg : g.natDegree = f.natDegree)
    (hfdeg : f.natDegree ≤ 2) :
    ∃ h : ℝ[X], Prec f h ∧ Prec g h := by
  by_cases hle : f.natDegree ≤ 1
  · exact
      posComboNoCommonSameDegreePairHasCommonInterleaver_of_degree_le_one
        hf_pos hg_pos hdeg hle
  · have htwo : f.natDegree = 2 := by lia
    have hf_split : f.Splits :=
      (hfg.isRealRooted_left_of_sameDegree hf_pos hg_pos hdeg).2
    have hg_split : g.Splits :=
      (hfg.isRealRooted_right_of_sameDegree hf_pos hg_pos hdeg).2
    obtain ⟨hc1, hc2⟩ :=
      sameDegreeRootCrossing_of_posCombo_natDegree_eq_two
        hf_pos hg_pos hfg hdeg htwo
    have hlenf : (rootSeqDesc f).length = f.natDegree := rootSeqDesc_length hf_split
    have hleng : (rootSeqDesc g).length = g.natDegree := rootSeqDesc_length hg_split
    refine
      pairHasCommonInterleaver_of_sameDegree_slotIntersections
        hf_pos.ne_zero hg_pos.ne_zero hf_split hg_split hdeg ?_
    intro j hj
    exact
      rootSlotInterval_inter_nonempty_of_sameDegree_crossing
        (rootSeqDesc f) (rootSeqDesc g) rootSeqDesc_pairwise rootSeqDesc_pairwise
        (by rw [hleng, hlenf, hdeg])
        (fun k hk1 hk2 => hc1 k hk1 (by rw [hlenf] at hk2; exact hk2))
        (fun k hk1 hk2 => hc2 k hk1 (by rw [hlenf] at hk2; exact hk2))
        j (by rw [hlenf]; exact hj) (by rw [hleng, hdeg]; exact hj)

/-- Low-degree base case for the repaired same-degree common-right-interleaver
endpoint in the positive-combination / no-common-root setting. -/
theorem posComboNoCommonSameDegreePairHasCommonInterleaver_of_natDegree_le_two
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f) (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g)
    (hdeg : g.natDegree = f.natDegree)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hfdeg : f.natDegree ≤ 2) :
    ∃ h : ℝ[X], Prec f h ∧ Prec g h := by
  have _hfnn := hfnn
  have _hgnn := hgnn
  have _hno := hno
  exact
    posComboSameDegreePairHasCommonInterleaver_of_natDegree_le_two
      hf_pos hg_pos hfg hdeg hfdeg

/-- Low-degree no-common degree-split endpoint in the positive-combination /
nonnegative-coefficient setting.  The same-degree branch uses the checked
degree-`≤ 2` root-crossing route, while the succ-degree branch reduces to the
checked degree-`≤ 1` endpoint for the smaller polynomial. -/
theorem posComboNoCommonPairHasCommonInterleaver_of_natDegree_le_two
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f) (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g)
    (hdeg_lo : f.natDegree ≤ g.natDegree)
    (hdeg_hi : g.natDegree ≤ f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hgdeg : g.natDegree ≤ 2) :
    ∃ h : ℝ[X], Prec f h ∧ Prec g h := by
  rcases Nat.lt_or_ge f.natDegree g.natDegree with hlt | hge
  · have hsucc : g.natDegree = f.natDegree + 1 := by lia
    have hfdeg : f.natDegree ≤ 1 := by lia
    exact
      posComboNoCommonSuccDegreePairHasCommonInterleaver_of_natDegree_le_one
        hf_pos hg_pos hfnn hgnn hfg hsucc hno hfdeg
  · have hsame : g.natDegree = f.natDegree := by lia
    have hfdeg : f.natDegree ≤ 2 := by lia
    exact
      posComboNoCommonSameDegreePairHasCommonInterleaver_of_natDegree_le_two
        hf_pos hg_pos hfnn hgnn hfg hsame hno hfdeg

/-- Degree-`≤ 3` no-common endpoint from cubic same-degree and succ-degree
endpoints. -/
theorem posComboNoCommonPairHasCommonInterleaver_of_natDegree_le_three_of_cubicInterior
    (hbelow : CubicInteriorTwoBelowStatement)
    (habove : CubicInteriorTwoAboveStatement)
    (hsucc : PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement)
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f) (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g)
    (hdeg_lo : f.natDegree ≤ g.natDegree)
    (hdeg_hi : g.natDegree ≤ f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hgdeg : g.natDegree ≤ 3) :
    ∃ h : ℝ[X], Prec f h ∧ Prec g h := by
  rcases Nat.lt_or_ge f.natDegree g.natDegree with hlt | hge
  · have hsucc_deg : g.natDegree = f.natDegree + 1 := by lia
    exact hsucc hf_pos hg_pos hfnn hgnn hfg hsucc_deg hno
  · have hsame : g.natDegree = f.natDegree := by lia
    have hfdeg : f.natDegree ≤ 3 := by lia
    exact
      sameDegreePairHasCommonInterleaver_nonneg_of_natDegree_le_three_of_cubicInterior
        hbelow habove hf_pos hg_pos hfnn hgnn hfg hsame hno hfdeg

/-- Degree-`≤ 3` no-common endpoint naming both the cubic same-degree and
succ-degree branches. -/
theorem posComboNoCommonPairHasCommonInterleaver_of_natDegree_le_three_and_succDegree
    (hbelow : CubicInteriorTwoBelowStatement)
    (habove : CubicInteriorTwoAboveStatement)
    (hsucc : PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement)
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f) (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g)
    (hdeg_lo : f.natDegree ≤ g.natDegree)
    (hdeg_hi : g.natDegree ≤ f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hgdeg : g.natDegree ≤ 3) :
    ∃ h : ℝ[X], Prec f h ∧ Prec g h :=
  posComboNoCommonPairHasCommonInterleaver_of_natDegree_le_three_of_cubicInterior
    hbelow habove hsucc hf_pos hg_pos hfnn hgnn hfg hdeg_lo hdeg_hi hno hgdeg

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
    (hsame : PosComboNoCommonSameDegreePairHasCommonInterleaverNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement)
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f) (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g) :
    ∃ h : ℝ[X], Prec f h ∧ Prec g h :=
  posComboPairHasCommonInterleaver_of_orderedBridge_and_nonnegCoeffs
    (fun {f g} hf_pos hg_pos hfnn hgnn hfg hdeg_lo hdeg_hi =>
      posComboPairHasCommonInterleaver_of_pairDegreeSplit_and_nonnegCoeffs_ordered
        (f := f) (g := g) hsame hsucc hf_pos hg_pos hfnn hgnn hfg hdeg_lo hdeg_hi)
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
  posComboPairHasCommonInterleaver_of_pairDegreeSplit_and_nonnegCoeffs
    (posComboNoCommonSameDegreePairHasCommonInterleaver_of_orientationAlternative_nonneg hsame)
    hsucc hf_pos hg_pos hfnn hgnn hfg

/-- Full positive-combo pair bridge in the nonnegative-coefficient regime,
using the repaired same-degree branch and the affine-family bridge for the
succ-degree branch. -/
theorem posComboPairHasCommonInterleaver_of_sameDegreePair_and_affineFamily_nonneg
    (hsame : PosComboNoCommonSameDegreePairHasCommonInterleaverNonnegStatement)
    (haffBridge : PosComboNoCommonAffineFamilyStatement)
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f) (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g) :
    ∃ h : ℝ[X], Prec f h ∧ Prec g h :=
  posComboPairHasCommonInterleaver_of_pairDegreeSplit_and_nonnegCoeffs
    hsame
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
    (hsame : PosComboNoCommonSameDegreePairHasCommonInterleaverNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement) :
    ∀ ⦃f g : ℝ[X]⦄,
      HasPosLeadingCoeff f →
      HasPosLeadingCoeff g →
      HasNonnegCoeffs f →
      HasNonnegCoeffs g →
      PosComboRealRooted f g →
      ∃ h : ℝ[X], Prec f h ∧ Prec g h :=
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
    (hsame : PosComboNoCommonSameDegreePairHasCommonInterleaverNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement)
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f) (hgnn : HasNonnegCoeffs g)
    (hfg : Compatible f g) :
    ∃ h : ℝ[X], Prec f h ∧ Prec g h :=
  compatiblePairHasCommonInterleaver_of_nonnegPosComboPairBridge
    (nonnegPosComboPairBridge_of_pairDegreeSplit hsame hsucc)
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
  compatiblePairHasCommonInterleaver_of_pairDegreeSplit_and_nonnegCoeffs
    (posComboNoCommonSameDegreePairHasCommonInterleaver_of_orientationAlternative_nonneg hsame)
    hsucc hf_pos hg_pos hfnn hgnn hfg

/-- Compatibility bridge in the nonnegative-coefficient regime, using the
repaired same-degree branch and the affine-family bridge for the succ-degree
branch. -/
theorem compatiblePairHasCommonInterleaver_of_sameDegreePair_and_affineFamily_nonneg
    (hsame : PosComboNoCommonSameDegreePairHasCommonInterleaverNonnegStatement)
    (haffBridge : PosComboNoCommonAffineFamilyStatement)
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f) (hgnn : HasNonnegCoeffs g)
    (hfg : Compatible f g) :
    ∃ h : ℝ[X], Prec f h ∧ Prec g h :=
  compatiblePairHasCommonInterleaver_of_pairDegreeSplit_and_nonnegCoeffs
    hsame
    (posComboNoCommonSuccDegreePairHasCommonInterleaver_of_affineFamily haffBridge)
    hf_pos hg_pos hfnn hgnn hfg

private theorem nonnegPairBridge_of_noCommonOrientation
    (hstep : PosComboNoCommonOrientationStatement) :
    ∀ ⦃f g : ℝ[X]⦄,
      HasPosLeadingCoeff f →
      HasPosLeadingCoeff g →
      HasNonnegCoeffs f →
      HasNonnegCoeffs g →
      Compatible f g →
      ∃ h : ℝ[X], Prec f h ∧ Prec g h :=
  fun {_ _} hf_pos hg_pos hfnn hgnn hfg =>
    compatiblePairHasCommonInterleaver_of_noCommonOrientation_and_nonnegCoeffs
      hstep hf_pos hg_pos hfnn hgnn hfg

private theorem nonnegPairBridge_of_pairDegreeSplit
    (hsame : PosComboNoCommonSameDegreePairHasCommonInterleaverNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement) :
    ∀ ⦃f g : ℝ[X]⦄,
      HasPosLeadingCoeff f →
      HasPosLeadingCoeff g →
      HasNonnegCoeffs f →
      HasNonnegCoeffs g →
      Compatible f g →
      ∃ h : ℝ[X], Prec f h ∧ Prec g h :=
  fun {_ _} hf_pos hg_pos hfnn hgnn hfg =>
    compatiblePairHasCommonInterleaver_of_pairDegreeSplit_and_nonnegCoeffs
      hsame hsucc hf_pos hg_pos hfnn hgnn hfg

private theorem nonnegPairBridge_of_affineFamilyBridge
    (haffBridge : PosComboNoCommonAffineFamilyStatement) :
    ∀ ⦃f g : ℝ[X]⦄,
      HasPosLeadingCoeff f →
      HasPosLeadingCoeff g →
      HasNonnegCoeffs f →
      HasNonnegCoeffs g →
      Compatible f g →
      ∃ h : ℝ[X], Prec f h ∧ Prec g h :=
  fun {_ _} hf_pos hg_pos hfnn hgnn hfg =>
    compatiblePairHasCommonInterleaver_of_affineFamilyBridge_and_nonnegCoeffs
      haffBridge hf_pos hg_pos hfnn hgnn hfg

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
    (hsame : PosComboNoCommonSameDegreePairHasCommonInterleaverNonnegStatement)
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
      posComboPairHasCommonInterleaver_of_pairDegreeSplit_and_nonnegCoeffs
        hsame hsucc (f := F) (g := G) hF_pos hG_pos hFnn hGnn hFG)

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
  posComboPairHasCommonInterleaver_of_pairDegreeSplit_via_nonnegShift
    (posComboNoCommonSameDegreePairHasCommonInterleaver_of_orientationAlternative_nonneg hsame)
    hsucc _hf_rr_ne hf_rr_splits _hg_rr_ne hg_rr_splits hf_pos hg_pos hfg

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
    (hsame : PosComboNoCommonSameDegreePairHasCommonInterleaverNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement) :
    CompatiblePairHasCommonInterleaverStatement :=
  compatiblePairHasCommonInterleaver_of_realRootedPosComboBridge
    (fun {_ _} hf_ne hf_splits hg_ne hg_splits hf_pos hg_pos hfg =>
      posComboPairHasCommonInterleaver_of_pairDegreeSplit_via_nonnegShift
        hsame hsucc hf_ne hf_splits hg_ne hg_splits hf_pos hg_pos hfg)

/-- Shifted compatibility bridge from the concrete slot-data endpoints for the
same-degree and succ-degree nonnegative branches. -/
theorem compatiblePairHasCommonInterleaver_of_slotData_via_nonnegShift
    (hsame : PosComboNoCommonSameDegreeSlotDataNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreeSlotDataNonnegStatement) :
    CompatiblePairHasCommonInterleaverStatement :=
  compatiblePairHasCommonInterleaver_of_pairDegreeSplit_via_nonnegShift
    (sameDegreePairHasCommonInterleaver_nonneg_of_slotData hsame)
    (succDegreePairHasCommonInterleaver_nonneg_of_slotData hsucc)

/-- Shifted compatibility bridge from the root-crossing formulations of the
nonnegative same-degree and succ-degree branches.  The succ-degree branch also
needs the left-splitting input that is part of its slot-data decomposition. -/
theorem compatiblePairHasCommonInterleaver_of_rootCrossing_via_nonnegShift
    (hsame : PosComboNoCommonSameDegreeRootCrossingNonnegStatement)
    (hsplit : PosComboSuccDegreeLeftSplitsNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreeRootCrossingNonnegStatement) :
    CompatiblePairHasCommonInterleaverStatement :=
  compatiblePairHasCommonInterleaver_of_pairDegreeSplit_via_nonnegShift
    (sameDegreePairHasCommonInterleaver_nonneg_of_rootCrossing hsame)
    (succDegreePairHasCommonInterleaver_nonneg_of_leftSplits_and_rootCrossing
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
  compatiblePairHasCommonInterleaver_of_pairDegreeSplit_via_nonnegShift
    (posComboNoCommonSameDegreePairHasCommonInterleaver_of_orientationAlternative_nonneg hsame)
    hsucc

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
    (hsame : PosComboNoCommonSameDegreePairHasCommonInterleaverNonnegStatement)
    (haffBridge : PosComboNoCommonAffineFamilyStatement) :
    CompatiblePairHasCommonInterleaverStatement :=
  compatiblePairHasCommonInterleaver_of_pairDegreeSplit_via_nonnegShift
    hsame
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

/-- Pairwise upgrade using the natural positive-leading two-polynomial bridge. -/
theorem pairwiseHasCommonInterleaver_of_pairwiseCompatible_of_pairBridgePos
    {fs : List ℝ[X]}
    (htwo : CompatiblePairHasCommonInterleaverStatement)
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hpair : PairwiseCompatible fs) :
    PairwiseHasCommonInterleaver fs :=
  fun i j hij =>
    htwo
      (hpos (fs.get i) (List.get_mem _ _))
      (hpos (fs.get j) (List.get_mem _ _))
      (hpair i j hij)

/-- Pairwise upgrade using the honest same-degree/succ-degree compatibility
split. -/
theorem pairwiseHasCommonInterleaver_of_pairwiseCompatible_of_compatibleDegreeSplit
    {fs : List ℝ[X]}
    (hsame : CompatibleSameDegreePairHasCommonInterleaverStatement)
    (hsucc : CompatibleSuccDegreePairHasCommonInterleaverStatement)
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hpair : PairwiseCompatible fs) :
    PairwiseHasCommonInterleaver fs :=
  pairwiseHasCommonInterleaver_of_pairwiseCompatible_of_pairBridgePos
    (compatiblePairHasCommonInterleaver_of_degreeSplit hsame hsucc)
    hpos hpair

/-- Pairwise upgrade from the repaired shifted nonnegative-coefficient
degree-split package. -/
theorem pairwiseHasCommonInterleaver_of_pairwiseCompatible_of_pairDegreeSplit_via_nonnegShift
    {fs : List ℝ[X]}
    (hsame : PosComboNoCommonSameDegreePairHasCommonInterleaverNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement)
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hpair : PairwiseCompatible fs) :
    PairwiseHasCommonInterleaver fs :=
  pairwiseHasCommonInterleaver_of_pairwiseCompatible_of_pairBridgePos
    (compatiblePairHasCommonInterleaver_of_pairDegreeSplit_via_nonnegShift
      hsame hsucc)
    hpos hpair

/-- Pairwise upgrade from the slot-data endpoints after shifting each pair
into the nonnegative regime. -/
theorem pairwiseHasCommonInterleaver_of_pairwiseCompatible_of_slotData_via_nonnegShift
    {fs : List ℝ[X]}
    (hsame : PosComboNoCommonSameDegreeSlotDataNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreeSlotDataNonnegStatement)
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hpair : PairwiseCompatible fs) :
    PairwiseHasCommonInterleaver fs :=
  pairwiseHasCommonInterleaver_of_pairwiseCompatible_of_pairBridgePos
    (compatiblePairHasCommonInterleaver_of_slotData_via_nonnegShift hsame hsucc)
    hpos hpair

/-- Pairwise upgrade from the root-crossing formulations after shifting each
pair into the nonnegative regime. -/
theorem pairwiseHasCommonInterleaver_of_pairwiseCompatible_of_rootCrossing_via_nonnegShift
    {fs : List ℝ[X]}
    (hsame : PosComboNoCommonSameDegreeRootCrossingNonnegStatement)
    (hsplit : PosComboSuccDegreeLeftSplitsNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreeRootCrossingNonnegStatement)
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hpair : PairwiseCompatible fs) :
    PairwiseHasCommonInterleaver fs :=
  pairwiseHasCommonInterleaver_of_pairwiseCompatible_of_pairBridgePos
    (compatiblePairHasCommonInterleaver_of_rootCrossing_via_nonnegShift
      hsame hsplit hsucc)
    hpos hpair

/-- Pairwise upgrade from root-crossing formulations alone.  The succ-degree
left endpoint is supplied by root continuity before shifting. -/
theorem pairwiseHasCommonInterleaver_of_pairwiseCompatible_of_rootCrossing
    {fs : List ℝ[X]}
    (hsame : PosComboNoCommonSameDegreeRootCrossingNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreeRootCrossingNonnegStatement)
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hpair : PairwiseCompatible fs) :
    PairwiseHasCommonInterleaver fs :=
  pairwiseHasCommonInterleaver_of_pairwiseCompatible_of_rootCrossing_via_nonnegShift
    hsame PosComboSuccDegreeLeftSplitsNonnegStatement_of_rootContinuity hsucc hpos hpair

/-- Pairwise upgrade from lower-threshold root-count formulations. -/
theorem pairwiseHasCommonInterleaver_of_pairwiseCompatible_of_rootCount
    {fs : List ℝ[X]}
    (hsame : PosComboNoCommonSameDegreeRootCountNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreeRootCountNonnegStatement)
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hpair : PairwiseCompatible fs) :
    PairwiseHasCommonInterleaver fs :=
  pairwiseHasCommonInterleaver_of_pairwiseCompatible_of_rootCrossing
    (posComboNoCommonSameDegreeRootCrossing_of_rootCount hsame)
    (posComboNoCommonSuccDegreeRootCrossing_of_rootCount hsucc) hpos hpair

/-- Pairwise upgrade from same-degree lower-threshold root counts and
succ-degree upper-threshold root counts. -/
theorem pairwiseHasCommonInterleaver_of_pairwiseCompatible_of_rootCountAbove
    {fs : List ℝ[X]}
    (hsame : PosComboNoCommonSameDegreeRootCountNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreeRootCountAboveNonnegStatement)
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hpair : PairwiseCompatible fs) :
    PairwiseHasCommonInterleaver fs :=
  pairwiseHasCommonInterleaver_of_pairwiseCompatible_of_rootCrossing
    (posComboNoCommonSameDegreeRootCrossing_of_rootCount hsame)
    (posComboNoCommonSuccDegreeRootCrossing_of_rootCountAbove hsucc) hpos hpair

/-- Pairwise upgrade from same-degree upper-threshold root counts and
succ-degree lower-threshold root counts. -/
theorem pairwiseHasCommonInterleaver_of_pairwiseCompatible_of_sameRootCountAbove
    {fs : List ℝ[X]}
    (hsame : PosComboNoCommonSameDegreeRootCountAboveNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreeRootCountNonnegStatement)
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hpair : PairwiseCompatible fs) :
    PairwiseHasCommonInterleaver fs :=
  pairwiseHasCommonInterleaver_of_pairwiseCompatible_of_pairBridgePos
    (compatiblePairHasCommonInterleaver_of_sameRootCountAbove hsame hsucc)
    hpos hpair

/-- Pairwise upgrade from upper-threshold root-count formulations in both the
same-degree and succ-degree branches. -/
theorem pairwiseHasCommonInterleaver_of_pairwiseCompatible_of_rootCountAboveBoth
    {fs : List ℝ[X]}
    (hsame : PosComboNoCommonSameDegreeRootCountAboveNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreeRootCountAboveNonnegStatement)
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hpair : PairwiseCompatible fs) :
    PairwiseHasCommonInterleaver fs :=
  pairwiseHasCommonInterleaver_of_pairwiseCompatible_of_pairBridgePos
    (compatiblePairHasCommonInterleaver_of_rootCountAboveBoth hsame hsucc)
    hpos hpair

/-- Pairwise upgrade from common-non-root lower-threshold root-count
formulations in both branches. -/
theorem pairwiseHasCommonInterleaver_of_pairwiseCompatible_of_rootCountNonRoot
    {fs : List ℝ[X]}
    (hsame : PosComboNoCommonSameDegreeRootCountNonRootNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreeRootCountNonRootNonnegStatement)
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hpair : PairwiseCompatible fs) :
    PairwiseHasCommonInterleaver fs :=
  pairwiseHasCommonInterleaver_of_pairwiseCompatible_of_pairBridgePos
    (compatiblePairHasCommonInterleaver_of_rootCountNonRoot hsame hsucc)
    hpos hpair

/-- Pairwise upgrade from same-degree common-non-root lower-threshold root
counts and succ-degree common-non-root upper-threshold root counts. -/
theorem
    pairwiseHasCommonInterleaver_of_pairwiseCompatible_of_rootCountAboveNonRoot
    {fs : List ℝ[X]}
    (hsame : PosComboNoCommonSameDegreeRootCountNonRootNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreeRootCountAboveNonRootNonnegStatement)
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hpair : PairwiseCompatible fs) :
    PairwiseHasCommonInterleaver fs :=
  pairwiseHasCommonInterleaver_of_pairwiseCompatible_of_pairBridgePos
    (compatiblePairHasCommonInterleaver_of_rootCountAboveNonRoot hsame hsucc)
    hpos hpair

/-- Pairwise upgrade from same-degree common-non-root upper-threshold root
counts and succ-degree common-non-root lower-threshold root counts. -/
theorem
    pairwiseHasCommonInterleaver_of_pairwiseCompatible_of_sameRootCountAboveNonRoot
    {fs : List ℝ[X]}
    (hsame : PosComboNoCommonSameDegreeRootCountAboveNonRootNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreeRootCountNonRootNonnegStatement)
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hpair : PairwiseCompatible fs) :
    PairwiseHasCommonInterleaver fs :=
  pairwiseHasCommonInterleaver_of_pairwiseCompatible_of_pairBridgePos
    (compatiblePairHasCommonInterleaver_of_sameRootCountAboveNonRoot hsame hsucc)
    hpos hpair

/-- Pairwise upgrade from common-non-root upper-threshold root-count
formulations in both branches. -/
theorem
    pairwiseHasCommonInterleaver_of_pairwiseCompatible_of_rootCountAboveBothNonRoot
    {fs : List ℝ[X]}
    (hsame : PosComboNoCommonSameDegreeRootCountAboveNonRootNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreeRootCountAboveNonRootNonnegStatement)
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hpair : PairwiseCompatible fs) :
    PairwiseHasCommonInterleaver fs :=
  pairwiseHasCommonInterleaver_of_pairwiseCompatible_of_pairBridgePos
    (compatiblePairHasCommonInterleaver_of_rootCountAboveBothNonRoot hsame hsucc)
    hpos hpair

/-- Pairwise upgrade from root-crossing formulations, with the succ-degree left
endpoint supplied by the PF/ASW route before shifting. -/
theorem
    pairwiseHasCommonInterleaver_of_pairwiseCompatible_of_rootCrossing_and_forward_asw
    {fs : List ℝ[X]}
    (hsame : PosComboNoCommonSameDegreeRootCrossingNonnegStatement)
    (hASW : aissenSchoenbergWhitneyForwardOrZeroStatement)
    (hsucc : PosComboNoCommonSuccDegreeRootCrossingNonnegStatement)
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hpair : PairwiseCompatible fs) :
    PairwiseHasCommonInterleaver fs :=
  pairwiseHasCommonInterleaver_of_pairwiseCompatible_of_pairBridgePos
    (compatiblePairHasCommonInterleaver_of_rootCrossing_and_forward_asw
      hsame hASW hsucc)
    hpos hpair

/-- Pairwise upgrade from root-crossing formulations, with the succ-degree left
endpoint supplied by the splitting-only ASW target before shifting. -/
theorem
    pairwiseHasCommonInterleaver_of_pairwiseCompatible_of_rootCrossing_and_forward_asw_splits
    {fs : List ℝ[X]}
    (hsame : PosComboNoCommonSameDegreeRootCrossingNonnegStatement)
    (hASW : aissenSchoenbergWhitneyForwardSplitsStatement)
    (hsucc : PosComboNoCommonSuccDegreeRootCrossingNonnegStatement)
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hpair : PairwiseCompatible fs) :
    PairwiseHasCommonInterleaver fs :=
  pairwiseHasCommonInterleaver_of_pairwiseCompatible_of_rootCrossing_and_forward_asw
    hsame (aissenSchoenbergWhitneyForwardOrZero_of_splits hASW) hsucc hpos hpair

/-- Pairwise upgrade from the nonnegative-coefficient degree-split package,
after shifting each pair into the nonnegative regime. -/
theorem pairwiseHasCommonInterleaver_of_pairwiseCompatible_of_degreeSplit_via_nonnegShift
    {fs : List ℝ[X]}
    (hsame : PosComboNoCommonSameDegreeOrientationAlternativeNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement)
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hpair : PairwiseCompatible fs) :
    PairwiseHasCommonInterleaver fs :=
  pairwiseHasCommonInterleaver_of_pairwiseCompatible_of_pairDegreeSplit_via_nonnegShift
    (posComboNoCommonSameDegreePairHasCommonInterleaver_of_orientationAlternative_nonneg
      hsame)
    hsucc hpos hpair

/-- Pairwise upgrade after the nonnegative shift reduction, with the
succ-degree branch discharged by the affine-family bridge. -/
theorem
    pairwiseHasCommonInterleaver_of_pairwiseCompatible_nonnegShift
    {fs : List ℝ[X]}
    (hsame : PosComboNoCommonSameDegreeOrientationAlternativeNonnegStatement)
    (haffBridge : PosComboNoCommonAffineFamilyStatement)
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hpair : PairwiseCompatible fs) :
    PairwiseHasCommonInterleaver fs :=
  pairwiseHasCommonInterleaver_of_pairwiseCompatible_of_degreeSplit_via_nonnegShift
    hsame
    (posComboNoCommonSuccDegreePairHasCommonInterleaver_of_affineFamily haffBridge)
    hpos hpair

/-- Pairwise upgrade from the boundary-right-pair hypothesis after shifting
each pair into the nonnegative regime. -/
theorem
    pairwiseHasCommonInterleaver_of_pairwiseCompatible_of_boundaryRightPairOrientation
    {fs : List ℝ[X]}
    (hboundary : PosComboNoCommonBoundaryRightPairOrientationStatement)
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hpair : PairwiseCompatible fs) :
    PairwiseHasCommonInterleaver fs :=
  pairwiseHasCommonInterleaver_of_pairwiseCompatible_nonnegShift
    (boundaryRightPairOrientation_implies_sameDegreeOrientationAlternative_nonneg
      hboundary)
    (posComboNoCommonAffineFamily_of_boundaryRightPairOrientation hboundary)
    hpos hpair

private theorem pairwiseHasCommonInterleaver_of_nonnegPairBridge
    {fs : List ℝ[X]}
    (hbridge :
      ∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        Compatible f g →
        ∃ h : ℝ[X], Prec f h ∧ Prec g h)
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hnn : ∀ f ∈ fs, HasNonnegCoeffs f)
    (hpair : PairwiseCompatible fs) :
    PairwiseHasCommonInterleaver fs :=
  fun i j hij =>
    hbridge
      (hpos (fs.get i) (List.get_mem _ _))
      (hpos (fs.get j) (List.get_mem _ _))
      (hnn (fs.get i) (List.get_mem _ _))
      (hnn (fs.get j) (List.get_mem _ _))
      (hpair i j hij)

/-- Pairwise upgrade in the nonnegative-coefficient regime from the
no-common-roots orientation core. -/
theorem pairwiseHasCommonInterleaver_of_pairwiseCompatible_of_noCommonOrientation_and_nonnegCoeffs
    {fs : List ℝ[X]}
    (hstep : PosComboNoCommonOrientationStatement)
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hnn : ∀ f ∈ fs, HasNonnegCoeffs f)
    (hpair : PairwiseCompatible fs) :
    PairwiseHasCommonInterleaver fs :=
  pairwiseHasCommonInterleaver_of_nonnegPairBridge
    (nonnegPairBridge_of_noCommonOrientation hstep)
    hpos hnn hpair

/-- Pairwise upgrade in the nonnegative-coefficient regime from the repaired
degree-split package. -/
theorem pairwiseHasCommonInterleaver_of_pairwiseCompatible_of_pairDegreeSplit_and_nonnegCoeffs
    {fs : List ℝ[X]}
    (hsame : PosComboNoCommonSameDegreePairHasCommonInterleaverNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement)
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hnn : ∀ f ∈ fs, HasNonnegCoeffs f)
    (hpair : PairwiseCompatible fs) :
    PairwiseHasCommonInterleaver fs :=
  pairwiseHasCommonInterleaver_of_nonnegPairBridge
    (nonnegPairBridge_of_pairDegreeSplit hsame hsucc)
    hpos hnn hpair

/-- Pairwise upgrade in the nonnegative-coefficient regime from the honest
degree-split package. -/
theorem pairwiseHasCommonInterleaver_of_pairwiseCompatible_of_degreeSplit_and_nonnegCoeffs
    {fs : List ℝ[X]}
    (hsame : PosComboNoCommonSameDegreeOrientationAlternativeNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement)
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hnn : ∀ f ∈ fs, HasNonnegCoeffs f)
    (hpair : PairwiseCompatible fs) :
    PairwiseHasCommonInterleaver fs :=
  pairwiseHasCommonInterleaver_of_pairwiseCompatible_of_pairDegreeSplit_and_nonnegCoeffs
    (posComboNoCommonSameDegreePairHasCommonInterleaver_of_orientationAlternative_nonneg hsame)
    hsucc hpos hnn hpair

/-- Pairwise upgrade in the nonnegative-coefficient regime, using the repaired
same-degree branch and the affine-family bridge for the succ-degree branch. -/
theorem pairwiseHasCommonInterleaver_of_pairwiseCompatible_of_sameDegreePair_and_affineFamily_nonneg
    {fs : List ℝ[X]}
    (hsame : PosComboNoCommonSameDegreePairHasCommonInterleaverNonnegStatement)
    (haffBridge : PosComboNoCommonAffineFamilyStatement)
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hnn : ∀ f ∈ fs, HasNonnegCoeffs f)
    (hpair : PairwiseCompatible fs) :
    PairwiseHasCommonInterleaver fs :=
  pairwiseHasCommonInterleaver_of_pairwiseCompatible_of_pairDegreeSplit_and_nonnegCoeffs
    hsame
    (posComboNoCommonSuccDegreePairHasCommonInterleaver_of_affineFamily haffBridge)
    hpos hnn hpair

/-- Pairwise upgrade in the nonnegative-coefficient regime from the
all-combinations bridge. -/
theorem pairwiseHasCommonInterleaver_of_pairwiseCompatible_of_allComboBridge_and_nonnegCoeffs
    {fs : List ℝ[X]}
    (hallBridge : PosComboNoCommonToAllComboBridgeStatement)
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hnn : ∀ f ∈ fs, HasNonnegCoeffs f)
    (hpair : PairwiseCompatible fs) :
    PairwiseHasCommonInterleaver fs :=
  pairwiseHasCommonInterleaver_of_pairwiseCompatible_of_noCommonOrientation_and_nonnegCoeffs
    (posComboNoCommonOrientation_of_allComboBridge hallBridge)
    hpos hnn hpair

/-- Pairwise upgrade in the nonnegative-coefficient regime from the
affine-family bridge. -/
theorem pairwiseHasCommonInterleaver_of_pairwiseCompatible_of_affineFamilyBridge_and_nonnegCoeffs
    {fs : List ℝ[X]}
    (haffBridge : PosComboNoCommonAffineFamilyStatement)
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hnn : ∀ f ∈ fs, HasNonnegCoeffs f)
    (hpair : PairwiseCompatible fs) :
    PairwiseHasCommonInterleaver fs :=
  pairwiseHasCommonInterleaver_of_nonnegPairBridge
    (nonnegPairBridge_of_affineFamilyBridge haffBridge)
    hpos hnn hpair

/-- Pairwise upgrade in the nonnegative-coefficient regime from the
boundary-right-pair orientation statement. -/
theorem
    pairwiseHasCommonInterleaver_of_pairwiseCompatible_of_boundaryRightPairOrientation_nonneg
    {fs : List ℝ[X]}
    (hboundary : PosComboNoCommonBoundaryRightPairOrientationStatement)
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hnn : ∀ f ∈ fs, HasNonnegCoeffs f)
    (hpair : PairwiseCompatible fs) :
    PairwiseHasCommonInterleaver fs :=
  pairwiseHasCommonInterleaver_of_pairwiseCompatible_of_affineFamilyBridge_and_nonnegCoeffs
    (posComboNoCommonAffineFamily_of_boundaryRightPairOrientation hboundary)
    hpos hnn hpair

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
  rcases hcommon with ⟨h, hprec⟩
  intro l hmem hnonneg
  by_cases hex : ∃ ap ∈ l, 0 < ap.1
  · right
    have hprec_l : ∀ ap ∈ l, Prec ap.2 h := by grind
    have hpos_l : ∀ ap ∈ l, HasPosLeadingCoeff ap.2 := by grind
    exact (prec_weightedSum_right l h hnonneg hprec_l hpos_l hex).1
  · left
    have hall_zero : ∀ ap ∈ l, ap.1 = 0 := by grind
    exact weightedSum_eq_zero_of_forall_coeff_zero l hall_zero

/-- Full family compatibility implies pairwise compatibility by specializing to
two-term weighted sums. -/
theorem pairwiseCompatible_of_familyCompatible
    {fs : List ℝ[X]}
    (hfull : FamilyCompatible fs) :
    PairwiseCompatible fs := by
  intro i j hij α β hα hβ
  let fi : ℝ[X] := fs.get i
  let fj : ℝ[X] := fs.get j
  have hpair :
      weightedSum [(α, fi), (β, fj)] = 0 ∨
        ((weightedSum [(α, fi), (β, fj)]) ≠ 0 ∧
          (weightedSum [(α, fi), (β, fj)]).Splits) :=
    hfull [(α, fi), (β, fj)] (by grind) (by simp_all)
  simpa [fi, fj, weightedSum, weightedSum_cons] using hpair

/-- A forward common-interleaver upgrade is enough to identify pairwise
compatibility with full family compatibility for positive-leading families. -/
theorem pairwiseCompatible_iff_familyCompatible_of_commonInterleaver_forward
    {fs : List ℝ[X]}
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hcommon : PairwiseCompatible fs → HasCommonInterleaver fs) :
    PairwiseCompatible fs ↔ FamilyCompatible fs :=
  ⟨fun hpair => familyCompatible_of_commonInterleaver (hcommon hpair) hpos,
    pairwiseCompatible_of_familyCompatible⟩

/-- The finite-family four-way Chudnovsky--Seymour package used by this
project: pairwise compatibility, pairwise common right interleavers, global
common right interleaver, and full nonnegative family compatibility. -/
abbrev ChudnovskySeymourFourWayPackage (fs : List ℝ[X]) : Prop :=
  (PairwiseCompatible fs ↔ PairwiseHasCommonInterleaver fs) ∧
    (PairwiseHasCommonInterleaver fs ↔ HasCommonInterleaver fs) ∧
    (HasCommonInterleaver fs ↔ FamilyCompatible fs)

private theorem chudnovskySeymour_fourWay_of_pairwiseCompatible_iff_pairwiseCommon
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (h12 : PairwiseCompatible fs ↔ PairwiseHasCommonInterleaver fs) :
    ChudnovskySeymourFourWayPackage fs := by
  have h23 : PairwiseHasCommonInterleaver fs ↔ HasCommonInterleaver fs :=
    ⟨commonInterleaverFamilyUpgrade
        (fun f hf => (hrr f hf).2) hpos,
      pairwiseHasCommonInterleaver_of_commonInterleaver⟩
  have h34 : HasCommonInterleaver fs ↔ FamilyCompatible fs :=
    ⟨fun hcommon => familyCompatible_of_commonInterleaver hcommon hpos,
      fun hfull => h23.1 (h12.1 (pairwiseCompatible_of_familyCompatible hfull))⟩
  exact ⟨h12, h23, h34⟩

private theorem chudnovskySeymour_fourWay_of_pairwiseCommonForward
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hforward : PairwiseCompatible fs → PairwiseHasCommonInterleaver fs) :
    ChudnovskySeymourFourWayPackage fs :=
  chudnovskySeymour_fourWay_of_pairwiseCompatible_iff_pairwiseCommon hrr hpos
    ⟨hforward, fun hpair => pairwiseCompatible_of_pairwiseHasCommonInterleaver hpair hpos⟩

/-- Chudnovsky--Seymour four-way package in the finite-list language used in
this project, with the two-polynomial converse isolated as hypothesis:

1. pairwise compatibility,
2. pairwise common right interleavers,
3. a global common right interleaver,
4. full nonnegative family compatibility. -/
theorem chudnovskySeymour_fourWay_of_pairBridge
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (htwo : CompatiblePairHasCommonRightInterleaverStatement) :
    ChudnovskySeymourFourWayPackage fs :=
  chudnovskySeymour_fourWay_of_pairwiseCommonForward hrr hpos <|
    pairwiseHasCommonInterleaver_of_pairwiseCompatible htwo hpos

/-- Chudnovsky--Seymour four-way package with the natural two-polynomial bridge
assumption (requiring positive leading coefficients on the pair). -/
theorem chudnovskySeymour_fourWay_of_pairBridgePos
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (htwo : CompatiblePairHasCommonInterleaverStatement) :
    ChudnovskySeymourFourWayPackage fs :=
  chudnovskySeymour_fourWay_of_pairwiseCommonForward hrr hpos <|
    pairwiseHasCommonInterleaver_of_pairwiseCompatible_of_pairBridgePos htwo hpos

/-- Four-way Chudnovsky--Seymour package from the honest same-degree/succ-degree
compatibility split. -/
theorem chudnovskySeymour_fourWay_of_compatibleDegreeSplit
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hsame : CompatibleSameDegreePairHasCommonInterleaverStatement)
    (hsucc : CompatibleSuccDegreePairHasCommonInterleaverStatement) :
    ChudnovskySeymourFourWayPackage fs :=
  chudnovskySeymour_fourWay_of_pairBridgePos
    (hrr := hrr) (hpos := hpos)
    (compatiblePairHasCommonInterleaver_of_degreeSplit hsame hsucc)

/-- Four-way Chudnovsky--Seymour package from the repaired shifted
nonnegative-coefficient degree split. -/
theorem chudnovskySeymour_fourWay_of_pairDegreeSplit_via_nonnegShift
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hsame : PosComboNoCommonSameDegreePairHasCommonInterleaverNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement) :
    ChudnovskySeymourFourWayPackage fs :=
  chudnovskySeymour_fourWay_of_pairBridgePos
    (hrr := hrr) (hpos := hpos)
    (compatiblePairHasCommonInterleaver_of_pairDegreeSplit_via_nonnegShift
      hsame hsucc)

/-- Four-way Chudnovsky--Seymour package from the concrete slot-data endpoints
for the nonnegative same-degree and succ-degree branches, upgraded by the
nonnegative-shift reduction. -/
theorem chudnovskySeymour_fourWay_of_slotData_via_nonnegShift
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hsame : PosComboNoCommonSameDegreeSlotDataNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreeSlotDataNonnegStatement) :
    ChudnovskySeymourFourWayPackage fs :=
  chudnovskySeymour_fourWay_of_pairBridgePos
    (hrr := hrr) (hpos := hpos)
    (compatiblePairHasCommonInterleaver_of_slotData_via_nonnegShift hsame hsucc)

/-- Four-way Chudnovsky--Seymour package from the root-crossing formulations
of the same-degree and succ-degree branches, upgraded by the nonnegative-shift
reduction. -/
theorem chudnovskySeymour_fourWay_of_rootCrossing_via_nonnegShift
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hsame : PosComboNoCommonSameDegreeRootCrossingNonnegStatement)
    (hsplit : PosComboSuccDegreeLeftSplitsNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreeRootCrossingNonnegStatement) :
    ChudnovskySeymourFourWayPackage fs :=
  chudnovskySeymour_fourWay_of_pairBridgePos
    (hrr := hrr) (hpos := hpos)
    (compatiblePairHasCommonInterleaver_of_rootCrossing_via_nonnegShift
      hsame hsplit hsucc)

/-- Four-way Chudnovsky--Seymour package from root-crossing formulations alone.
The succ-degree left endpoint is supplied by root continuity before shifting. -/
theorem chudnovskySeymour_fourWay_of_rootCrossing
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hsame : PosComboNoCommonSameDegreeRootCrossingNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreeRootCrossingNonnegStatement) :
    ChudnovskySeymourFourWayPackage fs :=
  chudnovskySeymour_fourWay_of_rootCrossing_via_nonnegShift
    hrr hpos hsame PosComboSuccDegreeLeftSplitsNonnegStatement_of_rootContinuity hsucc

/-- Four-way Chudnovsky--Seymour package from root-crossing formulations, with
the succ-degree left endpoint supplied by the PF/ASW route before shifting. -/
theorem chudnovskySeymour_fourWay_of_rootCrossing_and_forward_asw
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hsame : PosComboNoCommonSameDegreeRootCrossingNonnegStatement)
    (hASW : aissenSchoenbergWhitneyForwardOrZeroStatement)
    (hsucc : PosComboNoCommonSuccDegreeRootCrossingNonnegStatement) :
    ChudnovskySeymourFourWayPackage fs :=
  chudnovskySeymour_fourWay_of_pairBridgePos
    (hrr := hrr) (hpos := hpos)
    (compatiblePairHasCommonInterleaver_of_rootCrossing_and_forward_asw
      hsame hASW hsucc)

/-- Four-way Chudnovsky--Seymour package from root-crossing formulations, with
the succ-degree left endpoint supplied by the splitting-only ASW target before
shifting. -/
theorem chudnovskySeymour_fourWay_of_rootCrossing_and_forward_asw_splits
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hsame : PosComboNoCommonSameDegreeRootCrossingNonnegStatement)
    (hASW : aissenSchoenbergWhitneyForwardSplitsStatement)
    (hsucc : PosComboNoCommonSuccDegreeRootCrossingNonnegStatement) :
    ChudnovskySeymourFourWayPackage fs :=
  chudnovskySeymour_fourWay_of_rootCrossing_and_forward_asw
    (fs := fs) hrr hpos hsame
    (aissenSchoenbergWhitneyForwardOrZero_of_splits hASW) hsucc

/-- Four-way Chudnovsky--Seymour package from the nonnegative-coefficient
degree-split package, upgraded to arbitrary positive-leading families by a
common translation trick applied pairwise. -/
theorem chudnovskySeymour_fourWay_of_degreeSplit_via_nonnegShift
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hsame : PosComboNoCommonSameDegreeOrientationAlternativeNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement) :
    ChudnovskySeymourFourWayPackage fs :=
  chudnovskySeymour_fourWay_of_pairDegreeSplit_via_nonnegShift
    (fs := fs) hrr hpos
    (posComboNoCommonSameDegreePairHasCommonInterleaver_of_orientationAlternative_nonneg
      hsame)
    hsucc

/-- Four-way Chudnovsky--Seymour package after the nonnegative shift
reduction, with the succ-degree branch discharged by the affine-family bridge.
-/
theorem chudnovskySeymour_fourWay_of_sameDegreeAlternative_and_affineFamily_via_nonnegShift
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hsame : PosComboNoCommonSameDegreeOrientationAlternativeNonnegStatement)
    (haffBridge : PosComboNoCommonAffineFamilyStatement) :
    ChudnovskySeymourFourWayPackage fs :=
  chudnovskySeymour_fourWay_of_degreeSplit_via_nonnegShift
    (fs := fs) hrr hpos hsame
    (posComboNoCommonSuccDegreePairHasCommonInterleaver_of_affineFamily haffBridge)

/-- Four-way Chudnovsky--Seymour package from the stronger boundary-right-pair
statement, upgraded to arbitrary positive-leading families by the shift
reduction. -/
theorem chudnovskySeymour_fourWay_of_boundaryRightPairOrientation_via_nonnegShift
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hboundary : PosComboNoCommonBoundaryRightPairOrientationStatement) :
    ChudnovskySeymourFourWayPackage fs :=
  chudnovskySeymour_fourWay_of_sameDegreeAlternative_and_affineFamily_via_nonnegShift
    (fs := fs) hrr hpos
    (boundaryRightPairOrientation_implies_sameDegreeOrientationAlternative_nonneg
      hboundary)
    (posComboNoCommonAffineFamily_of_boundaryRightPairOrientation hboundary)

/-- Same four-way Chudnovsky--Seymour package, with assumptions phrased via the
positive-combination two-polynomial bridge. -/
theorem chudnovskySeymour_fourWay_of_posComboBridge
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hposComboBridge : PosComboPairHasCommonInterleaverStatement) :
    ChudnovskySeymourFourWayPackage fs :=
  chudnovskySeymour_fourWay_of_pairBridgePos
    (hrr := hrr) (hpos := hpos)
    (compatiblePairHasCommonInterleaver_of_posComboPair hposComboBridge)

/-- Same four-way package from the reduced positive-combo ingredients:
no-common orientation and degree closeness for `PosComboRealRooted` pairs. -/
theorem chudnovskySeymour_fourWay_of_noCommonOrientation_and_degreeClose
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hstep : PosComboNoCommonOrientationStatement)
    (hdegClose : PosComboNatDegreeCloseStatement) :
    ChudnovskySeymourFourWayPackage fs :=
  chudnovskySeymour_fourWay_of_posComboBridge
    (hrr := hrr) (hpos := hpos)
    (posComboPairHasCommonInterleaver_of_noCommonOrientation_and_degreeClose
      hstep hdegClose)

private theorem chudnovskySeymour_fourWay_of_nonnegPairBridge
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hnn : ∀ f ∈ fs, HasNonnegCoeffs f)
    (hbridge :
      ∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        Compatible f g →
        ∃ h : ℝ[X], Prec f h ∧ Prec g h) :
    ChudnovskySeymourFourWayPackage fs :=
  chudnovskySeymour_fourWay_of_pairwiseCommonForward hrr hpos <|
    pairwiseHasCommonInterleaver_of_nonnegPairBridge hbridge hpos hnn

/-- Four-way Chudnovsky--Seymour package from no-common orientation in the
nonnegative-coefficient regime (where degree closeness is automatic). -/
theorem chudnovskySeymour_fourWay_of_noCommonOrientation_and_nonnegCoeffs
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hnn : ∀ f ∈ fs, HasNonnegCoeffs f)
    (hstep : PosComboNoCommonOrientationStatement) :
    ChudnovskySeymourFourWayPackage fs :=
  chudnovskySeymour_fourWay_of_nonnegPairBridge hrr hpos hnn
    (nonnegPairBridge_of_noCommonOrientation hstep)

/-- Four-way Chudnovsky--Seymour package in the nonnegative-coefficient regime
from the repaired degree split: both same-degree and succ-degree no-common
branches are stated directly as common-interleaver bridges. -/
theorem chudnovskySeymour_fourWay_of_pairDegreeSplit_and_nonnegCoeffs
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hnn : ∀ f ∈ fs, HasNonnegCoeffs f)
    (hsame : PosComboNoCommonSameDegreePairHasCommonInterleaverNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement) :
    ChudnovskySeymourFourWayPackage fs :=
  chudnovskySeymour_fourWay_of_nonnegPairBridge hrr hpos hnn
    (nonnegPairBridge_of_pairDegreeSplit hsame hsucc)

/-- Four-way Chudnovsky--Seymour package in the nonnegative-coefficient regime
from the honest same-degree/succ-degree split, where the succ-degree branch is
stated directly as a common-interleaver bridge. -/
theorem chudnovskySeymour_fourWay_of_degreeSplit_and_nonnegCoeffs
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hnn : ∀ f ∈ fs, HasNonnegCoeffs f)
    (hsame : PosComboNoCommonSameDegreeOrientationAlternativeNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement) :
    ChudnovskySeymourFourWayPackage fs :=
  chudnovskySeymour_fourWay_of_pairDegreeSplit_and_nonnegCoeffs
    (fs := fs) hrr hpos hnn
    (posComboNoCommonSameDegreePairHasCommonInterleaver_of_orientationAlternative_nonneg hsame)
    hsucc

/-- Four-way Chudnovsky--Seymour package in the nonnegative-coefficient regime,
using the repaired same-degree branch and the affine-family bridge for the
succ-degree branch. -/
theorem chudnovskySeymour_fourWay_of_sameDegreePair_and_affineFamily_nonneg
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hnn : ∀ f ∈ fs, HasNonnegCoeffs f)
    (hsame : PosComboNoCommonSameDegreePairHasCommonInterleaverNonnegStatement)
    (haffBridge : PosComboNoCommonAffineFamilyStatement) :
    ChudnovskySeymourFourWayPackage fs :=
  chudnovskySeymour_fourWay_of_pairDegreeSplit_and_nonnegCoeffs
    (fs := fs) hrr hpos hnn hsame
    (posComboNoCommonSuccDegreePairHasCommonInterleaver_of_affineFamily haffBridge)

/-- Four-way Chudnovsky--Seymour package in the nonnegative-coefficient regime
from the all-combinations bridge. -/
theorem chudnovskySeymour_fourWay_of_allComboBridge_and_nonnegCoeffs
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hnn : ∀ f ∈ fs, HasNonnegCoeffs f)
    (hallBridge : PosComboNoCommonToAllComboBridgeStatement) :
    ChudnovskySeymourFourWayPackage fs :=
  chudnovskySeymour_fourWay_of_noCommonOrientation_and_nonnegCoeffs
    (fs := fs) hrr hpos hnn
    (posComboNoCommonOrientation_of_allComboBridge hallBridge)

/-- Four-way Chudnovsky--Seymour package in the nonnegative-coefficient regime
from the affine-family bridge. -/
theorem chudnovskySeymour_fourWay_of_affineFamilyBridge_and_nonnegCoeffs
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hnn : ∀ f ∈ fs, HasNonnegCoeffs f)
    (haffBridge : PosComboNoCommonAffineFamilyStatement) :
    ChudnovskySeymourFourWayPackage fs :=
  chudnovskySeymour_fourWay_of_nonnegPairBridge hrr hpos hnn
    (nonnegPairBridge_of_affineFamilyBridge haffBridge)

/-- Four-way Chudnovsky--Seymour package in the nonnegative-coefficient regime
from the boundary-right-pair orientation statement. -/
theorem chudnovskySeymour_fourWay_of_boundaryRightPairOrientation_and_nonnegCoeffs
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hnn : ∀ f ∈ fs, HasNonnegCoeffs f)
    (hboundary : PosComboNoCommonBoundaryRightPairOrientationStatement) :
    ChudnovskySeymourFourWayPackage fs :=
  chudnovskySeymour_fourWay_of_affineFamilyBridge_and_nonnegCoeffs
    (fs := fs) hrr hpos hnn
    (posComboNoCommonAffineFamily_of_boundaryRightPairOrientation hboundary)

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

/-- Chudnovsky--Seymour `1 ↔ 3` corollary under the natural positive-leading
pair bridge. -/
theorem pairwiseCompatible_iff_hasCommonInterleaver_of_pairBridgePos
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (htwo : CompatiblePairHasCommonInterleaverStatement) :
    PairwiseCompatible fs ↔ HasCommonInterleaver fs :=
  pairwiseCompatible_iff_hasCommonInterleaver_of_fourWay <|
    chudnovskySeymour_fourWay_of_pairBridgePos
      (fs := fs) hrr hpos htwo

/-- Chudnovsky--Seymour `1 ↔ 3` corollary from the honest same-degree /
succ-degree compatibility split. -/
theorem pairwiseCompatible_iff_hasCommonInterleaver_of_compatibleDegreeSplit
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hsame : CompatibleSameDegreePairHasCommonInterleaverStatement)
    (hsucc : CompatibleSuccDegreePairHasCommonInterleaverStatement) :
    PairwiseCompatible fs ↔ HasCommonInterleaver fs :=
  pairwiseCompatible_iff_hasCommonInterleaver_of_fourWay <|
    chudnovskySeymour_fourWay_of_compatibleDegreeSplit
      (fs := fs) hrr hpos hsame hsucc

/-- Chudnovsky--Seymour `1 ↔ 3` corollary from the repaired shifted
nonnegative-coefficient degree split. -/
theorem pairwiseCompatible_iff_hasCommonInterleaver_of_pairDegreeSplit_via_nonnegShift
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hsame : PosComboNoCommonSameDegreePairHasCommonInterleaverNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement) :
    PairwiseCompatible fs ↔ HasCommonInterleaver fs :=
  pairwiseCompatible_iff_hasCommonInterleaver_of_fourWay <|
    chudnovskySeymour_fourWay_of_pairDegreeSplit_via_nonnegShift
      (fs := fs) hrr hpos hsame hsucc

/-- Chudnovsky--Seymour `1 ↔ 3` corollary from the concrete slot-data
endpoints after the nonnegative-shift reduction. -/
theorem pairwiseCompatible_iff_hasCommonInterleaver_of_slotData_via_nonnegShift
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hsame : PosComboNoCommonSameDegreeSlotDataNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreeSlotDataNonnegStatement) :
    PairwiseCompatible fs ↔ HasCommonInterleaver fs :=
  pairwiseCompatible_iff_hasCommonInterleaver_of_fourWay <|
    chudnovskySeymour_fourWay_of_slotData_via_nonnegShift
      (fs := fs) hrr hpos hsame hsucc

/-- Chudnovsky--Seymour `1 ↔ 3` corollary from the root-crossing
formulations after the nonnegative-shift reduction. -/
theorem pairwiseCompatible_iff_hasCommonInterleaver_of_rootCrossing_via_nonnegShift
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hsame : PosComboNoCommonSameDegreeRootCrossingNonnegStatement)
    (hsplit : PosComboSuccDegreeLeftSplitsNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreeRootCrossingNonnegStatement) :
    PairwiseCompatible fs ↔ HasCommonInterleaver fs :=
  pairwiseCompatible_iff_hasCommonInterleaver_of_fourWay <|
    chudnovskySeymour_fourWay_of_rootCrossing_via_nonnegShift
      (fs := fs) hrr hpos hsame hsplit hsucc

/-- Chudnovsky--Seymour `1 ↔ 3` corollary from root-crossing formulations
alone.  Root continuity supplies the succ-degree left endpoint. -/
theorem pairwiseCompatible_iff_hasCommonInterleaver_of_rootCrossing
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hsame : PosComboNoCommonSameDegreeRootCrossingNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreeRootCrossingNonnegStatement) :
    PairwiseCompatible fs ↔ HasCommonInterleaver fs :=
  pairwiseCompatible_iff_hasCommonInterleaver_of_rootCrossing_via_nonnegShift
    hrr hpos hsame PosComboSuccDegreeLeftSplitsNonnegStatement_of_rootContinuity hsucc

/-- Chudnovsky--Seymour `1 ↔ 3` corollary from root-crossing formulations, with
the succ-degree left endpoint supplied by the PF/ASW route before shifting. -/
theorem pairwiseCompatible_iff_hasCommonInterleaver_of_rootCrossing_and_forward_asw
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hsame : PosComboNoCommonSameDegreeRootCrossingNonnegStatement)
    (hASW : aissenSchoenbergWhitneyForwardOrZeroStatement)
    (hsucc : PosComboNoCommonSuccDegreeRootCrossingNonnegStatement) :
    PairwiseCompatible fs ↔ HasCommonInterleaver fs :=
  pairwiseCompatible_iff_hasCommonInterleaver_of_fourWay <|
    chudnovskySeymour_fourWay_of_rootCrossing_and_forward_asw
      (fs := fs) hrr hpos hsame hASW hsucc

/-- Chudnovsky--Seymour `1 ↔ 3` corollary from root-crossing formulations, with
the succ-degree left endpoint supplied by the splitting-only ASW target before
shifting. -/
theorem pairwiseCompatible_iff_hasCommonInterleaver_of_rootCrossing_and_forward_asw_splits
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hsame : PosComboNoCommonSameDegreeRootCrossingNonnegStatement)
    (hASW : aissenSchoenbergWhitneyForwardSplitsStatement)
    (hsucc : PosComboNoCommonSuccDegreeRootCrossingNonnegStatement) :
    PairwiseCompatible fs ↔ HasCommonInterleaver fs :=
  pairwiseCompatible_iff_hasCommonInterleaver_of_rootCrossing_and_forward_asw
    (fs := fs) hrr hpos hsame
    (aissenSchoenbergWhitneyForwardOrZero_of_splits hASW) hsucc

/-- Chudnovsky--Seymour `1 ↔ 3` corollary from the nonnegative-coefficient
degree-split package, with the familywise nonnegativity assumption removed by
translation. -/
theorem pairwiseCompatible_iff_hasCommonInterleaver_of_degreeSplit_via_nonnegShift
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hsame : PosComboNoCommonSameDegreeOrientationAlternativeNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement) :
    PairwiseCompatible fs ↔ HasCommonInterleaver fs :=
  pairwiseCompatible_iff_hasCommonInterleaver_of_fourWay <|
    chudnovskySeymour_fourWay_of_degreeSplit_via_nonnegShift
      (fs := fs) hrr hpos hsame hsucc

/-- Chudnovsky--Seymour `1 ↔ 3` corollary after the nonnegative shift
reduction, with the succ-degree branch discharged by the affine-family bridge.
-/
theorem
    pairwiseCompatible_iff_hasCommonInterleaver_via_nonnegShift
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hsame : PosComboNoCommonSameDegreeOrientationAlternativeNonnegStatement)
    (haffBridge : PosComboNoCommonAffineFamilyStatement) :
    PairwiseCompatible fs ↔ HasCommonInterleaver fs :=
  pairwiseCompatible_iff_hasCommonInterleaver_of_fourWay <|
    chudnovskySeymour_fourWay_of_sameDegreeAlternative_and_affineFamily_via_nonnegShift
      (fs := fs) hrr hpos hsame haffBridge

/-- Chudnovsky--Seymour `1 ↔ 3` corollary from the stronger
boundary-right-pair statement after the nonnegative shift reduction. -/
theorem
    pairwiseCompatible_iff_hasCommonInterleaver_of_boundaryRightPairOrientation_via_nonnegShift
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hboundary : PosComboNoCommonBoundaryRightPairOrientationStatement) :
    PairwiseCompatible fs ↔ HasCommonInterleaver fs :=
  pairwiseCompatible_iff_hasCommonInterleaver_of_fourWay <|
    chudnovskySeymour_fourWay_of_boundaryRightPairOrientation_via_nonnegShift
      (fs := fs) hrr hpos hboundary

/-- Chudnovsky--Seymour `1 ↔ 4` corollary under the natural positive-leading
pair bridge: pairwise compatibility is equivalent to full family
compatibility. -/
theorem pairwiseCompatible_iff_familyCompatible_of_pairBridgePos
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (htwo : CompatiblePairHasCommonInterleaverStatement) :
    PairwiseCompatible fs ↔ FamilyCompatible fs :=
  pairwiseCompatible_iff_familyCompatible_of_commonInterleaver_forward hpos <|
    (pairwiseCompatible_iff_hasCommonInterleaver_of_pairBridgePos
      (fs := fs) hrr hpos htwo).1

/-- Chudnovsky--Seymour `1 ↔ 4` specialization from the honest same-degree /
succ-degree compatibility split. -/
theorem pairwiseCompatible_iff_familyCompatible_of_compatibleDegreeSplit
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hsame : CompatibleSameDegreePairHasCommonInterleaverStatement)
    (hsucc : CompatibleSuccDegreePairHasCommonInterleaverStatement) :
    PairwiseCompatible fs ↔ FamilyCompatible fs :=
  pairwiseCompatible_iff_familyCompatible_of_commonInterleaver_forward hpos <|
    (pairwiseCompatible_iff_hasCommonInterleaver_of_compatibleDegreeSplit
      (fs := fs) hrr hpos hsame hsucc).1

/-- Chudnovsky--Seymour `1 ↔ 4` specialization from the repaired shifted
nonnegative-coefficient degree split. -/
theorem pairwiseCompatible_iff_familyCompatible_of_pairDegreeSplit_via_nonnegShift
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hsame : PosComboNoCommonSameDegreePairHasCommonInterleaverNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement) :
    PairwiseCompatible fs ↔ FamilyCompatible fs :=
  pairwiseCompatible_iff_familyCompatible_of_commonInterleaver_forward hpos <|
    (pairwiseCompatible_iff_hasCommonInterleaver_of_pairDegreeSplit_via_nonnegShift
      (fs := fs) hrr hpos hsame hsucc).1

/-- Chudnovsky--Seymour `1 ↔ 4` specialization from the concrete slot-data
endpoints after the nonnegative-shift reduction. -/
theorem pairwiseCompatible_iff_familyCompatible_of_slotData_via_nonnegShift
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hsame : PosComboNoCommonSameDegreeSlotDataNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreeSlotDataNonnegStatement) :
    PairwiseCompatible fs ↔ FamilyCompatible fs :=
  pairwiseCompatible_iff_familyCompatible_of_commonInterleaver_forward hpos <|
    (pairwiseCompatible_iff_hasCommonInterleaver_of_slotData_via_nonnegShift
      (fs := fs) hrr hpos hsame hsucc).1

/-- Chudnovsky--Seymour `1 ↔ 4` specialization from the root-crossing
formulations after the nonnegative-shift reduction. -/
theorem pairwiseCompatible_iff_familyCompatible_of_rootCrossing_via_nonnegShift
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hsame : PosComboNoCommonSameDegreeRootCrossingNonnegStatement)
    (hsplit : PosComboSuccDegreeLeftSplitsNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreeRootCrossingNonnegStatement) :
    PairwiseCompatible fs ↔ FamilyCompatible fs :=
  pairwiseCompatible_iff_familyCompatible_of_commonInterleaver_forward hpos <|
    (pairwiseCompatible_iff_hasCommonInterleaver_of_rootCrossing_via_nonnegShift
      (fs := fs) hrr hpos hsame hsplit hsucc).1

/-- Chudnovsky--Seymour `1 ↔ 4` specialization from root-crossing formulations
alone.  Root continuity supplies the succ-degree left endpoint. -/
theorem pairwiseCompatible_iff_familyCompatible_of_rootCrossing
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hsame : PosComboNoCommonSameDegreeRootCrossingNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreeRootCrossingNonnegStatement) :
    PairwiseCompatible fs ↔ FamilyCompatible fs :=
  pairwiseCompatible_iff_familyCompatible_of_rootCrossing_via_nonnegShift
    hrr hpos hsame PosComboSuccDegreeLeftSplitsNonnegStatement_of_rootContinuity hsucc

/-- Chudnovsky--Seymour `1 ↔ 4` specialization from root-crossing formulations,
with the succ-degree left endpoint supplied by the PF/ASW route before shifting.
-/
theorem pairwiseCompatible_iff_familyCompatible_of_rootCrossing_and_forward_asw
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hsame : PosComboNoCommonSameDegreeRootCrossingNonnegStatement)
    (hASW : aissenSchoenbergWhitneyForwardOrZeroStatement)
    (hsucc : PosComboNoCommonSuccDegreeRootCrossingNonnegStatement) :
    PairwiseCompatible fs ↔ FamilyCompatible fs :=
  pairwiseCompatible_iff_familyCompatible_of_commonInterleaver_forward hpos <|
    (pairwiseCompatible_iff_hasCommonInterleaver_of_rootCrossing_and_forward_asw
      (fs := fs) hrr hpos hsame hASW hsucc).1

/-- Chudnovsky--Seymour `1 ↔ 4` specialization from root-crossing formulations,
with the succ-degree left endpoint supplied by the splitting-only ASW target
before shifting. -/
theorem pairwiseCompatible_iff_familyCompatible_of_rootCrossing_and_forward_asw_splits
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hsame : PosComboNoCommonSameDegreeRootCrossingNonnegStatement)
    (hASW : aissenSchoenbergWhitneyForwardSplitsStatement)
    (hsucc : PosComboNoCommonSuccDegreeRootCrossingNonnegStatement) :
    PairwiseCompatible fs ↔ FamilyCompatible fs :=
  pairwiseCompatible_iff_familyCompatible_of_rootCrossing_and_forward_asw
    (fs := fs) hrr hpos hsame
    (aissenSchoenbergWhitneyForwardOrZero_of_splits hASW) hsucc

/-- Chudnovsky--Seymour `1 ↔ 4` specialization from the nonnegative-coefficient
degree-split package, with the familywise nonnegativity assumption removed by
translation. -/
theorem pairwiseCompatible_iff_familyCompatible_of_degreeSplit_via_nonnegShift
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hsame : PosComboNoCommonSameDegreeOrientationAlternativeNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement) :
    PairwiseCompatible fs ↔ FamilyCompatible fs :=
  pairwiseCompatible_iff_familyCompatible_of_commonInterleaver_forward hpos <|
    (pairwiseCompatible_iff_hasCommonInterleaver_of_degreeSplit_via_nonnegShift
      (fs := fs) hrr hpos hsame hsucc).1

/-- Chudnovsky--Seymour `1 ↔ 4` specialization after the nonnegative shift
reduction, with the succ-degree branch discharged by the affine-family bridge.
-/
theorem
    pairwiseCompatible_iff_familyCompatible_via_nonnegShift
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hsame : PosComboNoCommonSameDegreeOrientationAlternativeNonnegStatement)
    (haffBridge : PosComboNoCommonAffineFamilyStatement) :
    PairwiseCompatible fs ↔ FamilyCompatible fs :=
  pairwiseCompatible_iff_familyCompatible_of_commonInterleaver_forward hpos <|
    (pairwiseCompatible_iff_hasCommonInterleaver_via_nonnegShift
      (fs := fs) hrr hpos hsame haffBridge).1

/-- Chudnovsky--Seymour `1 ↔ 4` specialization from the stronger
boundary-right-pair statement after the nonnegative shift reduction. -/
theorem pairwiseCompatible_iff_familyCompatible_of_boundaryRightPairOrientation_via_nonnegShift
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hboundary : PosComboNoCommonBoundaryRightPairOrientationStatement) :
    PairwiseCompatible fs ↔ FamilyCompatible fs :=
  pairwiseCompatible_iff_familyCompatible_of_commonInterleaver_forward hpos <|
    (pairwiseCompatible_iff_hasCommonInterleaver_of_boundaryRightPairOrientation_via_nonnegShift
      (fs := fs) hrr hpos hboundary).1

/-- Nonnegative-coefficient specialization of Chudnovsky--Seymour `1 ↔ 3`
from a direct nonnegative pair bridge. -/
private theorem pairwiseCompatible_iff_hasCommonInterleaver_of_nonnegPairBridge
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hnn : ∀ f ∈ fs, HasNonnegCoeffs f)
    (hbridge :
      ∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        Compatible f g →
        ∃ h : ℝ[X], Prec f h ∧ Prec g h) :
    PairwiseCompatible fs ↔ HasCommonInterleaver fs :=
  pairwiseCompatible_iff_hasCommonInterleaver_of_fourWay <|
    chudnovskySeymour_fourWay_of_nonnegPairBridge hrr hpos hnn hbridge

/-- Nonnegative-coefficient specialization of Chudnovsky--Seymour `1 ↔ 3`
from the no-common orientation core. -/
theorem pairwiseCompatible_iff_hasCommonInterleaver_of_noCommonOrientation_and_nonnegCoeffs
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hnn : ∀ f ∈ fs, HasNonnegCoeffs f)
    (hstep : PosComboNoCommonOrientationStatement) :
    PairwiseCompatible fs ↔ HasCommonInterleaver fs :=
  pairwiseCompatible_iff_hasCommonInterleaver_of_nonnegPairBridge hrr hpos hnn
    (nonnegPairBridge_of_noCommonOrientation hstep)

/-- Nonnegative-coefficient specialization of Chudnovsky--Seymour `1 ↔ 3`
from the repaired degree-split package. -/
theorem pairwiseCompatible_iff_hasCommonInterleaver_of_pairDegreeSplit_and_nonnegCoeffs
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hnn : ∀ f ∈ fs, HasNonnegCoeffs f)
    (hsame : PosComboNoCommonSameDegreePairHasCommonInterleaverNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement) :
    PairwiseCompatible fs ↔ HasCommonInterleaver fs :=
  pairwiseCompatible_iff_hasCommonInterleaver_of_nonnegPairBridge hrr hpos hnn
    (nonnegPairBridge_of_pairDegreeSplit hsame hsucc)

/-- Nonnegative-coefficient specialization of Chudnovsky--Seymour `1 ↔ 3`
from the honest degree-split package. -/
theorem pairwiseCompatible_iff_hasCommonInterleaver_of_degreeSplit_and_nonnegCoeffs
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hnn : ∀ f ∈ fs, HasNonnegCoeffs f)
    (hsame : PosComboNoCommonSameDegreeOrientationAlternativeNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement) :
    PairwiseCompatible fs ↔ HasCommonInterleaver fs :=
  pairwiseCompatible_iff_hasCommonInterleaver_of_pairDegreeSplit_and_nonnegCoeffs
    (fs := fs) hrr hpos hnn
    (posComboNoCommonSameDegreePairHasCommonInterleaver_of_orientationAlternative_nonneg hsame)
    hsucc

/-- Nonnegative-coefficient specialization of Chudnovsky--Seymour `1 ↔ 3`,
using the repaired same-degree branch and the affine-family bridge for the
succ-degree branch. -/
theorem pairwiseCompatible_iff_hasCommonInterleaver_of_sameDegreePair_and_affineFamily_nonneg
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hnn : ∀ f ∈ fs, HasNonnegCoeffs f)
    (hsame : PosComboNoCommonSameDegreePairHasCommonInterleaverNonnegStatement)
    (haffBridge : PosComboNoCommonAffineFamilyStatement) :
    PairwiseCompatible fs ↔ HasCommonInterleaver fs :=
  pairwiseCompatible_iff_hasCommonInterleaver_of_pairDegreeSplit_and_nonnegCoeffs
    (fs := fs) hrr hpos hnn hsame
    (posComboNoCommonSuccDegreePairHasCommonInterleaver_of_affineFamily haffBridge)

/-- Nonnegative-coefficient specialization of Chudnovsky--Seymour `1 ↔ 3`
from the all-combinations bridge. -/
theorem pairwiseCompatible_iff_hasCommonInterleaver_of_allComboBridge_and_nonnegCoeffs
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hnn : ∀ f ∈ fs, HasNonnegCoeffs f)
    (hallBridge : PosComboNoCommonToAllComboBridgeStatement) :
    PairwiseCompatible fs ↔ HasCommonInterleaver fs :=
  pairwiseCompatible_iff_hasCommonInterleaver_of_noCommonOrientation_and_nonnegCoeffs
    (fs := fs) hrr hpos hnn
    (posComboNoCommonOrientation_of_allComboBridge hallBridge)

/-- Nonnegative-coefficient specialization of Chudnovsky--Seymour `1 ↔ 3`
from the affine-family bridge. -/
theorem pairwiseCompatible_iff_hasCommonInterleaver_of_affineFamilyBridge_and_nonnegCoeffs
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hnn : ∀ f ∈ fs, HasNonnegCoeffs f)
    (haffBridge : PosComboNoCommonAffineFamilyStatement) :
    PairwiseCompatible fs ↔ HasCommonInterleaver fs :=
  pairwiseCompatible_iff_hasCommonInterleaver_of_nonnegPairBridge hrr hpos hnn
    (nonnegPairBridge_of_affineFamilyBridge haffBridge)

/-- Nonnegative-coefficient specialization of Chudnovsky--Seymour `1 ↔ 3`
from the boundary-right-pair orientation statement. -/
theorem pairwiseCompatible_iff_hasCommonInterleaver_of_boundaryRightPairOrientation_and_nonnegCoeffs
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hnn : ∀ f ∈ fs, HasNonnegCoeffs f)
    (hboundary : PosComboNoCommonBoundaryRightPairOrientationStatement) :
    PairwiseCompatible fs ↔ HasCommonInterleaver fs :=
  pairwiseCompatible_iff_hasCommonInterleaver_of_affineFamilyBridge_and_nonnegCoeffs
    (fs := fs) hrr hpos hnn
    (posComboNoCommonAffineFamily_of_boundaryRightPairOrientation hboundary)

/-- Nonnegative-coefficient specialization of Chudnovsky--Seymour `1 ↔ 4`
from the no-common orientation core. -/
theorem pairwiseCompatible_iff_familyCompatible_of_noCommonOrientation_and_nonnegCoeffs
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hnn : ∀ f ∈ fs, HasNonnegCoeffs f)
    (hstep : PosComboNoCommonOrientationStatement) :
    PairwiseCompatible fs ↔ FamilyCompatible fs :=
  pairwiseCompatible_iff_familyCompatible_of_commonInterleaver_forward hpos <|
    (pairwiseCompatible_iff_hasCommonInterleaver_of_noCommonOrientation_and_nonnegCoeffs
      (fs := fs) hrr hpos hnn hstep).1

/-- Nonnegative-coefficient specialization of Chudnovsky--Seymour `1 ↔ 4`
from the repaired degree-split package. -/
theorem pairwiseCompatible_iff_familyCompatible_of_pairDegreeSplit_and_nonnegCoeffs
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hnn : ∀ f ∈ fs, HasNonnegCoeffs f)
    (hsame : PosComboNoCommonSameDegreePairHasCommonInterleaverNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement) :
    PairwiseCompatible fs ↔ FamilyCompatible fs :=
  pairwiseCompatible_iff_familyCompatible_of_commonInterleaver_forward hpos <|
    (pairwiseCompatible_iff_hasCommonInterleaver_of_pairDegreeSplit_and_nonnegCoeffs
      (fs := fs) hrr hpos hnn hsame hsucc).1

/-- Nonnegative-coefficient specialization of Chudnovsky--Seymour `1 ↔ 4`
from the honest degree-split package. -/
theorem pairwiseCompatible_iff_familyCompatible_of_degreeSplit_and_nonnegCoeffs
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hnn : ∀ f ∈ fs, HasNonnegCoeffs f)
    (hsame : PosComboNoCommonSameDegreeOrientationAlternativeNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement) :
    PairwiseCompatible fs ↔ FamilyCompatible fs :=
  pairwiseCompatible_iff_familyCompatible_of_commonInterleaver_forward hpos <|
    (pairwiseCompatible_iff_hasCommonInterleaver_of_degreeSplit_and_nonnegCoeffs
      (fs := fs) hrr hpos hnn hsame hsucc).1

/-- Nonnegative-coefficient specialization of Chudnovsky--Seymour `1 ↔ 4`,
using the repaired same-degree branch and the affine-family bridge for the
succ-degree branch. -/
theorem pairwiseCompatible_iff_familyCompatible_of_sameDegreePair_and_affineFamily_nonneg
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hnn : ∀ f ∈ fs, HasNonnegCoeffs f)
    (hsame : PosComboNoCommonSameDegreePairHasCommonInterleaverNonnegStatement)
    (haffBridge : PosComboNoCommonAffineFamilyStatement) :
    PairwiseCompatible fs ↔ FamilyCompatible fs :=
  pairwiseCompatible_iff_familyCompatible_of_commonInterleaver_forward hpos <|
    (pairwiseCompatible_iff_hasCommonInterleaver_of_sameDegreePair_and_affineFamily_nonneg
      (fs := fs) hrr hpos hnn hsame haffBridge).1

/-- Nonnegative-coefficient specialization of Chudnovsky--Seymour `1 ↔ 4`
from the all-combinations bridge. -/
theorem pairwiseCompatible_iff_familyCompatible_of_allComboBridge_and_nonnegCoeffs
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hnn : ∀ f ∈ fs, HasNonnegCoeffs f)
    (hallBridge : PosComboNoCommonToAllComboBridgeStatement) :
    PairwiseCompatible fs ↔ FamilyCompatible fs :=
  pairwiseCompatible_iff_familyCompatible_of_commonInterleaver_forward hpos <|
    (pairwiseCompatible_iff_hasCommonInterleaver_of_allComboBridge_and_nonnegCoeffs
      (fs := fs) hrr hpos hnn hallBridge).1

/-- Nonnegative-coefficient specialization of Chudnovsky--Seymour `1 ↔ 4`
from the affine-family bridge. -/
theorem pairwiseCompatible_iff_familyCompatible_of_affineFamilyBridge_and_nonnegCoeffs
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hnn : ∀ f ∈ fs, HasNonnegCoeffs f)
    (haffBridge : PosComboNoCommonAffineFamilyStatement) :
    PairwiseCompatible fs ↔ FamilyCompatible fs :=
  pairwiseCompatible_iff_familyCompatible_of_commonInterleaver_forward hpos <|
    (pairwiseCompatible_iff_hasCommonInterleaver_of_affineFamilyBridge_and_nonnegCoeffs
      (fs := fs) hrr hpos hnn haffBridge).1

/-- Nonnegative-coefficient specialization of Chudnovsky--Seymour `1 ↔ 4`
from the boundary-right-pair orientation statement. -/
theorem pairwiseCompatible_iff_familyCompatible_of_boundaryRightPairOrientation_and_nonnegCoeffs
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hnn : ∀ f ∈ fs, HasNonnegCoeffs f)
    (hboundary : PosComboNoCommonBoundaryRightPairOrientationStatement) :
    PairwiseCompatible fs ↔ FamilyCompatible fs :=
  pairwiseCompatible_iff_familyCompatible_of_commonInterleaver_forward hpos <|
    (pairwiseCompatible_iff_hasCommonInterleaver_of_boundaryRightPairOrientation_and_nonnegCoeffs
      (fs := fs) hrr hpos hnn hboundary).1

/-- In the degree-`≤ 1` regime, every pair already has a common right
interleaver. This is the fully packaged two-polynomial input for the
Chudnovsky--Seymour chain in the linear/constant endpoint. -/
theorem pairwiseHasCommonInterleaver_of_natDegree_le_one
    {fs : List ℝ[X]}
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hdeg : ∀ f ∈ fs, f.natDegree ≤ 1) :
    PairwiseHasCommonInterleaver fs :=
  fun i j _ =>
    pairHasCommonInterleaver_of_natDegree_le_one
      (hpos (fs.get i) (List.get_mem _ _))
      (hpos (fs.get j) (List.get_mem _ _))
      (hdeg (fs.get i) (List.get_mem _ _))
      (hdeg (fs.get j) (List.get_mem _ _))

/-- In the degree-`≤ 2` regime, pairwise compatibility gives pairwise common
right interleavers. -/
theorem pairwiseHasCommonInterleaver_of_pairwiseCompatible_of_natDegree_le_two
    {fs : List ℝ[X]}
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hdeg : ∀ f ∈ fs, f.natDegree ≤ 2)
    (hpair : PairwiseCompatible fs) :
    PairwiseHasCommonInterleaver fs :=
  fun i j hij =>
    compatiblePairHasCommonInterleaver_of_natDegree_le_two
      (hpos (fs.get i) (List.get_mem _ _))
      (hpos (fs.get j) (List.get_mem _ _))
      (hpair i j hij)
      (hdeg (fs.get i) (List.get_mem _ _))
      (hdeg (fs.get j) (List.get_mem _ _))

/-- Pairwise low-degree common-left interleavers for positive-leading
linear/constant families. -/
theorem pairwiseHasCommonLeftInterleaver_of_natDegree_le_one
    {fs : List ℝ[X]}
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hdeg : ∀ f ∈ fs, f.natDegree ≤ 1) :
    PairwiseHasCommonLeftInterleaver fs :=
  fun i j _ =>
    pairHasCommonLeftInterleaver_of_natDegree_le_one
      (hpos (fs.get i) (List.get_mem _ _))
      (hpos (fs.get j) (List.get_mem _ _))
      (hdeg (fs.get i) (List.get_mem _ _))
      (hdeg (fs.get j) (List.get_mem _ _))

/-- Positive-leading degree-`≤ 1` families are nonzero and split memberwise. -/
theorem family_ne_zero_and_splits_of_natDegree_le_one
    {fs : List ℝ[X]}
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hdeg : ∀ f ∈ fs, f.natDegree ≤ 1) :
    ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits) :=
  fun f hf =>
    isRealRooted_of_natDegree_le_one
      ((hpos f hf).ne_zero) (hdeg f hf)

/-- Therefore any finite positive-leading family of degree at most one already
has a global common right interleaver. -/
theorem hasCommonInterleaver_of_natDegree_le_one
    {fs : List ℝ[X]}
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hdeg : ∀ f ∈ fs, f.natDegree ≤ 1) :
    HasCommonInterleaver fs := by
  let hrr := family_ne_zero_and_splits_of_natDegree_le_one hpos hdeg
  exact
    commonInterleaverFamilyUpgrade
      (fun f hf => (hrr f hf).2) hpos (pairwiseHasCommonInterleaver_of_natDegree_le_one hpos hdeg)

/-- Positive-leading degree-`≤ 1` families already have a global common left
interleaver. -/
theorem hasCommonLeftInterleaver_of_natDegree_le_one
    {fs : List ℝ[X]}
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hdeg : ∀ f ∈ fs, f.natDegree ≤ 1) :
    HasCommonLeftInterleaver fs := by
  let hrr := family_ne_zero_and_splits_of_natDegree_le_one hpos hdeg
  exact
    commonLeftInterleaverFamilyUpgrade
      (fun f hf => (hrr f hf).2) hpos
      (pairwiseHasCommonLeftInterleaver_of_natDegree_le_one hpos hdeg)

/-- Low-degree Chudnovsky--Seymour package: if every member of the family has
degree at most one and positive leading coefficient, then all four standard
compatibility/common-interleaver formulations collapse without any additional
bridge hypothesis. -/
theorem chudnovskySeymour_fourWay_of_natDegree_le_one
    {fs : List ℝ[X]}
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hdeg : ∀ f ∈ fs, f.natDegree ≤ 1) :
    ChudnovskySeymourFourWayPackage fs := by
  exact
    chudnovskySeymour_fourWay_of_pairwiseCommonForward
      (family_ne_zero_and_splits_of_natDegree_le_one hpos hdeg) hpos <|
      fun _ => pairwiseHasCommonInterleaver_of_natDegree_le_one hpos hdeg

/-- Degree-`≤ 2` Chudnovsky--Seymour package under the standard memberwise
real-rootedness hypothesis.  The new ingredient is the checked two-polynomial
degree-`≤ 2` bridge from pairwise compatibility to pairwise common right
interleavers. -/
theorem chudnovskySeymour_fourWay_of_natDegree_le_two
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hdeg : ∀ f ∈ fs, f.natDegree ≤ 2) :
    ChudnovskySeymourFourWayPackage fs :=
  chudnovskySeymour_fourWay_of_pairwiseCommonForward hrr hpos <|
    pairwiseHasCommonInterleaver_of_pairwiseCompatible_of_natDegree_le_two hpos hdeg

/-- Degree-`≤ 1` specialization of Chudnovsky--Seymour `1 ↔ 2`: for
positive-leading linear/constant families, pairwise compatibility is already
equivalent to pairwise common-interleaver data. -/
theorem pairwiseCompatible_iff_pairwiseHasCommonInterleaver_of_natDegree_le_one
    {fs : List ℝ[X]}
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hdeg : ∀ f ∈ fs, f.natDegree ≤ 1) :
    PairwiseCompatible fs ↔ PairwiseHasCommonInterleaver fs :=
  pairwiseCompatible_iff_pairwiseHasCommonInterleaver_of_fourWay <|
    chudnovskySeymour_fourWay_of_natDegree_le_one
      (fs := fs) hpos hdeg

/-- Degree-`≤ 2` specialization of Chudnovsky--Seymour `1 ↔ 2`: pairwise
compatibility is equivalent to pairwise common-interleaver data. -/
theorem pairwiseCompatible_iff_pairwiseHasCommonInterleaver_of_natDegree_le_two
    {fs : List ℝ[X]}
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hdeg : ∀ f ∈ fs, f.natDegree ≤ 2) :
    PairwiseCompatible fs ↔ PairwiseHasCommonInterleaver fs :=
  ⟨pairwiseHasCommonInterleaver_of_pairwiseCompatible_of_natDegree_le_two hpos hdeg,
    fun hpair => pairwiseCompatible_of_pairwiseHasCommonInterleaver hpair hpos⟩

/-- Degree-`≤ 1` specialization of Chudnovsky--Seymour `2 ↔ 3`: for
positive-leading linear/constant families, pairwise common-interleaver data is
already equivalent to a global common interleaver. -/
theorem pairwiseHasCommonInterleaver_iff_hasCommonInterleaver_of_natDegree_le_one
    {fs : List ℝ[X]}
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hdeg : ∀ f ∈ fs, f.natDegree ≤ 1) :
    PairwiseHasCommonInterleaver fs ↔ HasCommonInterleaver fs :=
  pairwiseHasCommonInterleaver_iff_hasCommonInterleaver_of_fourWay <|
    chudnovskySeymour_fourWay_of_natDegree_le_one
      (fs := fs) hpos hdeg

/-- Degree-`≤ 2` specialization of Chudnovsky--Seymour `2 ↔ 3` under
memberwise real-rootedness. -/
theorem pairwiseHasCommonInterleaver_iff_hasCommonInterleaver_of_natDegree_le_two
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hdeg : ∀ f ∈ fs, f.natDegree ≤ 2) :
    PairwiseHasCommonInterleaver fs ↔ HasCommonInterleaver fs :=
  pairwiseHasCommonInterleaver_iff_hasCommonInterleaver_of_fourWay <|
    chudnovskySeymour_fourWay_of_natDegree_le_two
      (fs := fs) hrr hpos hdeg

/-- Degree-`≤ 1` specialization of Chudnovsky--Seymour `3 ↔ 4`: for
positive-leading linear/constant families, a global common interleaver is
already equivalent to full family compatibility. -/
theorem hasCommonInterleaver_iff_familyCompatible_of_natDegree_le_one
    {fs : List ℝ[X]}
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hdeg : ∀ f ∈ fs, f.natDegree ≤ 1) :
    HasCommonInterleaver fs ↔ FamilyCompatible fs :=
  hasCommonInterleaver_iff_familyCompatible_of_fourWay <|
    chudnovskySeymour_fourWay_of_natDegree_le_one
      (fs := fs) hpos hdeg

/-- Degree-`≤ 2` specialization of Chudnovsky--Seymour `3 ↔ 4` under
memberwise real-rootedness. -/
theorem hasCommonInterleaver_iff_familyCompatible_of_natDegree_le_two
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hdeg : ∀ f ∈ fs, f.natDegree ≤ 2) :
    HasCommonInterleaver fs ↔ FamilyCompatible fs :=
  hasCommonInterleaver_iff_familyCompatible_of_fourWay <|
    chudnovskySeymour_fourWay_of_natDegree_le_two
      (fs := fs) hrr hpos hdeg

/-- Degree-`≤ 1` specialization of Chudnovsky--Seymour `1 ↔ 3`: for
positive-leading linear/constant families, pairwise compatibility is already
equivalent to having a common right interleaver. -/
theorem pairwiseCompatible_iff_hasCommonInterleaver_of_natDegree_le_one
    {fs : List ℝ[X]}
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hdeg : ∀ f ∈ fs, f.natDegree ≤ 1) :
    PairwiseCompatible fs ↔ HasCommonInterleaver fs :=
  pairwiseCompatible_iff_hasCommonInterleaver_of_fourWay <|
    chudnovskySeymour_fourWay_of_natDegree_le_one
      (fs := fs) hpos hdeg

/-- Degree-`≤ 2` specialization of Chudnovsky--Seymour `1 ↔ 3` under
memberwise real-rootedness. -/
theorem pairwiseCompatible_iff_hasCommonInterleaver_of_natDegree_le_two
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hdeg : ∀ f ∈ fs, f.natDegree ≤ 2) :
    PairwiseCompatible fs ↔ HasCommonInterleaver fs :=
  pairwiseCompatible_iff_hasCommonInterleaver_of_fourWay <|
    chudnovskySeymour_fourWay_of_natDegree_le_two
      (fs := fs) hrr hpos hdeg

/-- Degree-`≤ 1` specialization of Chudnovsky--Seymour `1 ↔ 3`, left-oriented:
for positive-leading linear/constant families, pairwise compatibility is
already equivalent to having a common left interleaver. -/
theorem pairwiseCompatible_iff_commonLeftInterleaver_of_natDegree_le_one
    {fs : List ℝ[X]}
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hdeg : ∀ f ∈ fs, f.natDegree ≤ 1) :
    PairwiseCompatible fs ↔ HasCommonLeftInterleaver fs :=
  ⟨fun _ => hasCommonLeftInterleaver_of_natDegree_le_one hpos hdeg,
    fun hcommon => pairwiseCompatible_of_commonLeftInterleaver hcommon hpos⟩

/-- Degree-`≤ 1` specialization of Chudnovsky--Seymour `1 ↔ 4`: for
positive-leading linear/constant families, pairwise compatibility is already
equivalent to full family compatibility. -/
theorem pairwiseCompatible_iff_familyCompatible_of_natDegree_le_one
    {fs : List ℝ[X]}
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hdeg : ∀ f ∈ fs, f.natDegree ≤ 1) :
    PairwiseCompatible fs ↔ FamilyCompatible fs :=
  pairwiseCompatible_iff_familyCompatible_of_commonInterleaver_forward hpos <|
    (pairwiseCompatible_iff_hasCommonInterleaver_of_natDegree_le_one
      (fs := fs) hpos hdeg).1

/-- Degree-`≤ 2` specialization of Chudnovsky--Seymour `1 ↔ 4` under
memberwise real-rootedness. -/
theorem pairwiseCompatible_iff_familyCompatible_of_natDegree_le_two
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hdeg : ∀ f ∈ fs, f.natDegree ≤ 2) :
    PairwiseCompatible fs ↔ FamilyCompatible fs :=
  pairwiseCompatible_iff_familyCompatible_of_commonInterleaver_forward hpos <|
    (pairwiseCompatible_iff_hasCommonInterleaver_of_natDegree_le_two
      (fs := fs) hrr hpos hdeg).1

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
