/-
# Low-degree endpoints for two-polynomial common interleavers

This module contains the low-degree endpoint material extracted from
`CommonInterleaverTwo`: degree `<= 1` pair endpoints, the quadratic/cubic
succ-degree obstruction leaves, and the degree zero/one/two root-count bases.
-/
import RealRooted.CommonInterleaver.RightPencil
import RealRooted.CommonInterleaver.RootCountCombinatorics
import RealRooted.CommonInterleaver.SameDegreeRootCount
import RealRooted.CommonInterleaver.SuccDegreeEndpoint
import RealRooted.SameDegreeCubicRootCount
import RealRooted.SameDegreeQuadraticRootCount
import RealRooted.SuccDegreeLeftEndpoint
import RealRooted.SuccDegreeRootCrossing

open Polynomial

noncomputable section

namespace RealRooted

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
    (∀ ⦃f g : ℝ[X]⦄,
    HasPosLeadingCoeff f →
    HasPosLeadingCoeff g →
    HasNonnegCoeffs f →
    HasNonnegCoeffs g →
    PosComboRealRooted f g →
    g.natDegree = f.natDegree →
    (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
    ∃ h : ℝ[X], Prec f h ∧ Prec g h) := by
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
end RealRooted
