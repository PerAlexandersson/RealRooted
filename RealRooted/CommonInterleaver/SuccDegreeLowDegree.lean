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
theorem strictInterl_or_reverse_of_natDegree_le_one
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hf_deg_le_one : f.natDegree ≤ 1)
    (hg_deg_le_one : g.natDegree ≤ 1) :
    StrictInterl f g ∨ StrictInterl g f := by
  have hf0 : f ≠ 0 := hf_pos.ne_zero
  have hg0 : g ≠ 0 := hg_pos.ne_zero
  by_cases hf_deg0 : f.natDegree = 0
  · have hf_rr : (f ≠ 0 ∧ f.Splits) := isRealRooted_of_deg_zero hf0 hf_deg0
    by_cases hg_deg0 : g.natDegree = 0
    · have hg_rr : (g ≠ 0 ∧ g.Splits) := isRealRooted_of_deg_zero hg0 hg_deg0
      exact Or.inl (StrictInterl.of_degree_zero_degree_zero
        hf_rr.1 hf_rr.2 hg_rr.1 hg_rr.2 hf_deg0 hg_deg0)
    · have hg_deg1 : g.natDegree = 1 := by lia
      have hg_rr : (g ≠ 0 ∧ g.Splits) := isRealRooted_of_degree_one hg_deg1
      exact Or.inl (StrictInterl.of_degree_zero_right_of_degree_one
        hf_rr.1 hf_rr.2 hg_rr.1 hg_rr.2
        hf_deg0 hg_deg1)
  · have hf_deg1 : f.natDegree = 1 := by lia
    by_cases hg_deg0 : g.natDegree = 0
    · have hg_rr : (g ≠ 0 ∧ g.Splits) := isRealRooted_of_deg_zero hg0 hg_deg0
      have hf_rr : (f ≠ 0 ∧ f.Splits) := isRealRooted_of_degree_one hf_deg1
      exact Or.inr (StrictInterl.of_degree_zero_right_of_degree_one
        hg_rr.1 hg_rr.2 hf_rr.1 hf_rr.2
        hg_deg0 hf_deg1)
    · have hg_deg1 : g.natDegree = 1 := by lia
      exact PosComboRealRooted.strictInterl_or_reverse_of_same_degree_one (by lia) hf_deg1

@[deprecated strictInterl_or_reverse_of_natDegree_le_one (since := "2026-09-18")]
alias prec_or_revPrec_of_natDegree_le_one :=
  strictInterl_or_reverse_of_natDegree_le_one

/-- A symmetric `StrictInterl` orientation implies all real linear combinations are
real-rooted, after commuting the pair in the reversed case. -/
theorem allComboRealRooted_of_strictInterl_or_reverse
    {f g : ℝ[X]} :
    StrictInterl f g ∨ StrictInterl g f →
    AllComboRealRooted f g
  | Or.inl hstrictInterl => allComboRealRooted_of_strictInterl hstrictInterl
  | Or.inr hstrictInterl =>
      allComboRealRooted_comm (allComboRealRooted_of_strictInterl hstrictInterl)

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

/-- A `StrictInterl` relation implies Chudnovsky--Seymour nonnegative compatibility. -/
lemma of_strictInterl {f g : ℝ[X]} (h : StrictInterl f g) :
    Compatible f g :=
  of_allComboRealRooted (allComboRealRooted_of_strictInterl h)

@[deprecated of_strictInterl (since := "2026-09-18")]
alias of_prec := of_strictInterl

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
  allComboRealRooted_of_strictInterl_or_reverse <|
    strictInterl_or_reverse_of_natDegree_le_one
      hf_pos hg_pos hf_deg_le_one hg_deg_le_one

/-- A `StrictInterl` relation immediately gives a common right interleaver: use the
right endpoint as the witness. -/
theorem pairHasCommonInterleaver_of_strictInterl
    {f g : ℝ[X]} (hstrictInterl : StrictInterl f g) :
    ∃ h : ℝ[X], StrictInterl f h ∧ StrictInterl g h :=
  ⟨g, hstrictInterl, StrictInterl.refl hstrictInterl.2.1.1 hstrictInterl.2.1.2⟩

/-- A reversed `StrictInterl` relation immediately gives a common right interleaver:
use the left endpoint as the witness. -/
theorem pairHasCommonInterleaver_of_reverseStrictInterl
    {f g : ℝ[X]} (hstrictInterl : StrictInterl g f) :
    ∃ h : ℝ[X], StrictInterl f h ∧ StrictInterl g h :=
  ⟨f, StrictInterl.refl hstrictInterl.2.1.1 hstrictInterl.2.1.2, hstrictInterl⟩

/-- A symmetric `StrictInterl` orientation immediately gives a common right
interleaver: use the larger polynomial in the chosen orientation as the
witness. -/
theorem pairHasCommonInterleaver_of_strictInterl_or_reverse
    {f g : ℝ[X]} :
    StrictInterl f g ∨ StrictInterl g f →
    ∃ h : ℝ[X], StrictInterl f h ∧ StrictInterl g h
  | Or.inl hstrictInterl => pairHasCommonInterleaver_of_strictInterl hstrictInterl
  | Or.inr hstrictInterl => pairHasCommonInterleaver_of_reverseStrictInterl hstrictInterl

/-- A `StrictInterl` relation immediately gives a common left interleaver: use the
left endpoint as the witness. -/
theorem pairHasCommonLeftInterleaver_of_strictInterl
    {f g : ℝ[X]} (hstrictInterl : StrictInterl f g) :
    ∃ h : ℝ[X], StrictInterl h f ∧ StrictInterl h g :=
  ⟨f, StrictInterl.refl hstrictInterl.1.1 hstrictInterl.1.2, hstrictInterl⟩

/-- A reversed `StrictInterl` relation immediately gives a common left interleaver:
use the right endpoint as the witness. -/
theorem pairHasCommonLeftInterleaver_of_reverseStrictInterl
    {f g : ℝ[X]} (hstrictInterl : StrictInterl g f) :
    ∃ h : ℝ[X], StrictInterl h f ∧ StrictInterl h g :=
  ⟨g, hstrictInterl, StrictInterl.refl hstrictInterl.1.1 hstrictInterl.1.2⟩

/-- A symmetric `StrictInterl` orientation immediately gives a common left interleaver:
use the smaller polynomial in the chosen orientation as the witness. -/
theorem pairHasCommonLeftInterleaver_of_strictInterl_or_reverse
    {f g : ℝ[X]} :
    StrictInterl f g ∨ StrictInterl g f →
    ∃ h : ℝ[X], StrictInterl h f ∧ StrictInterl h g
  | Or.inl hstrictInterl => pairHasCommonLeftInterleaver_of_strictInterl hstrictInterl
  | Or.inr hstrictInterl => pairHasCommonLeftInterleaver_of_reverseStrictInterl hstrictInterl

/-- Two-polynomial common-interleaver endpoint in degree at most one. This is
the direct pair version used by the low-degree Chudnovsky--Seymour package. -/
theorem pairHasCommonInterleaver_of_natDegree_le_one
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hf_deg_le_one : f.natDegree ≤ 1)
    (hg_deg_le_one : g.natDegree ≤ 1) :
    ∃ h : ℝ[X], StrictInterl f h ∧ StrictInterl g h :=
  pairHasCommonInterleaver_of_strictInterl_or_reverse <|
    strictInterl_or_reverse_of_natDegree_le_one
      hf_pos hg_pos hf_deg_le_one hg_deg_le_one

/-- Two-polynomial common-left-interleaver endpoint in degree at most one. -/
theorem pairHasCommonLeftInterleaver_of_natDegree_le_one
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hf_deg_le_one : f.natDegree ≤ 1)
    (hg_deg_le_one : g.natDegree ≤ 1) :
    ∃ h : ℝ[X], StrictInterl h f ∧ StrictInterl h g :=
  pairHasCommonLeftInterleaver_of_strictInterl_or_reverse <|
    strictInterl_or_reverse_of_natDegree_le_one
      hf_pos hg_pos hf_deg_le_one hg_deg_le_one

/-- Same-degree specialization of the low-degree pair endpoint. -/
theorem pairHasCommonInterleaver_of_sameDegree_natDegree_le_one
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hdeg : g.natDegree = f.natDegree)
    (hf_deg_le_one : f.natDegree ≤ 1) :
    ∃ h : ℝ[X], StrictInterl f h ∧ StrictInterl g h :=
  pairHasCommonInterleaver_of_natDegree_le_one
    hf_pos hg_pos hf_deg_le_one (by lia)

/-- Same-degree specialization of the low-degree common-left pair endpoint. -/
theorem pairHasCommonLeftInterleaver_of_sameDegree_natDegree_le_one
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hdeg : g.natDegree = f.natDegree)
    (hf_deg_le_one : f.natDegree ≤ 1) :
    ∃ h : ℝ[X], StrictInterl h f ∧ StrictInterl h g :=
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
    ∃ h : ℝ[X], StrictInterl f h ∧ StrictInterl g h :=
  pairHasCommonInterleaver_of_natDegree_le_one
    hf_pos hg_pos hf_deg_le_one hg_deg_le_one

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
    rcases hsame hf_pos hg_pos hfnn hgnn hfg hdeg hno with hstrictInterl | hstrictInterl
    · intro j hj
      exact
        rootSlotInterval_inter_nonempty_of_commonInterleaver hstrictInterl
          (StrictInterl.refl hstrictInterl.2.1.1 hstrictInterl.2.1.2) j
          (by lia)
          (by lia)
    · intro j hj
      exact
        rootSlotInterval_inter_nonempty_of_commonInterleaver
          (StrictInterl.refl hstrictInterl.2.1.1 hstrictInterl.2.1.2) hstrictInterl
          j
          (by lia)
          (by lia)
  exact
    pairHasCommonInterleaver_of_sameDegree_slotIntersections
      hf_rr.1 hg_rr.1 hf_rr.2 hg_rr.2 hdeg hslot

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
  have hright : StrictInterl g (X * f) :=
    strictInterl_right_pair_of_affine_family_nonneg
      hf0 hg0 hfnn hgnn haff
  exact pairHasCommonInterleaver_of_strictInterl_right_pair_nonneg hright hfnn


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
  have hfcard : ((f.roots.filter (· ≤ x)).card : ℤ) = 0 := by exact_mod_cast hfcard_nat
  have hgcard : ((g.roots.filter (· ≤ x)).card : ℤ) ≤ 1 := by exact_mod_cast hgcard_nat
  have hgnonneg : (0 : ℤ) ≤ (g.roots.filter (· ≤ x)).card := by
    exact_mod_cast Nat.zero_le (g.roots.filter (· ≤ x)).card
  constructor <;> lia

/-- Degree-zero base case for the upper-threshold succ-degree root-count
formulation. -/
theorem succDegreeRootCountAbove_of_natDegree_eq_zero
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hdeg : g.natDegree = f.natDegree + 1) (hfdeg : f.natDegree = 0) (x : ℝ) :
      ((f.roots.filter (x < ·)).card : ℤ) - (g.roots.filter (x < ·)).card ≤ 1 ∧
      ((g.roots.filter (x < ·)).card : ℤ) - (f.roots.filter (x < ·)).card ≤ 1 :=
  (succDegreeRootCountAbove_of_rootCount hf hg hdeg
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
  · have hn0 : n = 0 := Nat.eq_zero_of_le_zero (Nat.succ_le_succ_iff.mp hn)
    exact Or.inr (by rw [hn0])

/-- Degree-zero compatible-pair base case for the upper-threshold succ-degree
root-count formulation. -/
theorem compatibleSuccDegreeRootCountAbove_of_natDegree_eq_zero
    {f g : ℝ[X]}
    (hcomp : Compatible f g)
    (_hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hdeg : g.natDegree = f.natDegree + 1)
    (hf_split : f.Splits) (hfdeg : f.natDegree = 0) (x : ℝ) :
      ((f.roots.filter (x < ·)).card : ℤ) - (g.roots.filter (x < ·)).card ≤ 1 ∧
      ((g.roots.filter (x < ·)).card : ℤ) - (f.roots.filter (x < ·)).card ≤ 1 :=
  succDegreeRootCountAbove_of_natDegree_eq_zero hf_split
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

/-- An even integer between `-1` and `1` is zero. -/
private lemma int_eq_zero_of_even_of_le_one_of_neg_le_one {z : ℤ}
    (hz_even : Even z) (hz_le : z ≤ 1) (hneg_le : -z ≤ 1) :
    z = 0 := by
  rcases hz_even with ⟨k, hk⟩
  have hk_le : k ≤ 0 := by linarith
  have hk_nonneg : 0 ≤ k := by linarith
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
    ∃ h : ℝ[X], StrictInterl f h ∧ StrictInterl g h := by
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
    ∃ h : ℝ[X], StrictInterl f h ∧ StrictInterl g h := by
  by_cases hle : f.natDegree ≤ 1
  · exact
      pairHasCommonInterleaver_of_sameDegree_natDegree_le_one
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
    ∃ h : ℝ[X], StrictInterl f h ∧ StrictInterl g h := by
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
    ∃ h : ℝ[X], StrictInterl f h ∧ StrictInterl g h := by
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
    ∃ h : ℝ[X], StrictInterl f h ∧ StrictInterl g h := by
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
    ∃ h : ℝ[X], StrictInterl f h ∧ StrictInterl g h :=
  posComboNoCommonPairHasCommonInterleaver_of_natDegree_le_three_of_cubicInterior
    hbelow habove hsucc hf_pos hg_pos hfnn hgnn hfg hdeg_lo hdeg_hi hno hgdeg
end RealRooted
