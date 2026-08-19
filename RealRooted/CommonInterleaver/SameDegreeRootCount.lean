/-
# Same-degree root-count theory for common interleavers

Same-degree slot-data, root-crossing, root-count, and low-degree endpoint
bridges extracted from `RealRooted.CommonInterleaverTwo`.
-/
import RealRooted.AffineFamily
import RealRooted.CommonInterleaver.IntervalLemmas
import RealRooted.CommonInterleaver.Statements
import RealRooted.CommonInterleaverSeq
import RealRooted.PosCombo
import RealRooted.RootCountJump
import RealRooted.RootOrderBridge
import RealRooted.SameDegreeCubicRootCount
import RealRooted.SameDegreeQuadraticRootCount

open Polynomial

noncomputable section

namespace RealRooted

/-- **Honest missing root-slot boundary for milestone B1 (#41).**

This is the same-degree analogue of
`PosComboNoCommonSuccDegreeSlotDataNonnegStatement`.  For a nonnegative
positive-combination pair with no common roots and `g.natDegree = f.natDegree`,
it packages the remaining converse-Obreschkoff content as nonempty
intersections of matching descending root-slot intervals.

The real-rootedness of `f` and `g` is not bundled here because it is already
available from the same-degree `PosComboRealRooted` lemmas. -/
def PosComboNoCommonSameDegreeSlotDataNonnegStatement : Prop :=
  ∀ ⦃f g : ℝ[X]⦄,
    HasPosLeadingCoeff f →
    HasPosLeadingCoeff g →
    HasNonnegCoeffs f →
    HasNonnegCoeffs g →
    PosComboRealRooted f g →
    g.natDegree = f.natDegree →
    (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
    ∀ j, j < f.natDegree + 1 →
      ∀ (hjf : j < (rootSeqDesc f).length + 1)
        (hjg : j < (rootSeqDesc g).length + 1),
        (rootSlotInterval (rootSeqDesc f) ⟨j, hjf⟩ ∩
          rootSlotInterval (rootSeqDesc g) ⟨j, hjg⟩).Nonempty

/-- **Checked reduction of #41 to the same-degree root-slot boundary.**

The repaired same-degree common-right-interleaver endpoint follows from the
matching slot-intersection condition via the constructive slot theorem in
`CommonInterleaverSeq`. -/
theorem sameDegreePairHasCommonInterleaver_nonneg_of_slotData
    (hstmt : PosComboNoCommonSameDegreeSlotDataNonnegStatement) :
    PosComboNoCommonSameDegreePairHasCommonInterleaverNonnegStatement := by
  intro f g hf_pos hg_pos hfnn hgnn hfg hdeg hno
  have hf_rr : f ≠ 0 ∧ f.Splits :=
    hfg.isRealRooted_left_of_sameDegree hf_pos hg_pos hdeg
  have hg_rr : g ≠ 0 ∧ g.Splits :=
    hfg.isRealRooted_right_of_sameDegree hf_pos hg_pos hdeg
  exact
    pairHasCommonInterleaver_of_sameDegree_slotIntersections
      hf_rr.1 hg_rr.1 hf_rr.2 hg_rr.2 hdeg <|
        fun j hj => hstmt hf_pos hg_pos hfnn hgnn hfg hdeg hno j hj _ _

/-- **Converse of the same-degree slot-data reduction for #41.**

A common right interleaver for the same-degree pair `(f, g)` recovers the
matching root-slot intersections through
`rootSlotInterval_inter_nonempty_of_commonInterleaver`. -/
theorem posComboNoCommonSameDegreeSlotData_of_pairHasCommonInterleaver
    (hstmt : PosComboNoCommonSameDegreePairHasCommonInterleaverNonnegStatement) :
    PosComboNoCommonSameDegreeSlotDataNonnegStatement := by
  intro f g hf_pos hg_pos hfnn hgnn hfg hdeg hno
  obtain ⟨h, hfh, hgh⟩ := hstmt hf_pos hg_pos hfnn hgnn hfg hdeg hno
  intro j hj _ _
  have hjg' : j < g.natDegree + 1 := by lia
  exact rootSlotInterval_inter_nonempty_of_commonInterleaver hfh hgh j hj hjg'

/-- **The #41 same-degree slot-data reformulation is equivalent to the target.**

The matching root-slot statement holds if and only if the repaired
same-degree common-right-interleaver statement holds, so the #41 reduction to
slot data loses no information. -/
theorem posComboNoCommonSameDegreeSlotData_iff_pairHasCommonInterleaver :
    PosComboNoCommonSameDegreeSlotDataNonnegStatement ↔
      PosComboNoCommonSameDegreePairHasCommonInterleaverNonnegStatement :=
  ⟨sameDegreePairHasCommonInterleaver_nonneg_of_slotData,
    posComboNoCommonSameDegreeSlotData_of_pairHasCommonInterleaver⟩

/-- **Combinatorial core of the same-degree slot bound.**

For descending real lists `rf` and `rg` of the same length, if their interior
roots cross in both directions, then every matching root-slot interval meets.
Top and bottom slots meet automatically; the hypotheses are only needed for
interior slots. -/
theorem rootSlotInterval_inter_nonempty_of_sameDegree_crossing
    (rf rg : List ℝ)
    (hrf : rf.Pairwise (· ≥ ·)) (hrg : rg.Pairwise (· ≥ ·))
    (hlen : rg.length = rf.length)
    (hc1 : ∀ j, 1 ≤ j → j < rf.length → rg.getD j 0 ≤ rf.getD (j - 1) 0)
    (hc2 : ∀ j, 1 ≤ j → j < rf.length → rf.getD j 0 ≤ rg.getD (j - 1) 0)
    (j : ℕ) (hjf : j < rf.length + 1) (hjg : j < rg.length + 1) :
    (rootSlotInterval rf ⟨j, hjf⟩ ∩ rootSlotInterval rg ⟨j, hjg⟩).Nonempty := by
  by_cases hlen0 : rf.length = 0
  · rcases rf with (_ | ⟨a, rf⟩)
    · rcases rg with (_ | ⟨b, rg⟩)
      · have hj : j = 0 := by simpa using hjf
        subst j
        simp [rootSlotInterval]
      · simp_all
    · simp_all
  by_cases hj0 : j = 0
  · subst j
    rcases rf with (_ | ⟨a, rf⟩)
    · simp_all
    rcases rg with (_ | ⟨b, rg⟩)
    · simp_all
    change (Set.Ici a ∩ Set.Ici b).Nonempty
    exact ici_inter_ici_nonempty a b
  by_cases hjlast : j = rf.length
  · subst j
    have hrf_len_pos : 0 < rf.length := Nat.pos_of_ne_zero hlen0
    have hrg_len_pos : 0 < rg.length := by simpa [hlen] using hrf_len_pos
    have hrf_rev_ne : rf.reverse ≠ [] := by
      exact List.ne_nil_of_length_pos (by simpa [List.length_reverse] using hrf_len_pos)
    have hrg_rev_ne : rg.reverse ≠ [] := by
      exact List.ne_nil_of_length_pos (by simpa [List.length_reverse] using hrg_len_pos)
    obtain ⟨a, rf', hrf_rev⟩ := List.exists_cons_of_ne_nil hrf_rev_ne
    obtain ⟨b, rg', hrg_rev⟩ := List.exists_cons_of_ne_nil hrg_rev_ne
    convert iic_inter_iic_nonempty a b using 1
    · simp [rootSlotInterval, hrf_rev, hrg_rev, hlen, hlen0]
  · have hjrf : j < rf.length := by lia
    have hjrg : j < rg.length := by simpa [hlen] using hjrf
    have hjpos : 1 ≤ j := by lia
    have hrf_step : rf[j] ≤ rf[j - 1] := by
      simpa [List.get_eq_getElem] using
        get_le_get_of_pairwise_ge hrf
          (i := ⟨j - 1, by lia⟩) (j := ⟨j, hjrf⟩) (by simp)
    have hrg_step : rg[j] ≤ rg[j - 1] := by
      simpa [List.get_eq_getElem] using
        get_le_get_of_pairwise_ge hrg
          (i := ⟨j - 1, by lia⟩) (j := ⟨j, hjrg⟩) (by simp)
    have hcross_gf : rg[j] ≤ rf[j - 1] :=
      getElem_le_getElem_of_getD_le (hc1 j hjpos hjrf) hjrg (by lia)
    have hcross_fg : rf[j] ≤ rg[j - 1] :=
      getElem_le_getElem_of_getD_le (hc2 j hjpos hjrf) hjrf (by lia)
    simpa [rootSlotInterval, hj0, hjlast, hlen] using
      icc_inter_icc_nonempty_of_crossing hrf_step hrg_step hcross_fg hcross_gf

/-- **Sub-statement of milestone B1: descending-root crossing inequalities.**

Given the nonnegative positive-combination/no-common hypotheses at equal
degree, the descending root sequences of `f` and `g` should cross in the two
interior inequalities consumed by
`rootSlotInterval_inter_nonempty_of_sameDegree_crossing`. -/
def PosComboNoCommonSameDegreeRootCrossingNonnegStatement : Prop :=
  ∀ ⦃f g : ℝ[X]⦄,
    HasPosLeadingCoeff f →
    HasPosLeadingCoeff g →
    HasNonnegCoeffs f →
    HasNonnegCoeffs g →
    PosComboRealRooted f g →
    g.natDegree = f.natDegree →
    (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
    (∀ j, 1 ≤ j → j < f.natDegree →
        (rootSeqDesc g).getD j 0 ≤ (rootSeqDesc f).getD (j - 1) 0) ∧
    (∀ j, 1 ≤ j → j < f.natDegree →
        (rootSeqDesc f).getD j 0 ≤ (rootSeqDesc g).getD (j - 1) 0)

/-- **Analytic root-count formulation of milestone B1.**

For a nonnegative positive-combination same-degree pair with no common roots,
the two threshold root-count functions should differ by at most one.  The
pure order bridge `rootCrossing_of_rootCount_diff_le_one` turns this into the
descending-root crossing inequalities. -/
def PosComboNoCommonSameDegreeRootCountNonnegStatement : Prop :=
  ∀ ⦃f g : ℝ[X]⦄,
    HasPosLeadingCoeff f →
    HasPosLeadingCoeff g →
    HasNonnegCoeffs f →
    HasNonnegCoeffs g →
    PosComboRealRooted f g →
    g.natDegree = f.natDegree →
    (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
    ∀ x : ℝ,
      ((f.roots.filter (· ≤ x)).card : ℤ) - (g.roots.filter (· ≤ x)).card ≤ 1 ∧
      ((g.roots.filter (· ≤ x)).card : ℤ) - (f.roots.filter (· ≤ x)).card ≤ 1

/-- **Upper-threshold version of the same-degree root-count formulation.**

This is the form naturally paired with sign-count lemmas, since the sign of a
split polynomial at `x` is controlled by the number of roots strictly above
`x`. -/
def PosComboNoCommonSameDegreeRootCountAboveNonnegStatement : Prop :=
  ∀ ⦃f g : ℝ[X]⦄,
    HasPosLeadingCoeff f →
    HasPosLeadingCoeff g →
    HasNonnegCoeffs f →
    HasNonnegCoeffs g →
    PosComboRealRooted f g →
    g.natDegree = f.natDegree →
    (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
    ∀ x : ℝ,
      ((f.roots.filter (x < ·)).card : ℤ) - (g.roots.filter (x < ·)).card ≤ 1 ∧
      ((g.roots.filter (x < ·)).card : ℤ) - (f.roots.filter (x < ·)).card ≤ 1

/-- Non-root-threshold version of the same-degree lower root-count target.

The `RootCountJump` local-constancy bridge reduces the full lower-threshold
target to this common-non-root form. -/
def PosComboNoCommonSameDegreeRootCountNonRootNonnegStatement : Prop :=
  ∀ ⦃f g : ℝ[X]⦄,
    HasPosLeadingCoeff f →
    HasPosLeadingCoeff g →
    HasNonnegCoeffs f →
    HasNonnegCoeffs g →
    PosComboRealRooted f g →
    g.natDegree = f.natDegree →
    (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
    ∀ x : ℝ, ¬ f.IsRoot x → ¬ g.IsRoot x →
      ((f.roots.filter (· ≤ x)).card : ℤ) - (g.roots.filter (· ≤ x)).card ≤ 1 ∧
      ((g.roots.filter (· ≤ x)).card : ℤ) - (f.roots.filter (· ≤ x)).card ≤ 1

/-- Non-root-threshold version of the same-degree upper root-count target. -/
def PosComboNoCommonSameDegreeRootCountAboveNonRootNonnegStatement : Prop :=
  ∀ ⦃f g : ℝ[X]⦄,
    HasPosLeadingCoeff f →
    HasPosLeadingCoeff g →
    HasNonnegCoeffs f →
    HasNonnegCoeffs g →
    PosComboRealRooted f g →
    g.natDegree = f.natDegree →
    (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
    ∀ x : ℝ, ¬ f.IsRoot x → ¬ g.IsRoot x →
      ((f.roots.filter (x < ·)).card : ℤ) - (g.roots.filter (x < ·)).card ≤ 1 ∧
      ((g.roots.filter (x < ·)).card : ℤ) - (f.roots.filter (x < ·)).card ≤ 1

/-- Same-degree lower root-count bounds reduce to thresholds that are roots
of neither polynomial.  This is the local-constancy bridge used before applying
the fixed-threshold sign/parity lemmas. -/
theorem sameDegreeRootCount_of_nonRoot_bound
    {f g : ℝ[X]} (hf : f ≠ 0) (hg : g ≠ 0)
    (hbound : ∀ x : ℝ, ¬ f.IsRoot x → ¬ g.IsRoot x →
      ((f.roots.filter (· ≤ x)).card : ℤ) - (g.roots.filter (· ≤ x)).card ≤ 1 ∧
      ((g.roots.filter (· ≤ x)).card : ℤ) - (f.roots.filter (· ≤ x)).card ≤ 1) :
    ∀ x : ℝ,
      ((f.roots.filter (· ≤ x)).card : ℤ) - (g.roots.filter (· ≤ x)).card ≤ 1 ∧
      ((g.roots.filter (· ≤ x)).card : ℤ) - (f.roots.filter (· ≤ x)).card ≤ 1 :=
  rootCount_diff_le_one_of_nonRoot_isRoot hf hg hbound

/-- Same-degree upper root-count bounds reduce to thresholds that are roots
of neither polynomial. -/
theorem sameDegreeRootCountAbove_of_nonRoot_bound
    {f g : ℝ[X]} (hf : f ≠ 0) (hg : g ≠ 0)
    (hbound : ∀ x : ℝ, ¬ f.IsRoot x → ¬ g.IsRoot x →
      ((f.roots.filter (x < ·)).card : ℤ) - (g.roots.filter (x < ·)).card ≤ 1 ∧
      ((g.roots.filter (x < ·)).card : ℤ) - (f.roots.filter (x < ·)).card ≤ 1) :
    ∀ x : ℝ,
      ((f.roots.filter (x < ·)).card : ℤ) - (g.roots.filter (x < ·)).card ≤ 1 ∧
      ((g.roots.filter (x < ·)).card : ℤ) - (f.roots.filter (x < ·)).card ≤ 1 :=
  rootCountAbove_diff_le_one_of_nonRoot_isRoot hf hg hbound

/-- Same-degree sign/parity bridge in the right-pencil language.  At a common
non-root threshold, the combined lower root-count parity is equivalent to the
absence of a positive parameter for which `f + C μ * g` vanishes at the
threshold. -/
theorem sameDegree_even_card_roots_le_add_iff_not_exists_pos_isRoot_add_right
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hf_pos : 0 < f.leadingCoeff) (hg_pos : 0 < g.leadingCoeff)
    (hdeg : g.natDegree = f.natDegree)
    {x : ℝ} (hxf : ¬ f.IsRoot x) (hxg : ¬ g.IsRoot x) :
    (Even ((f.roots.filter (· ≤ x)).card + (g.roots.filter (· ≤ x)).card) ↔
      ¬ ∃ μ : ℝ, 0 < μ ∧ (f + C μ * g).IsRoot x) := by
  have hfx_eval : f.eval x ≠ 0 := by
    intro hfx
    exact hxf (by simpa [Polynomial.IsRoot.def] using hfx)
  have hgx_eval : g.eval x ≠ 0 := by
    intro hgx
    exact hxg (by simpa [Polynomial.IsRoot.def] using hgx)
  rw [hf.even_card_roots_le_add_iff_eval_pos_iff hg hf_pos hg_pos hdeg hxf hxg]
  exact (not_exists_pos_isRoot_add_right_iff_eval_pos_iff hfx_eval hgx_eval).symm

/-- Positive-combination same-degree form of
`sameDegree_even_card_roots_le_add_iff_not_exists_pos_isRoot_add_right`. -/
theorem posComboSameDegree_even_card_roots_le_add_iff_not_exists_pos_isRoot_add_right
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfg : PosComboRealRooted f g)
    (hdeg : g.natDegree = f.natDegree)
    {x : ℝ} (hxf : ¬ f.IsRoot x) (hxg : ¬ g.IsRoot x) :
    (Even ((f.roots.filter (· ≤ x)).card + (g.roots.filter (· ≤ x)).card) ↔
      ¬ ∃ μ : ℝ, 0 < μ ∧ (f + C μ * g).IsRoot x) :=
  sameDegree_even_card_roots_le_add_iff_not_exists_pos_isRoot_add_right
    (hfg.isRealRooted_left_of_sameDegree hf_pos hg_pos hdeg).2
    (hfg.isRealRooted_right_of_sameDegree hf_pos hg_pos hdeg).2
    hf_pos hg_pos hdeg hxf hxg

/-- Odd same-degree root-count parity is equivalent to existence of a positive
right-pencil crossing at the threshold. -/
theorem sameDegree_odd_card_roots_le_add_iff_exists_pos_isRoot_add_right
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hf_pos : 0 < f.leadingCoeff) (hg_pos : 0 < g.leadingCoeff)
    (hdeg : g.natDegree = f.natDegree)
    {x : ℝ} (hxf : ¬ f.IsRoot x) (hxg : ¬ g.IsRoot x) :
    (Odd ((f.roots.filter (· ≤ x)).card + (g.roots.filter (· ≤ x)).card) ↔
      ∃ μ : ℝ, 0 < μ ∧ (f + C μ * g).IsRoot x) := by
  rw [← Nat.not_even_iff_odd]
  constructor
  · intro hodd
    by_contra hno
    exact hodd
      ((sameDegree_even_card_roots_le_add_iff_not_exists_pos_isRoot_add_right
        hf hg hf_pos hg_pos hdeg hxf hxg).mpr hno)
  · intro hcross heven
    exact
      ((sameDegree_even_card_roots_le_add_iff_not_exists_pos_isRoot_add_right
        hf hg hf_pos hg_pos hdeg hxf hxg).mp heven) hcross

/-- Positive-combination same-degree form of
`sameDegree_odd_card_roots_le_add_iff_exists_pos_isRoot_add_right`. -/
theorem posComboSameDegree_odd_card_roots_le_add_iff_exists_pos_isRoot_add_right
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfg : PosComboRealRooted f g)
    (hdeg : g.natDegree = f.natDegree)
    {x : ℝ} (hxf : ¬ f.IsRoot x) (hxg : ¬ g.IsRoot x) :
    (Odd ((f.roots.filter (· ≤ x)).card + (g.roots.filter (· ≤ x)).card) ↔
      ∃ μ : ℝ, 0 < μ ∧ (f + C μ * g).IsRoot x) :=
  sameDegree_odd_card_roots_le_add_iff_exists_pos_isRoot_add_right
    (hfg.isRealRooted_left_of_sameDegree hf_pos hg_pos hdeg).2
    (hfg.isRealRooted_right_of_sameDegree hf_pos hg_pos hdeg).2
    hf_pos hg_pos hdeg hxf hxg

/-- Oddness of the lower root-count difference is equivalent to a positive
right-pencil crossing at the threshold. -/
theorem sameDegree_odd_roots_le_count_sub_iff_exists_pos_isRoot_add_right
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hf_pos : 0 < f.leadingCoeff) (hg_pos : 0 < g.leadingCoeff)
    (hdeg : g.natDegree = f.natDegree)
    {x : ℝ} (hxf : ¬ f.IsRoot x) (hxg : ¬ g.IsRoot x) :
    (Odd (((f.roots.filter (· ≤ x)).card : ℤ) -
        (g.roots.filter (· ≤ x)).card) ↔
      ∃ μ : ℝ, 0 < μ ∧ (f + C μ * g).IsRoot x) := by
  rw [odd_int_nat_sub_iff_odd_add]
  exact sameDegree_odd_card_roots_le_add_iff_exists_pos_isRoot_add_right
    hf hg hf_pos hg_pos hdeg hxf hxg

/-- Positive-combination form of
`sameDegree_odd_roots_le_count_sub_iff_exists_pos_isRoot_add_right`. -/
theorem posComboSameDegree_odd_roots_le_count_sub_iff_exists_pos_isRoot_add_right
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfg : PosComboRealRooted f g)
    (hdeg : g.natDegree = f.natDegree)
    {x : ℝ} (hxf : ¬ f.IsRoot x) (hxg : ¬ g.IsRoot x) :
    (Odd (((f.roots.filter (· ≤ x)).card : ℤ) -
        (g.roots.filter (· ≤ x)).card) ↔
      ∃ μ : ℝ, 0 < μ ∧ (f + C μ * g).IsRoot x) := by
  rw [odd_int_nat_sub_iff_odd_add]
  exact posComboSameDegree_odd_card_roots_le_add_iff_exists_pos_isRoot_add_right
    hf_pos hg_pos hfg hdeg hxf hxg

/-- Same-degree sign/parity bridge for upper root counts in the right-pencil
language.  At a common non-root threshold, the combined upper root-count
parity is equivalent to absence of a positive parameter for which
`f + C μ * g` vanishes at the threshold. -/
theorem sameDegree_even_card_roots_gt_add_iff_not_exists_pos_isRoot_add_right
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hf_pos : 0 < f.leadingCoeff) (hg_pos : 0 < g.leadingCoeff)
    {x : ℝ} (hxf : ¬ f.IsRoot x) (hxg : ¬ g.IsRoot x) :
    (Even ((f.roots.filter (x < ·)).card + (g.roots.filter (x < ·)).card) ↔
      ¬ ∃ μ : ℝ, 0 < μ ∧ (f + C μ * g).IsRoot x) := by
  have hfx_eval : f.eval x ≠ 0 := by
    intro hfx
    exact hxf (by simpa [Polynomial.IsRoot.def] using hfx)
  have hgx_eval : g.eval x ≠ 0 := by
    intro hgx
    exact hxg (by simpa [Polynomial.IsRoot.def] using hgx)
  rw [hf.even_card_roots_gt_add_iff_eval_pos_iff hg hf_pos hg_pos hxf hxg]
  exact (not_exists_pos_isRoot_add_right_iff_eval_pos_iff hfx_eval hgx_eval).symm

/-- Positive-combination same-degree form of
`sameDegree_even_card_roots_gt_add_iff_not_exists_pos_isRoot_add_right`. -/
theorem posComboSameDegree_even_card_roots_gt_add_iff_not_exists_pos_isRoot_add_right
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfg : PosComboRealRooted f g)
    (hdeg : g.natDegree = f.natDegree)
    {x : ℝ} (hxf : ¬ f.IsRoot x) (hxg : ¬ g.IsRoot x) :
    (Even ((f.roots.filter (x < ·)).card + (g.roots.filter (x < ·)).card) ↔
      ¬ ∃ μ : ℝ, 0 < μ ∧ (f + C μ * g).IsRoot x) :=
  sameDegree_even_card_roots_gt_add_iff_not_exists_pos_isRoot_add_right
    (hfg.isRealRooted_left_of_sameDegree hf_pos hg_pos hdeg).2
    (hfg.isRealRooted_right_of_sameDegree hf_pos hg_pos hdeg).2
    hf_pos hg_pos hxf hxg

/-- Odd upper root-count parity is equivalent to existence of a positive
right-pencil crossing at the threshold. -/
theorem sameDegree_odd_card_roots_gt_add_iff_exists_pos_isRoot_add_right
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hf_pos : 0 < f.leadingCoeff) (hg_pos : 0 < g.leadingCoeff)
    {x : ℝ} (hxf : ¬ f.IsRoot x) (hxg : ¬ g.IsRoot x) :
    (Odd ((f.roots.filter (x < ·)).card + (g.roots.filter (x < ·)).card) ↔
      ∃ μ : ℝ, 0 < μ ∧ (f + C μ * g).IsRoot x) := by
  rw [← Nat.not_even_iff_odd]
  constructor
  · intro hodd
    by_contra hno
    exact hodd
      ((sameDegree_even_card_roots_gt_add_iff_not_exists_pos_isRoot_add_right
        hf hg hf_pos hg_pos hxf hxg).mpr hno)
  · intro hcross heven
    exact
      ((sameDegree_even_card_roots_gt_add_iff_not_exists_pos_isRoot_add_right
        hf hg hf_pos hg_pos hxf hxg).mp heven) hcross

/-- Positive-combination same-degree form of
`sameDegree_odd_card_roots_gt_add_iff_exists_pos_isRoot_add_right`. -/
theorem posComboSameDegree_odd_card_roots_gt_add_iff_exists_pos_isRoot_add_right
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfg : PosComboRealRooted f g)
    (hdeg : g.natDegree = f.natDegree)
    {x : ℝ} (hxf : ¬ f.IsRoot x) (hxg : ¬ g.IsRoot x) :
    (Odd ((f.roots.filter (x < ·)).card + (g.roots.filter (x < ·)).card) ↔
      ∃ μ : ℝ, 0 < μ ∧ (f + C μ * g).IsRoot x) :=
  sameDegree_odd_card_roots_gt_add_iff_exists_pos_isRoot_add_right
    (hfg.isRealRooted_left_of_sameDegree hf_pos hg_pos hdeg).2
    (hfg.isRealRooted_right_of_sameDegree hf_pos hg_pos hdeg).2
    hf_pos hg_pos hxf hxg

/-- Oddness of the upper root-count difference is equivalent to a positive
right-pencil crossing at the threshold. -/
theorem sameDegree_odd_roots_gt_count_sub_iff_exists_pos_isRoot_add_right
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hf_pos : 0 < f.leadingCoeff) (hg_pos : 0 < g.leadingCoeff)
    {x : ℝ} (hxf : ¬ f.IsRoot x) (hxg : ¬ g.IsRoot x) :
    (Odd (((f.roots.filter (x < ·)).card : ℤ) -
        (g.roots.filter (x < ·)).card) ↔
      ∃ μ : ℝ, 0 < μ ∧ (f + C μ * g).IsRoot x) := by
  rw [odd_int_nat_sub_iff_odd_add]
  exact sameDegree_odd_card_roots_gt_add_iff_exists_pos_isRoot_add_right
    hf hg hf_pos hg_pos hxf hxg

/-- Positive-combination form of
`sameDegree_odd_roots_gt_count_sub_iff_exists_pos_isRoot_add_right`. -/
theorem posComboSameDegree_odd_roots_gt_count_sub_iff_exists_pos_isRoot_add_right
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfg : PosComboRealRooted f g)
    (hdeg : g.natDegree = f.natDegree)
    {x : ℝ} (hxf : ¬ f.IsRoot x) (hxg : ¬ g.IsRoot x) :
    (Odd (((f.roots.filter (x < ·)).card : ℤ) -
        (g.roots.filter (x < ·)).card) ↔
      ∃ μ : ℝ, 0 < μ ∧ (f + C μ * g).IsRoot x) := by
  rw [odd_int_nat_sub_iff_odd_add]
  exact posComboSameDegree_odd_card_roots_gt_add_iff_exists_pos_isRoot_add_right
    hf_pos hg_pos hfg hdeg hxf hxg

/-- Root-count bridge for the same-degree root-crossing target.

If for every threshold `x` the numbers of roots `≤ x`, counted with
multiplicity, of `f` and `g` differ by at most one, then the descending root
sequences of `f` and `g` satisfy the two interior crossing inequalities. -/
theorem rootCrossing_of_rootCount_diff_le_one
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hdeg : g.natDegree = f.natDegree)
    (hcount : ∀ x : ℝ,
      ((f.roots.filter (· ≤ x)).card : ℤ) - (g.roots.filter (· ≤ x)).card ≤ 1 ∧
      ((g.roots.filter (· ≤ x)).card : ℤ) - (f.roots.filter (· ≤ x)).card ≤ 1) :
    (∀ j, 1 ≤ j → j < f.natDegree →
        (rootSeqDesc g).getD j 0 ≤ (rootSeqDesc f).getD (j - 1) 0) ∧
    (∀ j, 1 ≤ j → j < f.natDegree →
        (rootSeqDesc f).getD j 0 ≤ (rootSeqDesc g).getD (j - 1) 0) := by
  have hMcard : f.roots.card = f.natDegree := card_roots_of_splits hf
  have hNcard : g.roots.card = f.natDegree := by rw [card_roots_of_splits hg, hdeg]
  exact rootCrossing_of_count_diff_le_one hMcard hNcard hcount

/-- Root-count bridge from the upper-threshold formulation to the same-degree
root-crossing target. -/
theorem rootCrossing_of_rootCountAbove_diff_le_one
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hdeg : g.natDegree = f.natDegree)
    (hcount : ∀ x : ℝ,
      ((f.roots.filter (x < ·)).card : ℤ) - (g.roots.filter (x < ·)).card ≤ 1 ∧
      ((g.roots.filter (x < ·)).card : ℤ) - (f.roots.filter (x < ·)).card ≤ 1) :
    (∀ j, 1 ≤ j → j < f.natDegree →
        (rootSeqDesc g).getD j 0 ≤ (rootSeqDesc f).getD (j - 1) 0) ∧
    (∀ j, 1 ≤ j → j < f.natDegree →
        (rootSeqDesc f).getD j 0 ≤ (rootSeqDesc g).getD (j - 1) 0) := by
  have hMcard : f.roots.card = f.natDegree := card_roots_of_splits hf
  have hNcard : g.roots.card = f.natDegree := by rw [card_roots_of_splits hg, hdeg]
  exact rootCrossing_of_count_gt_diff_le_one hMcard hNcard hcount

/-- Same-degree descending-root crossing implies the lower-threshold root-count
formulation. -/
theorem sameDegreeRootCount_of_rootCrossing
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hdeg : g.natDegree = f.natDegree)
    (hcross :
      (∀ j, 1 ≤ j → j < f.natDegree →
          (rootSeqDesc g).getD j 0 ≤ (rootSeqDesc f).getD (j - 1) 0) ∧
      (∀ j, 1 ≤ j → j < f.natDegree →
          (rootSeqDesc f).getD j 0 ≤ (rootSeqDesc g).getD (j - 1) 0)) :
    ∀ x : ℝ,
      ((f.roots.filter (· ≤ x)).card : ℤ) - (g.roots.filter (· ≤ x)).card ≤ 1 ∧
      ((g.roots.filter (· ≤ x)).card : ℤ) - (f.roots.filter (· ≤ x)).card ≤ 1 := by
  have hMcard : f.roots.card = f.natDegree := card_roots_of_splits hf
  have hNcard : g.roots.card = f.natDegree := by rw [card_roots_of_splits hg, hdeg]
  simpa [rootSeqDesc] using
    (count_diff_le_one_of_rootCrossing (M := f.roots) (N := g.roots)
      hMcard hNcard hcross)

/-- Convert the upper-threshold same-degree root-count formulation into the
lower-threshold formulation. -/
theorem sameDegreeRootCount_of_rootCountAbove
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hdeg : g.natDegree = f.natDegree)
    (hcount : ∀ x : ℝ,
      ((f.roots.filter (x < ·)).card : ℤ) - (g.roots.filter (x < ·)).card ≤ 1 ∧
      ((g.roots.filter (x < ·)).card : ℤ) - (f.roots.filter (x < ·)).card ≤ 1) :
    ∀ x : ℝ,
      ((f.roots.filter (· ≤ x)).card : ℤ) - (g.roots.filter (· ≤ x)).card ≤ 1 ∧
      ((g.roots.filter (· ≤ x)).card : ℤ) - (f.roots.filter (· ≤ x)).card ≤ 1 := by
  have hMcard : f.roots.card = f.natDegree := card_roots_of_splits hf
  have hNcard : g.roots.card = f.natDegree := by rw [card_roots_of_splits hg, hdeg]
  exact count_le_diff_le_one_of_count_gt_diff_le_one hMcard hNcard hcount

/-- Convert the lower-threshold same-degree root-count formulation into the
upper-threshold formulation. -/
theorem sameDegreeRootCountAbove_of_rootCount
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hdeg : g.natDegree = f.natDegree)
    (hcount : ∀ x : ℝ,
      ((f.roots.filter (· ≤ x)).card : ℤ) - (g.roots.filter (· ≤ x)).card ≤ 1 ∧
      ((g.roots.filter (· ≤ x)).card : ℤ) - (f.roots.filter (· ≤ x)).card ≤ 1) :
    ∀ x : ℝ,
      ((f.roots.filter (x < ·)).card : ℤ) - (g.roots.filter (x < ·)).card ≤ 1 ∧
      ((g.roots.filter (x < ·)).card : ℤ) - (f.roots.filter (x < ·)).card ≤ 1 := by
  have hMcard : f.roots.card = f.natDegree := card_roots_of_splits hf
  have hNcard : g.roots.card = f.natDegree := by rw [card_roots_of_splits hg, hdeg]
  exact count_gt_diff_le_one_of_count_le_diff_le_one hMcard hNcard hcount

/-- The same-degree root-count formulation implies the descending-root
crossing formulation. -/
theorem posComboNoCommonSameDegreeRootCrossing_of_rootCount
    (hcount : PosComboNoCommonSameDegreeRootCountNonnegStatement) :
    PosComboNoCommonSameDegreeRootCrossingNonnegStatement := by
  intro f g hf_pos hg_pos hfnn hgnn hfg hdeg hno
  have hf_split : f.Splits :=
    (hfg.isRealRooted_left_of_sameDegree hf_pos hg_pos hdeg).2
  have hg_split : g.Splits :=
    (hfg.isRealRooted_right_of_sameDegree hf_pos hg_pos hdeg).2
  exact rootCrossing_of_rootCount_diff_le_one hf_split hg_split hdeg
    (hcount hf_pos hg_pos hfnn hgnn hfg hdeg hno)

/-- The upper-threshold same-degree root-count formulation implies the
descending-root crossing formulation. -/
theorem posComboNoCommonSameDegreeRootCrossing_of_rootCountAbove
    (hcount : PosComboNoCommonSameDegreeRootCountAboveNonnegStatement) :
    PosComboNoCommonSameDegreeRootCrossingNonnegStatement := by
  intro f g hf_pos hg_pos hfnn hgnn hfg hdeg hno
  have hf_split : f.Splits :=
    (hfg.isRealRooted_left_of_sameDegree hf_pos hg_pos hdeg).2
  have hg_split : g.Splits :=
    (hfg.isRealRooted_right_of_sameDegree hf_pos hg_pos hdeg).2
  exact rootCrossing_of_rootCountAbove_diff_le_one hf_split hg_split hdeg
    (hcount hf_pos hg_pos hfnn hgnn hfg hdeg hno)

/-- The same-degree descending-root crossing formulation implies the
same-degree root-count formulation. -/
theorem posComboNoCommonSameDegreeRootCount_of_rootCrossing
    (hcross : PosComboNoCommonSameDegreeRootCrossingNonnegStatement) :
    PosComboNoCommonSameDegreeRootCountNonnegStatement := by
  intro f g hf_pos hg_pos hfnn hgnn hfg hdeg hno
  have hf_split : f.Splits :=
    (hfg.isRealRooted_left_of_sameDegree hf_pos hg_pos hdeg).2
  have hg_split : g.Splits :=
    (hfg.isRealRooted_right_of_sameDegree hf_pos hg_pos hdeg).2
  exact sameDegreeRootCount_of_rootCrossing hf_split hg_split hdeg
    (hcross hf_pos hg_pos hfnn hgnn hfg hdeg hno)

/-- The upper-threshold same-degree root-count target implies the
lower-threshold root-count target. -/
theorem posComboNoCommonSameDegreeRootCount_of_rootCountAbove
    (hcount : PosComboNoCommonSameDegreeRootCountAboveNonnegStatement) :
    PosComboNoCommonSameDegreeRootCountNonnegStatement := by
  intro f g hf_pos hg_pos hfnn hgnn hfg hdeg hno
  have hf_split : f.Splits :=
    (hfg.isRealRooted_left_of_sameDegree hf_pos hg_pos hdeg).2
  have hg_split : g.Splits :=
    (hfg.isRealRooted_right_of_sameDegree hf_pos hg_pos hdeg).2
  exact sameDegreeRootCount_of_rootCountAbove hf_split hg_split hdeg
    (hcount hf_pos hg_pos hfnn hgnn hfg hdeg hno)

/-- The lower-threshold same-degree root-count target implies the
upper-threshold root-count target. -/
theorem posComboNoCommonSameDegreeRootCountAbove_of_rootCount
    (hcount : PosComboNoCommonSameDegreeRootCountNonnegStatement) :
    PosComboNoCommonSameDegreeRootCountAboveNonnegStatement := by
  intro f g hf_pos hg_pos hfnn hgnn hfg hdeg hno
  have hf_split : f.Splits :=
    (hfg.isRealRooted_left_of_sameDegree hf_pos hg_pos hdeg).2
  have hg_split : g.Splits :=
    (hfg.isRealRooted_right_of_sameDegree hf_pos hg_pos hdeg).2
  exact sameDegreeRootCountAbove_of_rootCount hf_split hg_split hdeg
    (hcount hf_pos hg_pos hfnn hgnn hfg hdeg hno)

/-- The lower-threshold and upper-threshold same-degree root-count targets are
equivalent. -/
theorem posComboNoCommonSameDegreeRootCountAbove_iff_rootCount :
    PosComboNoCommonSameDegreeRootCountAboveNonnegStatement ↔
      PosComboNoCommonSameDegreeRootCountNonnegStatement :=
  ⟨posComboNoCommonSameDegreeRootCount_of_rootCountAbove,
    posComboNoCommonSameDegreeRootCountAbove_of_rootCount⟩

/-- The same-degree root-crossing target is equivalent to the lower-threshold
root-count target. -/
theorem posComboNoCommonSameDegreeRootCrossing_iff_rootCount :
    PosComboNoCommonSameDegreeRootCrossingNonnegStatement ↔
      PosComboNoCommonSameDegreeRootCountNonnegStatement :=
  ⟨posComboNoCommonSameDegreeRootCount_of_rootCrossing,
    posComboNoCommonSameDegreeRootCrossing_of_rootCount⟩

/-- The same-degree root-crossing target is equivalent to the upper-threshold
root-count target. -/
theorem posComboNoCommonSameDegreeRootCrossing_iff_rootCountAbove :
    PosComboNoCommonSameDegreeRootCrossingNonnegStatement ↔
      PosComboNoCommonSameDegreeRootCountAboveNonnegStatement :=
  ⟨fun hcross =>
      posComboNoCommonSameDegreeRootCountAbove_of_rootCount
        (posComboNoCommonSameDegreeRootCount_of_rootCrossing hcross),
    posComboNoCommonSameDegreeRootCrossing_of_rootCountAbove⟩

/-- The same-degree lower root-count target follows from its common-non-root
variant. -/
theorem posComboNoCommonSameDegreeRootCount_of_nonRoot
    (hcount : PosComboNoCommonSameDegreeRootCountNonRootNonnegStatement) :
    PosComboNoCommonSameDegreeRootCountNonnegStatement := by
  intro f g hf_pos hg_pos hfnn hgnn hfg hdeg hno
  exact sameDegreeRootCount_of_nonRoot_bound hf_pos.ne_zero hg_pos.ne_zero
    (hcount hf_pos hg_pos hfnn hgnn hfg hdeg hno)

/-- The same-degree upper root-count target follows from its common-non-root
variant. -/
theorem posComboNoCommonSameDegreeRootCountAbove_of_nonRoot
    (hcount : PosComboNoCommonSameDegreeRootCountAboveNonRootNonnegStatement) :
    PosComboNoCommonSameDegreeRootCountAboveNonnegStatement := by
  intro f g hf_pos hg_pos hfnn hgnn hfg hdeg hno
  exact sameDegreeRootCountAbove_of_nonRoot_bound hf_pos.ne_zero hg_pos.ne_zero
    (hcount hf_pos hg_pos hfnn hgnn hfg hdeg hno)

/-- Low-degree base case for the same-degree root-count formulation.

If `f` and `g` split, have equal degree, and `f.natDegree ≤ 1`, then at every
threshold the two root counts can differ by at most one. -/
theorem rootCount_diff_le_one_of_natDegree_le_one
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hdeg : g.natDegree = f.natDegree) (hfdeg : f.natDegree ≤ 1) (x : ℝ) :
      ((f.roots.filter (· ≤ x)).card : ℤ) - (g.roots.filter (· ≤ x)).card ≤ 1 ∧
      ((g.roots.filter (· ≤ x)).card : ℤ) - (f.roots.filter (· ≤ x)).card ≤ 1 := by
  have hfcard_nat : (f.roots.filter (· ≤ x)).card ≤ 1 := by
    calc
      (f.roots.filter (· ≤ x)).card ≤ f.roots.card :=
        Multiset.card_le_card (Multiset.filter_le _ _)
      _ = f.natDegree := card_roots_of_splits hf
      _ ≤ 1 := hfdeg
  have hgcard_nat : (g.roots.filter (· ≤ x)).card ≤ 1 := by
    calc
      (g.roots.filter (· ≤ x)).card ≤ g.roots.card :=
        Multiset.card_le_card (Multiset.filter_le _ _)
      _ = g.natDegree := card_roots_of_splits hg
      _ = f.natDegree := hdeg
      _ ≤ 1 := hfdeg
  have hfcard : ((f.roots.filter (· ≤ x)).card : ℤ) ≤ 1 := by exact_mod_cast hfcard_nat
  have hgcard : ((g.roots.filter (· ≤ x)).card : ℤ) ≤ 1 := by exact_mod_cast hgcard_nat
  have hfnonneg : (0 : ℤ) ≤ (f.roots.filter (· ≤ x)).card := by
    exact_mod_cast Nat.zero_le (f.roots.filter (· ≤ x)).card
  have hgnonneg : (0 : ℤ) ≤ (g.roots.filter (· ≤ x)).card := by
    exact_mod_cast Nat.zero_le (g.roots.filter (· ≤ x)).card
  constructor <;> lia

/-- Low-degree base case for the upper-threshold same-degree root-count
formulation. -/
theorem rootCountAbove_diff_le_one_of_natDegree_le_one
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hdeg : g.natDegree = f.natDegree) (hfdeg : f.natDegree ≤ 1) (x : ℝ) :
      ((f.roots.filter (x < ·)).card : ℤ) - (g.roots.filter (x < ·)).card ≤ 1 ∧
      ((g.roots.filter (x < ·)).card : ℤ) - (f.roots.filter (x < ·)).card ≤ 1 :=
  sameDegreeRootCountAbove_of_rootCount hf hg hdeg
    (fun y => rootCount_diff_le_one_of_natDegree_le_one hf hg hdeg hfdeg y) x

/-- Low-degree base case for the same-degree analytic root-count target in
the positive-combination/no-common setting. -/
theorem rootCount_diff_le_one_of_posCombo_sameDegree_natDegree_le_one
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (_hfnn : HasNonnegCoeffs f) (_hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g)
    (hdeg : g.natDegree = f.natDegree)
    (_hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hfdeg : f.natDegree ≤ 1) (x : ℝ) :
      ((f.roots.filter (· ≤ x)).card : ℤ) - (g.roots.filter (· ≤ x)).card ≤ 1 ∧
      ((g.roots.filter (· ≤ x)).card : ℤ) - (f.roots.filter (· ≤ x)).card ≤ 1 := by
  have hf_split : f.Splits :=
    (hfg.isRealRooted_left_of_sameDegree hf_pos hg_pos hdeg).2
  have hg_split : g.Splits :=
    (hfg.isRealRooted_right_of_sameDegree hf_pos hg_pos hdeg).2
  exact rootCount_diff_le_one_of_natDegree_le_one hf_split hg_split hdeg hfdeg x

/-- Low-degree base case for the upper-threshold same-degree analytic
root-count target in the positive-combination/no-common setting. -/
theorem rootCountAbove_diff_le_one_of_posCombo_sameDegree_natDegree_le_one
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (_hfnn : HasNonnegCoeffs f) (_hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g)
    (hdeg : g.natDegree = f.natDegree)
    (_hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hfdeg : f.natDegree ≤ 1) (x : ℝ) :
      ((f.roots.filter (x < ·)).card : ℤ) - (g.roots.filter (x < ·)).card ≤ 1 ∧
      ((g.roots.filter (x < ·)).card : ℤ) - (f.roots.filter (x < ·)).card ≤ 1 := by
  have hf_split : f.Splits :=
    (hfg.isRealRooted_left_of_sameDegree hf_pos hg_pos hdeg).2
  have hg_split : g.Splits :=
    (hfg.isRealRooted_right_of_sameDegree hf_pos hg_pos hdeg).2
  exact rootCountAbove_diff_le_one_of_natDegree_le_one hf_split hg_split hdeg hfdeg x

/-- Degree-two base case for the same-degree analytic root-count target in
the positive-combination setting. -/
theorem rootCount_diff_le_one_of_posCombo_sameDegree_natDegree_eq_two
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfg : PosComboRealRooted f g)
    (hdeg : g.natDegree = f.natDegree)
    (hfdeg : f.natDegree = 2) (x : ℝ) :
      ((f.roots.filter (· ≤ x)).card : ℤ) - (g.roots.filter (· ≤ x)).card ≤ 1 ∧
      ((g.roots.filter (· ≤ x)).card : ℤ) - (f.roots.filter (· ≤ x)).card ≤ 1 := by
  have hgdeg : g.natDegree = 2 := by rw [hdeg, hfdeg]
  exact sameDegree_quadratic_rootCount_le_one
    hfdeg hgdeg
    (hfg.isRealRooted_left_of_sameDegree hf_pos hg_pos hdeg).2
    (hfg.isRealRooted_right_of_sameDegree hf_pos hg_pos hdeg).2
    hf_pos hg_pos
    (fun {lam μ} hlam hμ => (hfg hlam hμ).2)
    x

/-- Degree-two base case for the upper-threshold same-degree analytic
root-count target in the positive-combination setting. -/
theorem rootCountAbove_diff_le_one_of_posCombo_sameDegree_natDegree_eq_two
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfg : PosComboRealRooted f g)
    (hdeg : g.natDegree = f.natDegree)
    (hfdeg : f.natDegree = 2) (x : ℝ) :
      ((f.roots.filter (x < ·)).card : ℤ) - (g.roots.filter (x < ·)).card ≤ 1 ∧
      ((g.roots.filter (x < ·)).card : ℤ) - (f.roots.filter (x < ·)).card ≤ 1 :=
  sameDegreeRootCountAbove_of_rootCount
    (hfg.isRealRooted_left_of_sameDegree hf_pos hg_pos hdeg).2
    (hfg.isRealRooted_right_of_sameDegree hf_pos hg_pos hdeg).2
    hdeg
    (fun y =>
      rootCount_diff_le_one_of_posCombo_sameDegree_natDegree_eq_two
        hf_pos hg_pos hfg hdeg hfdeg y)
    x

/-- Degree-`≤ 2` base case for the same-degree analytic root-count target in
the positive-combination/no-common setting. -/
theorem rootCount_diff_le_one_of_posCombo_sameDegree_natDegree_le_two
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f) (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g)
    (hdeg : g.natDegree = f.natDegree)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hfdeg : f.natDegree ≤ 2) (x : ℝ) :
      ((f.roots.filter (· ≤ x)).card : ℤ) - (g.roots.filter (· ≤ x)).card ≤ 1 ∧
      ((g.roots.filter (· ≤ x)).card : ℤ) - (f.roots.filter (· ≤ x)).card ≤ 1 := by
  by_cases hle : f.natDegree ≤ 1
  · exact rootCount_diff_le_one_of_posCombo_sameDegree_natDegree_le_one
      hf_pos hg_pos hfnn hgnn hfg hdeg hno hle x
  · have htwo : f.natDegree = 2 := by lia
    exact rootCount_diff_le_one_of_posCombo_sameDegree_natDegree_eq_two
      hf_pos hg_pos hfg hdeg htwo x

/-- Degree-`≤ 2` base case for the upper-threshold same-degree analytic
root-count target in the positive-combination/no-common setting. -/
theorem rootCountAbove_diff_le_one_of_posCombo_sameDegree_natDegree_le_two
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f) (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g)
    (hdeg : g.natDegree = f.natDegree)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hfdeg : f.natDegree ≤ 2) (x : ℝ) :
      ((f.roots.filter (x < ·)).card : ℤ) - (g.roots.filter (x < ·)).card ≤ 1 ∧
      ((g.roots.filter (x < ·)).card : ℤ) - (f.roots.filter (x < ·)).card ≤ 1 := by
  by_cases hle : f.natDegree ≤ 1
  · exact rootCountAbove_diff_le_one_of_posCombo_sameDegree_natDegree_le_one
      hf_pos hg_pos hfnn hgnn hfg hdeg hno hle x
  · have htwo : f.natDegree = 2 := by lia
    exact rootCountAbove_diff_le_one_of_posCombo_sameDegree_natDegree_eq_two
      hf_pos hg_pos hfg hdeg htwo x

/-- Low-degree base case for the same-degree root-crossing target.  Through
degree one the interior crossing inequalities are vacuous. -/
theorem sameDegreeRootCrossing_of_natDegree_le_one
    {f g : ℝ[X]} (hf_deg_le_one : f.natDegree ≤ 1) :
    (∀ j, 1 ≤ j → j < f.natDegree →
        (rootSeqDesc g).getD j 0 ≤ (rootSeqDesc f).getD (j - 1) 0) ∧
    (∀ j, 1 ≤ j → j < f.natDegree →
        (rootSeqDesc f).getD j 0 ≤ (rootSeqDesc g).getD (j - 1) 0) := by
  refine ⟨?_, ?_⟩ <;> intro j hj1 hjlt <;> exfalso <;> lia

/-- Degree-two base case for the same-degree root-crossing target in the
positive-combination setting. -/
theorem sameDegreeRootCrossing_of_posCombo_natDegree_eq_two
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfg : PosComboRealRooted f g)
    (hdeg : g.natDegree = f.natDegree)
    (hfdeg : f.natDegree = 2) :
    (∀ j, 1 ≤ j → j < f.natDegree →
        (rootSeqDesc g).getD j 0 ≤ (rootSeqDesc f).getD (j - 1) 0) ∧
    (∀ j, 1 ≤ j → j < f.natDegree →
        (rootSeqDesc f).getD j 0 ≤ (rootSeqDesc g).getD (j - 1) 0) :=
  rootCrossing_of_rootCountAbove_diff_le_one
    (hfg.isRealRooted_left_of_sameDegree hf_pos hg_pos hdeg).2
    (hfg.isRealRooted_right_of_sameDegree hf_pos hg_pos hdeg).2
    hdeg
    (fun x =>
      rootCountAbove_diff_le_one_of_posCombo_sameDegree_natDegree_eq_two
        hf_pos hg_pos hfg hdeg hfdeg x)

/-- Degree-`≤ 2` base case for the same-degree root-crossing target in the
positive-combination/no-common setting. -/
theorem sameDegreeRootCrossing_of_posCombo_natDegree_le_two
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f) (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g)
    (hdeg : g.natDegree = f.natDegree)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hfdeg : f.natDegree ≤ 2) :
    (∀ j, 1 ≤ j → j < f.natDegree →
        (rootSeqDesc g).getD j 0 ≤ (rootSeqDesc f).getD (j - 1) 0) ∧
    (∀ j, 1 ≤ j → j < f.natDegree →
        (rootSeqDesc f).getD j 0 ≤ (rootSeqDesc g).getD (j - 1) 0) :=
  rootCrossing_of_rootCountAbove_diff_le_one
    (hfg.isRealRooted_left_of_sameDegree hf_pos hg_pos hdeg).2
    (hfg.isRealRooted_right_of_sameDegree hf_pos hg_pos hdeg).2
    hdeg
    (fun x =>
      rootCountAbove_diff_le_one_of_posCombo_sameDegree_natDegree_le_two
        hf_pos hg_pos hfnn hgnn hfg hdeg hno hfdeg x)

/-- Degree-`≤ 3` same-degree root-count route, assuming the two cubic interior
partial-separation leaves. -/
theorem rootCount_diff_le_one_of_posCombo_sameDegree_natDegree_le_three_of_cubicInterior
    (hbelow : CubicInteriorTwoBelowStatement)
    (habove : CubicInteriorTwoAboveStatement)
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f) (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g)
    (hdeg : g.natDegree = f.natDegree)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hfdeg : f.natDegree ≤ 3) (x : ℝ) :
      ((f.roots.filter (· ≤ x)).card : ℤ) - (g.roots.filter (· ≤ x)).card ≤ 1 ∧
      ((g.roots.filter (· ≤ x)).card : ℤ) - (f.roots.filter (· ≤ x)).card ≤ 1 := by
  by_cases hle : f.natDegree ≤ 2
  · exact rootCount_diff_le_one_of_posCombo_sameDegree_natDegree_le_two
      hf_pos hg_pos hfnn hgnn hfg hdeg hno hle x
  · have hfdeg3 : f.natDegree = 3 := by lia
    have hgdeg3 : g.natDegree = 3 := by rw [hdeg, hfdeg3]
    exact sameDegree_cubic_rootCount_le_one_of_interior hbelow habove
      hfdeg3 hgdeg3
      (hfg.isRealRooted_left_of_sameDegree hf_pos hg_pos hdeg).2
      (hfg.isRealRooted_right_of_sameDegree hf_pos hg_pos hdeg).2
      hf_pos hg_pos hfg x

/-- Degree-`≤ 3` same-degree upper-threshold route, assuming the two cubic
interior partial-separation leaves. -/
theorem rootCountAbove_diff_le_one_of_posCombo_sameDegree_natDegree_le_three_of_cubicInterior
    (hbelow : CubicInteriorTwoBelowStatement)
    (habove : CubicInteriorTwoAboveStatement)
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f) (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g)
    (hdeg : g.natDegree = f.natDegree)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hfdeg : f.natDegree ≤ 3) (x : ℝ) :
      ((f.roots.filter (x < ·)).card : ℤ) - (g.roots.filter (x < ·)).card ≤ 1 ∧
      ((g.roots.filter (x < ·)).card : ℤ) - (f.roots.filter (x < ·)).card ≤ 1 :=
  sameDegreeRootCountAbove_of_rootCount
    (hfg.isRealRooted_left_of_sameDegree hf_pos hg_pos hdeg).2
    (hfg.isRealRooted_right_of_sameDegree hf_pos hg_pos hdeg).2
    hdeg
    (fun y =>
      rootCount_diff_le_one_of_posCombo_sameDegree_natDegree_le_three_of_cubicInterior
        hbelow habove hf_pos hg_pos hfnn hgnn hfg hdeg hno hfdeg y)
    x

/-- Degree-`≤ 3` same-degree root-crossing route, assuming the two cubic
interior partial-separation leaves. -/
theorem sameDegreeRootCrossing_of_posCombo_natDegree_le_three_of_cubicInterior
    (hbelow : CubicInteriorTwoBelowStatement)
    (habove : CubicInteriorTwoAboveStatement)
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f) (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g)
    (hdeg : g.natDegree = f.natDegree)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hfdeg : f.natDegree ≤ 3) :
    (∀ j, 1 ≤ j → j < f.natDegree →
        (rootSeqDesc g).getD j 0 ≤ (rootSeqDesc f).getD (j - 1) 0) ∧
    (∀ j, 1 ≤ j → j < f.natDegree →
        (rootSeqDesc f).getD j 0 ≤ (rootSeqDesc g).getD (j - 1) 0) :=
  rootCrossing_of_rootCountAbove_diff_le_one
    (hfg.isRealRooted_left_of_sameDegree hf_pos hg_pos hdeg).2
    (hfg.isRealRooted_right_of_sameDegree hf_pos hg_pos hdeg).2
    hdeg
    (fun x =>
      rootCountAbove_diff_le_one_of_posCombo_sameDegree_natDegree_le_three_of_cubicInterior
        hbelow habove hf_pos hg_pos hfnn hgnn hfg hdeg hno hfdeg x)

/-- Degree-`≤ 3` same-degree slot-data route, assuming the two cubic interior
partial-separation leaves. -/
theorem sameDegreeSlotData_of_posCombo_natDegree_le_three_of_cubicInterior
    (hbelow : CubicInteriorTwoBelowStatement)
    (habove : CubicInteriorTwoAboveStatement)
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f) (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g)
    (hdeg : g.natDegree = f.natDegree)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hfdeg : f.natDegree ≤ 3) :
    ∀ j, j < f.natDegree + 1 →
      ∀ (hjf : j < (rootSeqDesc f).length + 1)
        (hjg : j < (rootSeqDesc g).length + 1),
        (rootSlotInterval (rootSeqDesc f) ⟨j, hjf⟩ ∩
          rootSlotInterval (rootSeqDesc g) ⟨j, hjg⟩).Nonempty := by
  have hf_split : f.Splits :=
    (hfg.isRealRooted_left_of_sameDegree hf_pos hg_pos hdeg).2
  have hg_split : g.Splits :=
    (hfg.isRealRooted_right_of_sameDegree hf_pos hg_pos hdeg).2
  obtain ⟨hc1, hc2⟩ :=
    sameDegreeRootCrossing_of_posCombo_natDegree_le_three_of_cubicInterior
      hbelow habove hf_pos hg_pos hfnn hgnn hfg hdeg hno hfdeg
  have hlenf : (rootSeqDesc f).length = f.natDegree :=
    rootSeqDesc_length hf_split
  have hleng : (rootSeqDesc g).length = g.natDegree :=
    rootSeqDesc_length hg_split
  intro j _ hjf hjg
  exact
    rootSlotInterval_inter_nonempty_of_sameDegree_crossing
      (rootSeqDesc f) (rootSeqDesc g) rootSeqDesc_pairwise rootSeqDesc_pairwise
      (by rw [hleng, hlenf, hdeg])
      (fun k hk1 hk2 => hc1 k hk1 (by rw [hlenf] at hk2; exact hk2))
      (fun k hk1 hk2 => hc2 k hk1 (by rw [hlenf] at hk2; exact hk2))
      j hjf hjg

/-- Degree-`≤ 3` same-degree common-interleaver endpoint, assuming the two
cubic interior partial-separation leaves. -/
theorem sameDegreePairHasCommonInterleaver_nonneg_of_natDegree_le_three_of_cubicInterior
    (hbelow : CubicInteriorTwoBelowStatement)
    (habove : CubicInteriorTwoAboveStatement)
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f) (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g)
    (hdeg : g.natDegree = f.natDegree)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hfdeg : f.natDegree ≤ 3) :
    ∃ h : ℝ[X], Prec f h ∧ Prec g h := by
  have hf_rr : f ≠ 0 ∧ f.Splits :=
    hfg.isRealRooted_left_of_sameDegree hf_pos hg_pos hdeg
  have hg_rr : g ≠ 0 ∧ g.Splits :=
    hfg.isRealRooted_right_of_sameDegree hf_pos hg_pos hdeg
  exact
    pairHasCommonInterleaver_of_sameDegree_slotIntersections
      hf_rr.1 hg_rr.1 hf_rr.2 hg_rr.2 hdeg <|
        fun j hj =>
          sameDegreeSlotData_of_posCombo_natDegree_le_three_of_cubicInterior
            hbelow habove hf_pos hg_pos hfnn hgnn hfg hdeg hno hfdeg j hj _ _

/-- Degree-`≤ 3` no-common same-degree endpoint, assuming the two cubic
interior partial-separation leaves. -/
theorem posComboNoCommonSameDegreePairHasCommonInterleaver_of_natDegree_le_three_of_cubicInterior
    (hbelow : CubicInteriorTwoBelowStatement)
    (habove : CubicInteriorTwoAboveStatement)
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f) (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g)
    (hdeg : g.natDegree = f.natDegree)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hfdeg : f.natDegree ≤ 3) :
    ∃ h : ℝ[X], Prec f h ∧ Prec g h :=
  sameDegreePairHasCommonInterleaver_nonneg_of_natDegree_le_three_of_cubicInterior
    hbelow habove hf_pos hg_pos hfnn hgnn hfg hdeg hno hfdeg

/-- The same-degree orientation alternative gives the descending-root crossing
inequalities consumed by the #41 slot-data reduction. -/
theorem posComboNoCommonSameDegreeRootCrossing_of_orientationAlternative
    (hsame : PosComboNoCommonSameDegreeOrientationAlternativeNonnegStatement) :
    PosComboNoCommonSameDegreeRootCrossingNonnegStatement := by
  intro f g hf_pos hg_pos hfnn hgnn hfg hdeg hno
  have hf_rr : f ≠ 0 ∧ f.Splits :=
    hfg.isRealRooted_left_of_sameDegree hf_pos hg_pos hdeg
  have hg_rr : g ≠ 0 ∧ g.Splits :=
    hfg.isRealRooted_right_of_sameDegree hf_pos hg_pos hdeg
  obtain ⟨sf, sg, hsf_pw, hsg_pw, hsf_eq, hsg_eq, halt⟩ :
      ∃ sf sg : List ℝ, sf.Pairwise (· ≤ ·) ∧ sg.Pairwise (· ≤ ·) ∧
        (↑sf : Multiset ℝ) = f.roots ∧ (↑sg : Multiset ℝ) = g.roots ∧
        (ListAlternates sf sg ∨ ListAlternates sg sf) := by
    rcases hsame hf_pos hg_pos hfnn hgnn hfg hdeg hno with hprec | hprec
    · obtain ⟨hf, hg, ss, rs, hss_pw, hrs_pw, hss_eq, hrs_eq, hshape⟩ := hprec
      have hss_len : ss.length = f.natDegree := by
        rw [← Multiset.coe_card, hss_eq, card_roots_of_splits hf.2]
      have hrs_len : rs.length = g.natDegree := by
        rw [← Multiset.coe_card, hrs_eq, card_roots_of_splits hg.2]
      have halt : ListAlternates ss rs := by
        rcases hshape with ⟨hlen1, _⟩ | ⟨_, h⟩
        · exfalso
          rw [hss_len, hrs_len, hdeg] at hlen1
          lia
        · exact h
      exact ⟨ss, rs, hss_pw, hrs_pw, hss_eq, hrs_eq, Or.inl halt⟩
    · obtain ⟨hg, hf, sg, sf, hsg_pw, hsf_pw, hsg_eq, hsf_eq, hshape⟩ := hprec
      have hsg_len : sg.length = g.natDegree := by
        rw [← Multiset.coe_card, hsg_eq, card_roots_of_splits hg.2]
      have hsf_len : sf.length = f.natDegree := by
        rw [← Multiset.coe_card, hsf_eq, card_roots_of_splits hf.2]
      have halt : ListAlternates sg sf := by
        rcases hshape with ⟨hlen1, _⟩ | ⟨_, h⟩
        · exfalso
          rw [hsg_len, hsf_len, hdeg] at hlen1
          lia
        · exact h
      exact ⟨sf, sg, hsf_pw, hsg_pw, hsf_eq, hsg_eq, Or.inr halt⟩
  have hsf_len : sf.length = f.natDegree := by
    rw [← Multiset.coe_card, hsf_eq, card_roots_of_splits hf_rr.2]
  have hsg_len : sg.length = g.natDegree := by
    rw [← Multiset.coe_card, hsg_eq, card_roots_of_splits hg_rr.2]
  have hdf : rootSeqDesc f = sf.reverse :=
    rootSeqDesc_eq_reverse_of_pairwise hsf_pw hsf_eq
  have hdg : rootSeqDesc g = sg.reverse :=
    rootSeqDesc_eq_reverse_of_pairwise hsg_pw hsg_eq
  have hlen : sf.length = sg.length := by rw [hsf_len, hsg_len, hdeg]
  obtain ⟨hc1, hc2⟩ := rootCrossing_of_listAlternates_or hlen halt
  rw [hdf, hdg]
  exact ⟨
    (fun j hj1 hj2 => hc1 j hj1 (by rw [hsf_len]; exact hj2)),
    fun j hj1 hj2 => hc2 j hj1 (by rw [hsf_len]; exact hj2)⟩

/-- **Reduction of milestone B1 to its root-crossing content.**

The same-degree slot-data statement follows from the descending-root crossing
inequalities; the remaining work is therefore the analytic converse-Obreschkoff
crossing input. -/
theorem posComboNoCommonSameDegreeSlotData_of_rootCrossing
    (hcross : PosComboNoCommonSameDegreeRootCrossingNonnegStatement) :
    PosComboNoCommonSameDegreeSlotDataNonnegStatement := by
  intro f g hf_pos hg_pos hfnn hgnn hfg hdeg hno
  have hf_split : f.Splits :=
    (hfg.isRealRooted_left_of_sameDegree hf_pos hg_pos hdeg).2
  have hg_split : g.Splits :=
    (hfg.isRealRooted_right_of_sameDegree hf_pos hg_pos hdeg).2
  obtain ⟨hc1, hc2⟩ := hcross hf_pos hg_pos hfnn hgnn hfg hdeg hno
  have hlenf : (rootSeqDesc f).length = f.natDegree := rootSeqDesc_length hf_split
  have hleng : (rootSeqDesc g).length = g.natDegree := rootSeqDesc_length hg_split
  intro j _ hjf hjg
  exact
    rootSlotInterval_inter_nonempty_of_sameDegree_crossing
      (rootSeqDesc f) (rootSeqDesc g) rootSeqDesc_pairwise rootSeqDesc_pairwise
      (by rw [hleng, hlenf, hdeg])
      (fun k hk1 hk2 => hc1 k hk1 (by rw [hlenf] at hk2; exact hk2))
      (fun k hk1 hk2 => hc2 k hk1 (by rw [hlenf] at hk2; exact hk2))
      j hjf hjg

/-- The repaired same-degree pair-interleaver endpoint follows directly from
the same-degree descending-root crossing inequalities. -/
theorem sameDegreePairHasCommonInterleaver_nonneg_of_rootCrossing
    (hcross : PosComboNoCommonSameDegreeRootCrossingNonnegStatement) :
    PosComboNoCommonSameDegreePairHasCommonInterleaverNonnegStatement :=
  sameDegreePairHasCommonInterleaver_nonneg_of_slotData
    (posComboNoCommonSameDegreeSlotData_of_rootCrossing hcross)

/-- The same-degree slot-data statement follows directly from the analytic
root-count formulation. -/
theorem posComboNoCommonSameDegreeSlotData_of_rootCount
    (hcount : PosComboNoCommonSameDegreeRootCountNonnegStatement) :
    PosComboNoCommonSameDegreeSlotDataNonnegStatement :=
  posComboNoCommonSameDegreeSlotData_of_rootCrossing
    (posComboNoCommonSameDegreeRootCrossing_of_rootCount hcount)

/-- The repaired same-degree pair-interleaver endpoint follows directly from
the analytic root-count formulation. -/
theorem sameDegreePairHasCommonInterleaver_nonneg_of_rootCount
    (hcount : PosComboNoCommonSameDegreeRootCountNonnegStatement) :
    PosComboNoCommonSameDegreePairHasCommonInterleaverNonnegStatement :=
  sameDegreePairHasCommonInterleaver_nonneg_of_rootCrossing
    (posComboNoCommonSameDegreeRootCrossing_of_rootCount hcount)

/-- The same-degree slot-data statement follows directly from the
upper-threshold analytic root-count formulation. -/
theorem posComboNoCommonSameDegreeSlotData_of_rootCountAbove
    (hcount : PosComboNoCommonSameDegreeRootCountAboveNonnegStatement) :
    PosComboNoCommonSameDegreeSlotDataNonnegStatement :=
  posComboNoCommonSameDegreeSlotData_of_rootCrossing
    (posComboNoCommonSameDegreeRootCrossing_of_rootCountAbove hcount)

/-- The repaired same-degree pair-interleaver endpoint follows directly from
the upper-threshold analytic root-count formulation. -/
theorem sameDegreePairHasCommonInterleaver_nonneg_of_rootCountAbove
    (hcount : PosComboNoCommonSameDegreeRootCountAboveNonnegStatement) :
    PosComboNoCommonSameDegreePairHasCommonInterleaverNonnegStatement :=
  sameDegreePairHasCommonInterleaver_nonneg_of_rootCrossing
    (posComboNoCommonSameDegreeRootCrossing_of_rootCountAbove hcount)

/-- Same-degree root crossing from the common-non-root lower-threshold
root-count formulation. -/
theorem posComboNoCommonSameDegreeRootCrossing_of_rootCountNonRoot
    (hcount : PosComboNoCommonSameDegreeRootCountNonRootNonnegStatement) :
    PosComboNoCommonSameDegreeRootCrossingNonnegStatement :=
  posComboNoCommonSameDegreeRootCrossing_of_rootCount
    (posComboNoCommonSameDegreeRootCount_of_nonRoot hcount)

/-- Same-degree root crossing from the common-non-root upper-threshold
root-count formulation. -/
theorem posComboNoCommonSameDegreeRootCrossing_of_rootCountAboveNonRoot
    (hcount : PosComboNoCommonSameDegreeRootCountAboveNonRootNonnegStatement) :
    PosComboNoCommonSameDegreeRootCrossingNonnegStatement :=
  posComboNoCommonSameDegreeRootCrossing_of_rootCountAbove
    (posComboNoCommonSameDegreeRootCountAbove_of_nonRoot hcount)

/-- Same-degree slot data from the common-non-root lower-threshold root-count
formulation. -/
theorem posComboNoCommonSameDegreeSlotData_of_rootCountNonRoot
    (hcount : PosComboNoCommonSameDegreeRootCountNonRootNonnegStatement) :
    PosComboNoCommonSameDegreeSlotDataNonnegStatement :=
  posComboNoCommonSameDegreeSlotData_of_rootCount
    (posComboNoCommonSameDegreeRootCount_of_nonRoot hcount)

/-- Same-degree slot data from the common-non-root upper-threshold root-count
formulation. -/
theorem posComboNoCommonSameDegreeSlotData_of_rootCountAboveNonRoot
    (hcount : PosComboNoCommonSameDegreeRootCountAboveNonRootNonnegStatement) :
    PosComboNoCommonSameDegreeSlotDataNonnegStatement :=
  posComboNoCommonSameDegreeSlotData_of_rootCountAbove
    (posComboNoCommonSameDegreeRootCountAbove_of_nonRoot hcount)

/-- The repaired same-degree pair-interleaver endpoint follows from the
common-non-root lower-threshold root-count formulation. -/
theorem sameDegreePairHasCommonInterleaver_nonneg_of_rootCountNonRoot
    (hcount : PosComboNoCommonSameDegreeRootCountNonRootNonnegStatement) :
    PosComboNoCommonSameDegreePairHasCommonInterleaverNonnegStatement :=
  sameDegreePairHasCommonInterleaver_nonneg_of_rootCount
    (posComboNoCommonSameDegreeRootCount_of_nonRoot hcount)

/-- The repaired same-degree pair-interleaver endpoint follows from the
common-non-root upper-threshold root-count formulation. -/
theorem sameDegreePairHasCommonInterleaver_nonneg_of_rootCountAboveNonRoot
    (hcount : PosComboNoCommonSameDegreeRootCountAboveNonRootNonnegStatement) :
    PosComboNoCommonSameDegreePairHasCommonInterleaverNonnegStatement :=
  sameDegreePairHasCommonInterleaver_nonneg_of_rootCountAbove
    (posComboNoCommonSameDegreeRootCountAbove_of_nonRoot hcount)

end RealRooted
