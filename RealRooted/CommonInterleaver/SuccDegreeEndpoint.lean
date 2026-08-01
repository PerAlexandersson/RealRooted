/-
# Succ-degree endpoint and degree-drop reductions

Succ-degree slot-data and left-endpoint reductions extracted from
`RealRooted.CommonInterleaverTwo`.
-/
import RealRooted.AffineFamily
import RealRooted.CommonInterleaver.AffineBoundary
import RealRooted.CommonInterleaver.IntervalLemmas
import RealRooted.CommonInterleaver.Statements
import RealRooted.CommonInterleaverSeq
import RealRooted.DegreeDropDivXPrec
import RealRooted.DegreeDropReversal
import RealRooted.PFPolynomial
import RealRooted.PosCombo
import RealRooted.RootContinuity
import RealRooted.SuccDegreeLeftEndpoint

open Polynomial

noncomputable section

namespace RealRooted

/-- **Honest missing root-slot boundary for milestone B2 (#42).**

This is the succ-degree analogue of the same-degree slot-intersection input
used for #41.  For a nonnegative positive-combination pair with no common
roots and `g.natDegree = f.natDegree + 1`, it packages the two remaining
pieces of the remaining converse-Obreschkoff content:

* real-rootedness of the lower-degree member `f`, and
* the descending root-slot intervals of `f` and `g` meet in each of the
  `f.natDegree + 1` common slots.

The right endpoint `g` is now supplied by
`PosComboRealRooted.isRealRooted_right_of_succDegree`.
The `Fin` bounds are threaded as explicit hypotheses so no in-type proof
obligations remain. -/
def PosComboNoCommonSuccDegreeSlotDataNonnegStatement : Prop :=
  ∀ ⦃f g : ℝ[X]⦄,
    HasPosLeadingCoeff f →
    HasPosLeadingCoeff g →
    HasNonnegCoeffs f →
    HasNonnegCoeffs g →
    PosComboRealRooted f g →
    g.natDegree = f.natDegree + 1 →
    (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
    (f ≠ 0 ∧ f.Splits) ∧
      ∀ j, j < f.natDegree + 1 →
        ∀ (hjf : j < (rootSeqDesc f).length + 1)
          (hjg : j < (rootSeqDesc g).length + 1),
          (rootSlotInterval (rootSeqDesc f) ⟨j, hjf⟩ ∩
            rootSlotInterval (rootSeqDesc g) ⟨j, hjg⟩).Nonempty

/-- **Checked reduction of #42 to the root-slot boundary.**

The corrected succ-degree common-right-interleaver endpoint follows from the
precise root-slot condition `PosComboNoCommonSuccDegreeSlotDataNonnegStatement`
via the constructive slot theorem.  This mirrors the same-degree slot boundary
route for #41. -/
theorem succDegreePairHasCommonInterleaver_nonneg_of_slotData
    (hstmt : PosComboNoCommonSuccDegreeSlotDataNonnegStatement) :
    (∀ ⦃f g : ℝ[X]⦄,
    HasPosLeadingCoeff f →
    HasPosLeadingCoeff g →
    HasNonnegCoeffs f →
    HasNonnegCoeffs g →
    PosComboRealRooted f g →
    g.natDegree = f.natDegree + 1 →
    (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
    ∃ h : ℝ[X], Prec f h ∧ Prec g h) := by
  intro f g hf_pos hg_pos hfnn hgnn hfg hsucc hno
  obtain ⟨hf_rr, hslot⟩ := hstmt hf_pos hg_pos hfnn hgnn hfg hsucc hno
  have hg_rr : g ≠ 0 ∧ g.Splits :=
    hfg.isRealRooted_right_of_succDegree hf_pos hg_pos hsucc
  exact
    pairHasCommonInterleaver_of_succDegree_slotIntersections
      hf_rr.1 hg_rr.1 hf_rr.2 hg_rr.2 hsucc <|
        fun j hj => hslot j hj _ _

/-- **Converse of the slot-data reduction for #42.**

A common right interleaver `h` for the succ-degree pair `(f, g)` recovers both
pieces bundled by `PosComboNoCommonSuccDegreeSlotDataNonnegStatement`:
real-rootedness of `f` is the left component of `Prec f h`, and each root-slot
intersection is witnessed by the corresponding root of `h` through
`rootSlotInterval_inter_nonempty_of_commonInterleaver`.

Together with `succDegreePairHasCommonInterleaver_nonneg_of_slotData` this shows
the slot-data hypothesis is equivalent to the actual common-interleaver goal,
so the reduction to root slots loses nothing. -/
theorem posComboNoCommonSuccDegreeSlotData_of_pairHasCommonInterleaver :
    PosComboNoCommonSuccDegreeSlotDataNonnegStatement := by
  intro f g hf_pos hg_pos hfnn hgnn hfg hsucc hno
  obtain ⟨h, hfh, hgh⟩ := PosComboNoCommonSuccDegreePairHasCommonInterleaverNonneg hf_pos hg_pos hfnn hgnn hfg hsucc hno
  refine ⟨hfh.1, ?_⟩
  intro j hj _ _
  have hjg' : j < g.natDegree + 1 := by lia
  exact rootSlotInterval_inter_nonempty_of_commonInterleaver hfh hgh j hj hjg'

/-- **The #42 slot-data reformulation is equivalent to the target.**

Combining `succDegreePairHasCommonInterleaver_nonneg_of_slotData` with its
converse `posComboNoCommonSuccDegreeSlotData_of_pairHasCommonInterleaver`, the
root-slot statement `PosComboNoCommonSuccDegreeSlotDataNonnegStatement` holds if
and only if the common-right-interleaver statement
`(∀ ⦃f g : ℝ[X]⦄,
    HasPosLeadingCoeff f →
    HasPosLeadingCoeff g →
    HasNonnegCoeffs f →
    HasNonnegCoeffs g →
    PosComboRealRooted f g →
    g.natDegree = f.natDegree + 1 →
    (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
    ∃ h : ℝ[X], Prec f h ∧ Prec g h)` does. This
pins down the exact remaining content of milestone B2: proving the slot data is
neither stronger nor weaker than proving the interleaver goal directly. -/
theorem posComboNoCommonSuccDegreeSlotData_iff_pairHasCommonInterleaver :
    PosComboNoCommonSuccDegreeSlotDataNonnegStatement ↔
      (∀ ⦃f g : ℝ[X]⦄,
    HasPosLeadingCoeff f →
    HasPosLeadingCoeff g →
    HasNonnegCoeffs f →
    HasNonnegCoeffs g →
    PosComboRealRooted f g →
    g.natDegree = f.natDegree + 1 →
    (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
    ∃ h : ℝ[X], Prec f h ∧ Prec g h) :=
  ⟨succDegreePairHasCommonInterleaver_nonneg_of_slotData,
    fun _ => posComboNoCommonSuccDegreeSlotData_of_pairHasCommonInterleaver⟩

/-- **Combinatorial core of the succ-degree slot bound.**

For descending real lists `rf` (length `n`) and `rg` (length `n + 1`), if the
roots weave - `hc1`: for `1 ≤ j ≤ n`, `rg`'s `j`-th element is `≤` `rf`'s
`(j-1)`-th; `hc2`: for `1 ≤ j < n`, `rf`'s `j`-th is `≤` `rg`'s `(j-1)`-th -
then for every common slot `j ≤ n` the descending slot intervals of `rf` and
`rg` intersect. This turns the analytic converse-Obreschkoff content into two
clean root inequalities. (`List.getD _ _ 0` avoids in-bounds side goals.) -/
theorem rootSlotInterval_inter_nonempty_of_crossing
    (rf rg : List ℝ)
    (hrf : rf.Pairwise (· ≥ ·)) (hrg : rg.Pairwise (· ≥ ·))
    (hlen : rg.length = rf.length + 1)
    (hc1 : ∀ j, 1 ≤ j → j ≤ rf.length → rg.getD j 0 ≤ rf.getD (j - 1) 0)
    (hc2 : ∀ j, 1 ≤ j → j < rf.length → rf.getD j 0 ≤ rg.getD (j - 1) 0)
    (j : ℕ) (hjf : j < rf.length + 1) (hjg : j < rg.length + 1) :
    (rootSlotInterval rf ⟨j, hjf⟩ ∩ rootSlotInterval rg ⟨j, hjg⟩).Nonempty := by
  rcases j with (_ | j) <;>
    simp_all +decide only [ge_iff_le, List.getD_eq_getElem?_getD, Order.lt_add_one_iff,
      getElem?_pos, Option.getD_some, rootSlotInterval, ↓reduceDIte, Fin.zero_eta,
      List.length_nil, Nat.reduceAdd, List.length_cons, Nat.add_eq_zero_iff, and_false,
      List.get_eq_getElem, add_tsub_cancel_right, Nat.add_right_cancel_iff]
  · rcases rf with (_ | ⟨r, rf⟩) <;> rcases rg with (_ | ⟨s, rg⟩) <;> norm_num at *
  · split_ifs
    · exfalso
      lia
    · rcases x : rf.reverse with (_ | ⟨r, _ | ⟨s, l⟩⟩) <;>
          simp_all +decide only [lt_add_iff_pos_right, Order.lt_one_iff,
            List.reverse_eq_nil_iff, List.length_nil,
            Set.univ_inter, Set.nonempty_Icc, List.Pairwise.nil, nonpos_iff_eq_zero,
            zero_tsub, not_false_eq_true, getElem?_neg, Option.getD_none,
            not_lt_zero, IsEmpty.forall_iff, implies_true, Nat.add_eq_zero_iff,
            and_false, List.reverse_eq_cons_iff, List.reverse_nil, List.nil_append,
            List.length_cons, zero_add, List.pairwise_cons, List.not_mem_nil, and_self,
            Nat.sub_eq_zero_of_le, getElem?_pos, List.getElem_cons_zero, Option.getD_some,
            Nat.reduceAdd, Order.lt_two_iff, Nat.add_eq_right, List.reverse_cons,
            List.append_assoc, List.cons_append, List.length_append, List.length_reverse,
            Nat.add_right_cancel_iff]
      · rcases rg with (_ | ⟨a, _ | ⟨b, rg⟩⟩) <;>
            simp_all +decide only [List.pairwise_cons, List.mem_cons, forall_eq_or_imp,
              List.getElem_cons_succ, List.getElem_cons_zero]
        · contradiction
        · grind
        · have hba : b ≤ a := hrg.1.1
          exact iic_inter_icc_nonempty_of_left hba
            (by simpa using hc1 1 (by norm_num) (by norm_num))
      · refine ⟨rg[l.length + 2], ?_, ?_⟩ <;> norm_num
        · have h := hc1 (l.length + 2) (by lia) (by lia)
          have hr : (l.reverse ++ [s, r])[l.length + 2 - 1]?.getD 0 = r := by
            rw [List.getElem?_append_right (by simp)]
            simp
          rwa [hr] at h
        · simpa [List.get_eq_getElem] using
            get_le_get_of_pairwise_ge hrg
              (i := ⟨l.length + 1, by lia⟩)
              (j := ⟨l.length + 2, by lia⟩)
              (by simp)
    · exfalso
      lia
    · have hrf_step : rf[j + 1] ≤ rf[j] := by
        simpa [List.get_eq_getElem] using
          get_le_get_of_pairwise_ge hrf
            (i := ⟨j, by lia⟩) (j := ⟨j + 1, by lia⟩) (by simp)
      have hrg_step : rg[j + 1] ≤ rg[j] := by
        simpa [List.get_eq_getElem] using
          get_le_get_of_pairwise_ge hrg
            (i := ⟨j, by lia⟩) (j := ⟨j + 1, by lia⟩) (by simp)
      have hcross_gf : rg[j + 1] ≤ rf[j] := by
        simpa [List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem (l := rg) (i := j + 1) (by lia),
          List.getElem?_eq_getElem (l := rf) (i := j) (by lia)]
          using hc1 (j + 1) (by lia) (by lia)
      have hcross_fg : rf[j + 1] ≤ rg[j] := by
        simpa [List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem (l := rf) (i := j + 1) (by lia),
          List.getElem?_eq_getElem (l := rg) (i := j) (by lia)]
          using hc2 (j + 1) (by lia) (by lia)
      simpa [rootSlotInterval] using
        icc_inter_icc_nonempty_of_crossing hrf_step hrg_step hcross_fg hcross_gf

/-- **Sub-statement A of milestone B2: left-endpoint real-rootedness.**

For a nonnegative positive-combination pair `(f, g)` with positive leading
coefficients and `g.natDegree = f.natDegree + 1`, the lower-degree member `f`
splits over `ℝ`. This is the degree-drop root-continuity endpoint (`f` is the
`μ → 0⁺` limit of the real-rooted family `f + C μ * g`, whose `f.natDegree`
finite roots converge to the roots of `f` while one root escapes to `-∞`),
isolated here as a reusable statement. -/
def PosComboSuccDegreeLeftSplitsNonnegStatement : Prop :=
  ∀ ⦃f g : ℝ[X]⦄,
    HasPosLeadingCoeff f →
    HasPosLeadingCoeff g →
    HasNonnegCoeffs f →
    HasNonnegCoeffs g →
    PosComboRealRooted f g →
    g.natDegree = f.natDegree + 1 →
    f.Splits

/-- Residual form of the succ-degree left-endpoint problem after the algebraic
branches have been removed: the lower-degree polynomial has zero constant
coefficient, while the higher-degree polynomial does not. -/
def PosComboSuccDegreeResidualLeftSplitsNonnegStatement : Prop :=
  ∀ ⦃f g : ℝ[X]⦄,
    HasPosLeadingCoeff f →
    HasPosLeadingCoeff g →
    HasNonnegCoeffs f →
    HasNonnegCoeffs g →
    PosComboRealRooted f g →
    g.natDegree = f.natDegree + 1 →
    f.coeff 0 = 0 →
    g.coeff 0 ≠ 0 →
    f.Splits

/-- The succ-degree left endpoint follows directly from the escaping-root
continuity argument for the family `f + C μ * g`; no ASW input is needed. -/
theorem PosComboSuccDegreeLeftSplitsNonnegStatement_of_rootContinuity :
    PosComboSuccDegreeLeftSplitsNonnegStatement := by
  intro f g hf_pos hg_pos _ _ hfg hsucc
  exact
    splits_of_add_C_mul_family_of_succDegree
      (fun {μ} hμ => hfg.isRealRooted_add_right hμ) hf_pos hg_pos hsucc

/-- Residual succ-degree left endpoint from the same root-continuity argument. -/
theorem PosComboSuccDegreeResidualLeftSplitsNonnegStatement_of_rootContinuity :
    PosComboSuccDegreeResidualLeftSplitsNonnegStatement := by
  intro f g hf_pos hg_pos hfnn hgnn hfg hsucc _ _
  exact
    PosComboSuccDegreeLeftSplitsNonnegStatement_of_rootContinuity
      hf_pos hg_pos hfnn hgnn hfg hsucc

/-- The succ-degree left endpoint follows from the forward
Aissen--Schoenberg--Whitney theorem.  This gives an alternate classical route:
positive perturbations `f + μ g` are PF, and the PF Toeplitz minors are closed
under the coefficient limit `μ → 0⁺`. -/
theorem PosComboRealRooted.left_splits_of_forward_asw
    (hASW : aissenSchoenbergWhitneyForwardOrZeroStatement)
    {f g : ℝ[X]}
    (hfg : PosComboRealRooted f g)
    (hf_pos : HasPosLeadingCoeff f)
    (hfnn : HasNonnegCoeffs f) (hgnn : HasNonnegCoeffs g) :
    f.Splits :=
  IsPFPolynomial.splits_of_forall_pos_add_C_mul_of_forward
    hASW hf_pos.ne_zero hfnn hgnn
    fun {_} hμ => (hfg.isRealRooted_add_right hμ).2

/-- Conditional package form of `PosComboRealRooted.left_splits_of_forward_asw`
for the milestone-B2 endpoint statement. -/
theorem PosComboSuccDegreeLeftSplitsNonnegStatement_of_forward_asw
    (hASW : aissenSchoenbergWhitneyForwardOrZeroStatement) :
    PosComboSuccDegreeLeftSplitsNonnegStatement := by
  intro f g hf_pos _ hfnn hgnn hfg _
  exact hfg.left_splits_of_forward_asw hASW hf_pos hfnn hgnn

/-- Conditional package form using the splitting-only ASW target. -/
theorem PosComboSuccDegreeLeftSplitsNonnegStatement_of_forward_asw_splits
    (hASW : aissenSchoenbergWhitneyForwardSplitsStatement) :
    PosComboSuccDegreeLeftSplitsNonnegStatement :=
  PosComboSuccDegreeLeftSplitsNonnegStatement_of_forward_asw
    (aissenSchoenbergWhitneyForwardOrZero_of_splits hASW)

/-- Residual package form of the forward-ASW route.  This keeps the remaining
#42 branch available as a smaller challenge target, while making clear that the
PF-limit route already covers it under the forward ASW interface. -/
theorem PosComboSuccDegreeResidualLeftSplitsNonnegStatement_of_forward_asw
    (hASW : aissenSchoenbergWhitneyForwardOrZeroStatement) :
    PosComboSuccDegreeResidualLeftSplitsNonnegStatement := by
  intro f g hf_pos hg_pos hfnn hgnn hfg hsucc _ _
  exact (PosComboSuccDegreeLeftSplitsNonnegStatement_of_forward_asw hASW)
    hf_pos hg_pos hfnn hgnn hfg hsucc

/-- Residual package form using the splitting-only ASW target. -/
theorem PosComboSuccDegreeResidualLeftSplitsNonnegStatement_of_forward_asw_splits
    (hASW : aissenSchoenbergWhitneyForwardSplitsStatement) :
    PosComboSuccDegreeResidualLeftSplitsNonnegStatement :=
  PosComboSuccDegreeResidualLeftSplitsNonnegStatement_of_forward_asw
    (aissenSchoenbergWhitneyForwardOrZero_of_splits hASW)

/-- The affine-family bridge already gives the succ-degree left endpoint in
the no-common branch.  This isolates the remaining #42 work in that branch as
the affine-family/boundary-pair packaging step, not the endpoint
real-rootedness step. -/
theorem posComboNoCommonSuccDegreeLeftSplits_of_affineFamily
    (haffBridge : PosComboNoCommonAffineFamilyStatement)
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g)
    (hsucc : g.natDegree = f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    f.Splits := by
  have haff :
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        ((((C s * X + C t) * f) + g) ≠ 0 ∧
          (((C s * X + C t) * f) + g).Splits) :=
    fun {s t} hs ht =>
      haffBridge hf_pos hg_pos hfnn hgnn hfg (by lia) (by lia) hno hs ht
  exact
    (isRealRooted_left_of_affine_family_nonneg
      hf_pos.ne_zero hg_pos.ne_zero hfnn hgnn haff).2

/-- Boundary-right-pair orientation also contains the no-common succ-degree
left endpoint, because it first produces the affine-family bridge. -/
theorem posComboNoCommonSuccDegreeLeftSplits_of_boundaryRightPairOrientation
    (hboundary : PosComboNoCommonBoundaryRightPairOrientationStatement)
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g)
    (hsucc : g.natDegree = f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    f.Splits :=
  posComboNoCommonSuccDegreeLeftSplits_of_affineFamily
    (posComboNoCommonAffineFamily_of_boundaryRightPairOrientation hboundary)
    hf_pos hg_pos hfnn hgnn hfg hsucc hno

private theorem left_splits_of_succDegree_of_left_coeff_zero_ne_core
    {f g : ℝ[X]}
    (hfg : PosComboRealRooted f g)
    (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f) (hgnn : HasNonnegCoeffs g)
    (hsucc : g.natDegree = f.natDegree + 1)
    (hf0 : f.coeff 0 ≠ 0) :
    f.Splits := by
  let N := g.natDegree
  have hfN : f.natDegree ≤ N := by
    dsimp [N]
    lia
  have hgN : g.natDegree ≤ N := by simp [N]
  have hf0_pos : 0 < f.coeff 0 := lt_of_le_of_ne (hfnn 0) hf0.symm
  have hf_ref_pos : HasPosLeadingCoeff (reflect N f) := by
    unfold HasPosLeadingCoeff
    rw [DegreeDropReversal.leadingCoeff_reflect_eq_coeff_zero_of_natDegree_le hfN hf0]
    exact hf0_pos
  have hg_ref_nonneg : HasNonnegCoeffs (reflect N g) := by
    intro n
    simpa [Polynomial.coeff_reflect] using hgnn (revAt N n)
  have hg_ref_ne : reflect N g ≠ 0 := by
    intro hzero
    exact hg_pos.ne_zero (Polynomial.reflect_eq_zero_iff.mp hzero)
  have hg_ref_pos : HasPosLeadingCoeff (reflect N g) :=
    hg_ref_nonneg.pos_leadingCoeff hg_ref_ne
  have hfg_ref : PosComboRealRooted (reflect N f) (reflect N g) :=
    hfg.reflect_of_natDegree_le hfN hgN
  have hdeg_ref_le : (reflect N g).natDegree ≤ (reflect N f).natDegree := by
    rw [DegreeDropReversal.natDegree_reflect_eq_of_coeff_zero_ne hfN hf0]
    exact Polynomial.natDegree_reflect_le.trans <| by rw [max_eq_left hgN]
  have hreflect_rr :=
    PosComboRealRooted.isRealRooted_right_of_natDegree_le
      (PosComboRealRooted.comm hfg_ref) hg_ref_pos hf_ref_pos hdeg_ref_le
  exact (DegreeDropReversal.splits_reflect_iff (p := f) hfN).mp hreflect_rr.2

/-- Constant-term nonzero subcase of the degree-drop endpoint.  Reflection at
`g.natDegree` turns the succ-degree pair into an equal-degree pair, so the
same-degree positive-combination converse applies.  This two-sided interface is
kept for older call sites; it now specializes the stronger one-sided theorem
below. -/
theorem PosComboRealRooted.left_splits_of_succDegree_of_coeff_zero_ne
    {f g : ℝ[X]}
    (hfg : PosComboRealRooted f g)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f) (hgnn : HasNonnegCoeffs g)
    (hsucc : g.natDegree = f.natDegree + 1)
    (hf0 : f.coeff 0 ≠ 0) (hg0 : g.coeff 0 ≠ 0) :
    f.Splits := by
  have _ := hf_pos
  have _ := hg0
  exact left_splits_of_succDegree_of_left_coeff_zero_ne_core
    hfg hg_pos hfnn hgnn hsucc hf0

/-- If the lower-degree endpoint has nonzero constant coefficient, the
degree-drop endpoint follows by reflecting and applying the degree-`≤`
positive-combination closure to the reflected pair. -/
theorem PosComboRealRooted.left_splits_of_succDegree_of_left_coeff_zero_ne
    {f g : ℝ[X]}
    (hfg : PosComboRealRooted f g)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f) (hgnn : HasNonnegCoeffs g)
    (hsucc : g.natDegree = f.natDegree + 1)
    (hf0 : f.coeff 0 ≠ 0) :
    f.Splits := by
  have _ := hf_pos
  exact left_splits_of_succDegree_of_left_coeff_zero_ne_core
    hfg hg_pos hfnn hgnn hsucc hf0

private lemma natDegree_pos_of_posLeadingCoeff_of_coeff_zero
    {p : ℝ[X]} (hp_pos : HasPosLeadingCoeff p) (hp0 : p.coeff 0 = 0) :
    0 < p.natDegree := by
  by_contra hnot
  have hp_deg_zero : p.natDegree = 0 := Nat.eq_zero_of_not_pos hnot
  have hp_C : p = C (p.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hp_deg_zero
  exact hp_pos.ne_zero (by simpa [hp0] using hp_C)

/-- A no-common-roots pair cannot have zero constant coefficient on both
members.  This is the form used when the lower-degree endpoint has a factor
`X`: the higher-degree endpoint is automatically in the residual branch. -/
theorem right_coeff_zero_ne_of_no_common_of_left_coeff_zero
    {f g : ℝ[X]}
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hf0 : f.coeff 0 = 0) :
    g.coeff 0 ≠ 0 := by
  intro hg0
  have hf_root : f.IsRoot 0 := by
    simpa [Polynomial.IsRoot.def, Polynomial.coeff_zero_eq_eval_zero] using hf0
  have hg_root : g.IsRoot 0 := by
    simpa [Polynomial.IsRoot.def, Polynomial.coeff_zero_eq_eval_zero] using hg0
  exact (hno 0 hf_root) hg_root

/-- Symmetric constant-coefficient form of the no-common-roots hypothesis. -/
theorem left_coeff_zero_ne_of_no_common_of_right_coeff_zero
    {f g : ℝ[X]}
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hg0 : g.coeff 0 = 0) :
    f.coeff 0 ≠ 0 := by
  intro hf0
  exact right_coeff_zero_ne_of_no_common_of_left_coeff_zero hno hf0 hg0

/-- Zero-constant succ-degree data pass to the pair divided by the common
factor `X`.  This is the reduction package for the complementary branch to
`PosComboRealRooted.left_splits_of_succDegree_of_coeff_zero_ne`. -/
theorem PosComboRealRooted.divX_succDegree_data
    {f g : ℝ[X]}
    (hfg : PosComboRealRooted f g)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f) (hgnn : HasNonnegCoeffs g)
    (hsucc : g.natDegree = f.natDegree + 1)
    (hf0 : f.coeff 0 = 0) (hg0 : g.coeff 0 = 0) :
    HasPosLeadingCoeff f.divX ∧
      HasPosLeadingCoeff g.divX ∧
      HasNonnegCoeffs f.divX ∧
      HasNonnegCoeffs g.divX ∧
      PosComboRealRooted f.divX g.divX ∧
      g.divX.natDegree = f.divX.natDegree + 1 := by
  have hf_nat_pos := natDegree_pos_of_posLeadingCoeff_of_coeff_zero hf_pos hf0
  refine
    ⟨hf_pos.divX_of_coeff_zero hf0,
      hg_pos.divX_of_coeff_zero hg0,
      hfnn.divX,
      hgnn.divX,
      hfg.divX_of_coeff_zero hf0 hg0,
      ?_⟩
  rw [Polynomial.natDegree_divX_eq_natDegree_tsub_one,
    Polynomial.natDegree_divX_eq_natDegree_tsub_one]
  lia

/-- Single-polynomial `divX` root-count step.  For a nonzero polynomial with
zero constant coefficient, the number of roots satisfying any predicate `p`
equals the number for its `divX` quotient plus the contribution of the extra
root at `0`. -/
theorem card_roots_filter_divX_of_coeff_zero {f : ℝ[X]} (hf : f ≠ 0)
    (hf0 : f.coeff 0 = 0) (p : ℝ → Prop) [DecidablePred p] :
    (f.roots.filter p).card =
      (f.divX.roots.filter p).card + (if p 0 then 1 else 0) := by
  rw [roots_eq_zero_cons_divX_of_coeff_zero hf hf0, Multiset.filter_cons]
  by_cases h : p 0 <;>
    simp [h, Multiset.card_add, Multiset.card_singleton, add_comm]

/-- Common-`X`/`divX` root-count invariance step.  Dividing out the common
factor `X` from a pair of nonzero polynomials with zero constant coefficient
leaves the threshold root-count difference with respect to any predicate `p`
unchanged: the extra root at `0` is contributed to both counts and cancels. -/
theorem card_roots_filter_sub_divX_of_coeff_zero {f g : ℝ[X]}
    (hf : f ≠ 0) (hg : g ≠ 0) (hf0 : f.coeff 0 = 0) (hg0 : g.coeff 0 = 0)
    (p : ℝ → Prop) [DecidablePred p] :
    ((f.roots.filter p).card : ℤ) - (g.roots.filter p).card =
      ((f.divX.roots.filter p).card : ℤ) - (g.divX.roots.filter p).card := by
  rw [card_roots_filter_divX_of_coeff_zero hf hf0 p,
    card_roots_filter_divX_of_coeff_zero hg hg0 p]
  push_cast
  ring

/-- Lower-threshold same-cardinality count bounds lift across a common
zero constant term. -/
theorem rootCount_diff_le_one_of_divX_coeff_zero {f g : ℝ[X]}
    (hf : f ≠ 0) (hg : g ≠ 0) (hf0 : f.coeff 0 = 0) (hg0 : g.coeff 0 = 0)
    (hcount : ∀ x : ℝ,
      ((f.divX.roots.filter (· ≤ x)).card : ℤ) -
          (g.divX.roots.filter (· ≤ x)).card ≤ 1 ∧
      ((g.divX.roots.filter (· ≤ x)).card : ℤ) -
          (f.divX.roots.filter (· ≤ x)).card ≤ 1) :
    ∀ x : ℝ,
      ((f.roots.filter (· ≤ x)).card : ℤ) - (g.roots.filter (· ≤ x)).card ≤ 1 ∧
      ((g.roots.filter (· ≤ x)).card : ℤ) - (f.roots.filter (· ≤ x)).card ≤ 1 := by
  intro x
  have hfg := card_roots_filter_sub_divX_of_coeff_zero hf hg hf0 hg0 (fun y : ℝ => y ≤ x)
  have hgf := card_roots_filter_sub_divX_of_coeff_zero hg hf hg0 hf0 (fun y : ℝ => y ≤ x)
  constructor
  · rw [hfg]
    exact (hcount x).1
  · rw [hgf]
    exact (hcount x).2

/-- Upper-threshold same-cardinality count bounds lift across a common
zero constant term. -/
theorem rootCountAbove_diff_le_one_of_divX_coeff_zero {f g : ℝ[X]}
    (hf : f ≠ 0) (hg : g ≠ 0) (hf0 : f.coeff 0 = 0) (hg0 : g.coeff 0 = 0)
    (hcount : ∀ x : ℝ,
      ((f.divX.roots.filter (x < ·)).card : ℤ) -
          (g.divX.roots.filter (x < ·)).card ≤ 1 ∧
      ((g.divX.roots.filter (x < ·)).card : ℤ) -
          (f.divX.roots.filter (x < ·)).card ≤ 1) :
    ∀ x : ℝ,
      ((f.roots.filter (x < ·)).card : ℤ) - (g.roots.filter (x < ·)).card ≤ 1 ∧
      ((g.roots.filter (x < ·)).card : ℤ) - (f.roots.filter (x < ·)).card ≤ 1 := by
  intro x
  have hfg := card_roots_filter_sub_divX_of_coeff_zero hf hg hf0 hg0 (fun y : ℝ => x < y)
  have hgf := card_roots_filter_sub_divX_of_coeff_zero hg hf hg0 hf0 (fun y : ℝ => x < y)
  constructor
  · rw [hfg]
    exact (hcount x).1
  · rw [hgf]
    exact (hcount x).2

/-- Succ-degree lower-threshold count bounds lift across a common zero
constant term. -/
theorem succDegreeRootCount_of_divX_coeff_zero {f g : ℝ[X]}
    (hf : f ≠ 0) (hg : g ≠ 0) (hf0 : f.coeff 0 = 0) (hg0 : g.coeff 0 = 0)
    (hcount : ∀ x : ℝ,
      ((f.divX.roots.filter (· ≤ x)).card : ℤ) -
          (g.divX.roots.filter (· ≤ x)).card ≤ 0 ∧
      ((g.divX.roots.filter (· ≤ x)).card : ℤ) -
          (f.divX.roots.filter (· ≤ x)).card ≤ 2) :
    ∀ x : ℝ,
      ((f.roots.filter (· ≤ x)).card : ℤ) - (g.roots.filter (· ≤ x)).card ≤ 0 ∧
      ((g.roots.filter (· ≤ x)).card : ℤ) - (f.roots.filter (· ≤ x)).card ≤ 2 := by
  intro x
  have hfg := card_roots_filter_sub_divX_of_coeff_zero hf hg hf0 hg0 (fun y : ℝ => y ≤ x)
  have hgf := card_roots_filter_sub_divX_of_coeff_zero hg hf hg0 hf0 (fun y : ℝ => y ≤ x)
  constructor
  · rw [hfg]
    exact (hcount x).1
  · rw [hgf]
    exact (hcount x).2

/-- Succ-degree upper-threshold count bounds lift across a common zero
constant term. -/
theorem succDegreeRootCountAbove_of_divX_coeff_zero {f g : ℝ[X]}
    (hf : f ≠ 0) (hg : g ≠ 0) (hf0 : f.coeff 0 = 0) (hg0 : g.coeff 0 = 0)
    (hcount : ∀ x : ℝ,
      ((f.divX.roots.filter (x < ·)).card : ℤ) -
          (g.divX.roots.filter (x < ·)).card ≤ 1 ∧
      ((g.divX.roots.filter (x < ·)).card : ℤ) -
          (f.divX.roots.filter (x < ·)).card ≤ 1) :
    ∀ x : ℝ,
      ((f.roots.filter (x < ·)).card : ℤ) - (g.roots.filter (x < ·)).card ≤ 1 ∧
      ((g.roots.filter (x < ·)).card : ℤ) - (f.roots.filter (x < ·)).card ≤ 1 :=
  rootCountAbove_diff_le_one_of_divX_coeff_zero hf hg hf0 hg0 hcount

/-- The full succ-degree left-endpoint statement is reduced to the residual
branch `f.coeff 0 = 0`, `g.coeff 0 ≠ 0`.

The proof is a strong induction on `f.natDegree`.  If `f.coeff 0 ≠ 0`, the
reflection route applies.  If both constant coefficients vanish, divide both
polynomials by the common factor `X` and invoke the induction hypothesis. -/
theorem PosComboSuccDegreeLeftSplitsNonnegStatement_of_residual
    (hres : PosComboSuccDegreeResidualLeftSplitsNonnegStatement) :
    PosComboSuccDegreeLeftSplitsNonnegStatement := by
  intro f g hf_pos hg_pos hfnn hgnn hfg hsucc
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
          g.natDegree = f.natDegree + 1 →
          f.Splits)
      f.natDegree ?_ rfl hf_pos hg_pos hfnn hgnn hfg hsucc
  intro n ih f g hfdeg hf_pos hg_pos hfnn hgnn hfg hsucc
  by_cases hf0_ne : f.coeff 0 ≠ 0
  · exact
      hfg.left_splits_of_succDegree_of_left_coeff_zero_ne
        hf_pos hg_pos hfnn hgnn hsucc hf0_ne
  · have hf0 : f.coeff 0 = 0 := by
      by_contra hf0
      exact hf0_ne hf0
    by_cases hg0 : g.coeff 0 = 0
    · obtain ⟨hfdiv_pos, hgdiv_pos, hfdiv_nn, hgdiv_nn, hdiv_fg, hdiv_succ⟩ :=
        hfg.divX_succDegree_data hf_pos hg_pos hfnn hgnn hsucc hf0 hg0
      have hf_nat_pos := natDegree_pos_of_posLeadingCoeff_of_coeff_zero hf_pos hf0
      have hdiv_deg_lt : f.divX.natDegree < n := by
        rw [← hfdeg, Polynomial.natDegree_divX_eq_natDegree_tsub_one]
        lia
      have hdiv_splits : f.divX.Splits :=
        ih f.divX.natDegree hdiv_deg_lt rfl
          hfdiv_pos hgdiv_pos hfdiv_nn hgdiv_nn hdiv_fg hdiv_succ
      exact DegreeDropReversal.splits_of_divX_splits_of_coeff_zero hf0 hdiv_splits
    · exact hres hf_pos hg_pos hfnn hgnn hfg hsucc hf0 hg0

/-- The residual constant-term branch is exactly equivalent to the full
succ-degree left-endpoint statement: the reverse implication is just
specialization, while the forward implication is the strong-induction
constant-term reduction. -/
theorem PosComboSuccDegreeLeftSplitsNonnegStatement_iff_residual :
    PosComboSuccDegreeLeftSplitsNonnegStatement ↔
      PosComboSuccDegreeResidualLeftSplitsNonnegStatement := by
  constructor
  · intro h f g hf_pos hg_pos hfnn hgnn hfg hsucc _ _
    exact h hf_pos hg_pos hfnn hgnn hfg hsucc
  · exact PosComboSuccDegreeLeftSplitsNonnegStatement_of_residual

/-- Residual constant-term branch of the lower-threshold succ-degree no-common
root-count statement: the case `f.coeff 0 = 0` and hence `g.coeff 0 ≠ 0` by
the no-common hypothesis. -/
def PosComboNoCommonSuccDegreeRootCountResidualNonnegStatement : Prop :=
  ∀ ⦃f g : ℝ[X]⦄,
    HasPosLeadingCoeff f →
    HasPosLeadingCoeff g →
    HasNonnegCoeffs f →
    HasNonnegCoeffs g →
    PosComboRealRooted f g →
    g.natDegree = f.natDegree + 1 →
    (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
    f.Splits →
    f.coeff 0 = 0 →
    g.coeff 0 ≠ 0 →
    ∀ x : ℝ,
      ((f.roots.filter (· ≤ x)).card : ℤ) - (g.roots.filter (· ≤ x)).card ≤ 0 ∧
      ((g.roots.filter (· ≤ x)).card : ℤ) - (f.roots.filter (· ≤ x)).card ≤ 2

/-- Exact residual orientation target for the succ-degree branch: in the case
where the lower-degree polynomial has zero constant term but the higher-degree
polynomial does not, orient the original pair as `f ≺ g`. -/
def PosComboNoCommonSuccDegreeRootCountResidualPrecStatement : Prop :=
  ∀ ⦃f g : ℝ[X]⦄,
    HasPosLeadingCoeff f →
    HasPosLeadingCoeff g →
    HasNonnegCoeffs f →
    HasNonnegCoeffs g →
    PosComboRealRooted f g →
    g.natDegree = f.natDegree + 1 →
    (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
    f.Splits →
    f.coeff 0 = 0 →
    g.coeff 0 ≠ 0 →
    Prec f g

/-- Nonzero constant-term branch of the lower-threshold succ-degree no-common
root-count statement.  This is the root-count analogue of the reflection route
used for the succ-degree left endpoint. -/
def PosComboNoCommonSuccDegreeRootCountLeadNonnegStatement : Prop :=
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
    ∀ x : ℝ,
      ((f.roots.filter (· ≤ x)).card : ℤ) - (g.roots.filter (· ≤ x)).card ≤ 0 ∧
      ((g.roots.filter (· ≤ x)).card : ℤ) - (f.roots.filter (· ≤ x)).card ≤ 2

/-- Nonzero constant-term succ-degree root-count branch, further restricted to
the subcase where the higher-degree member also has nonzero constant term. -/
def PosComboNoCommonSuccDegreeRootCountLeadBothNonzeroNonnegStatement : Prop :=
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
    g.coeff 0 ≠ 0 →
    ∀ x : ℝ,
      ((f.roots.filter (· ≤ x)).card : ℤ) - (g.roots.filter (· ≤ x)).card ≤ 0 ∧
      ((g.roots.filter (· ≤ x)).card : ℤ) - (f.roots.filter (· ≤ x)).card ≤ 2

/-- Nonzero constant-term succ-degree root-count branch, further restricted to
the subcase where the higher-degree member has zero constant term. -/
def PosComboNoCommonSuccDegreeRootCountLeadRightZeroNonnegStatement : Prop :=
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
      ((f.roots.filter (· ≤ x)).card : ℤ) - (g.roots.filter (· ≤ x)).card ≤ 0 ∧
      ((g.roots.filter (· ≤ x)).card : ℤ) - (f.roots.filter (· ≤ x)).card ≤ 2

/-- Exact residual orientation target for the right-zero lead branch: after
removing the zero root from the higher-degree polynomial, orient the resulting
same-degree pair as `g.divX ≺ f`. -/
def PosComboNoCommonSuccDegreeRootCountLeadRightZeroDivXPrecStatement : Prop :=
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
    Prec (g.divX) f

/-- The right-zero `divX` orientation target follows from proving the original
succ-degree orientation `Prec f g` on this branch.  The degree-drop step is
isolated in `prec_divX_left_of_prec_of_hasNonnegCoeffs_coeff_zero`. -/
theorem posComboNoCommonSuccDegreeRootCountLeadRightZeroDivXPrec_of_precFG
    (hprecFG :
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
        Prec f g) :
    PosComboNoCommonSuccDegreeRootCountLeadRightZeroDivXPrecStatement := by
  intro f g hf_pos hg_pos hfnn hgnn hfg hdeg hno hf_split hf0 hg0
  exact prec_divX_left_of_prec_of_hasNonnegCoeffs_coeff_zero
    (hprecFG hf_pos hg_pos hfnn hgnn hfg hdeg hno hf_split hf0 hg0) hgnn hg0 hdeg

/-- Converse of `posComboNoCommonSuccDegreeRootCountLeadRightZeroDivXPrec_of_precFG`:
the sharper succ-degree orientation `Prec f g` on the right-zero lead branch
follows from the `divX` orientation target `Prec (g.divX) f`.  The degree-drop
reconstruction is isolated in
`prec_of_prec_divX_left_of_hasNonnegCoeffs_coeff_zero`.

Together with `posComboNoCommonSuccDegreeRootCountLeadRightZeroDivXPrec_of_precFG`
this shows that on the right-zero lead branch the sharper orientation target and
the `divX` orientation target are equivalent. -/
theorem posComboNoCommonSuccDegreeRootCountLeadRightZeroPrecFG_of_divX
    (hdivX : PosComboNoCommonSuccDegreeRootCountLeadRightZeroDivXPrecStatement) :
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
      Prec f g := by
  intro f g hf_pos hg_pos hfnn hgnn hfg hdeg hno hf_split hf0 hg0
  exact prec_of_prec_divX_left_of_hasNonnegCoeffs_coeff_zero
    (hdivX hf_pos hg_pos hfnn hgnn hfg hdeg hno hf_split hf0 hg0) hfnn hgnn hg0 hdeg

/-- On the right-zero lead branch, the sharper succ-degree orientation
`Prec f g` is equivalent to the `divX` orientation target `Prec (g.divX) f`. -/
theorem posComboNoCommonSuccDegreeRootCountLeadRightZeroPrecFG_iff_divXPrec :
    (∀ ⦃f g : ℝ[X]⦄,
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
        Prec f g) ↔
      PosComboNoCommonSuccDegreeRootCountLeadRightZeroDivXPrecStatement := by
  exact ⟨posComboNoCommonSuccDegreeRootCountLeadRightZeroDivXPrec_of_precFG,
    posComboNoCommonSuccDegreeRootCountLeadRightZeroPrecFG_of_divX⟩

/-- The lead root-count branch splits into the two possible constant-term
cases for the higher-degree member. -/
theorem posComboNoCommonSuccDegreeRootCountLead_of_bothNonzero_and_rightZero
    (hboth : PosComboNoCommonSuccDegreeRootCountLeadBothNonzeroNonnegStatement)
    (hright : PosComboNoCommonSuccDegreeRootCountLeadRightZeroNonnegStatement) :
    PosComboNoCommonSuccDegreeRootCountLeadNonnegStatement := by
  intro f g hf_pos hg_pos hfnn hgnn hfg hdeg hno hf_split hf0
  by_cases hg0 : g.coeff 0 = 0
  · exact hright hf_pos hg_pos hfnn hgnn hfg hdeg hno hf_split hf0 hg0
  · exact hboth hf_pos hg_pos hfnn hgnn hfg hdeg hno hf_split hf0 hg0

/-- `divX` reduction of the right-zero lead branch.

When `g.coeff 0 = 0`, the roots of `g` are the roots of `g.divX` together with
one extra root at `0`.  Thus the right-zero succ-degree lower root-count bounds
follow from the oriented same-degree lower count comparison of `g.divX` and
`f`. -/
theorem posComboNoCommonSuccDegreeRootCountLeadRightZero_of_divX_sameDegreeCount
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
          ((f.roots.filter (· ≤ x)).card : ℤ) ≤
              (g.divX.roots.filter (· ≤ x)).card ∧
          ((g.divX.roots.filter (· ≤ x)).card : ℤ) ≤
              (f.roots.filter (· ≤ x)).card + 1) :
    PosComboNoCommonSuccDegreeRootCountLeadRightZeroNonnegStatement := by
  intro f g hf_pos hg_pos hfnn hgnn hfg hdeg hno hf_split hf0 hg0 x
  have hg_ne : g ≠ 0 := hg_pos.ne_zero
  obtain ⟨hFH, hHF⟩ :=
    hcount hf_pos hg_pos hfnn hgnn hfg hdeg hno hf_split hf0 hg0 x
  by_cases h0 : (0 : ℝ) ≤ x
  · have hc : ((g.roots.filter (· ≤ x)).card : ℤ) =
        (g.divX.roots.filter (· ≤ x)).card + 1 := by
      have h := card_roots_filter_divX_of_coeff_zero hg_ne hg0 (· ≤ x)
      have h' : (g.roots.filter (· ≤ x)).card =
          (g.divX.roots.filter (· ≤ x)).card + 1 := by
        simpa [h0] using h
      exact_mod_cast h'
    exact ⟨by lia, by lia⟩
  · have hc : ((g.roots.filter (· ≤ x)).card : ℤ) =
        (g.divX.roots.filter (· ≤ x)).card := by
      have h := card_roots_filter_divX_of_coeff_zero hg_ne hg0 (· ≤ x)
      have h' : (g.roots.filter (· ≤ x)).card =
          (g.divX.roots.filter (· ≤ x)).card := by
        simpa [h0] using h
      exact_mod_cast h'
    exact ⟨by lia, by lia⟩

end RealRooted
