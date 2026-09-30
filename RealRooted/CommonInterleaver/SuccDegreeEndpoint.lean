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
    PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement := by
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
real-rootedness of `f` is the left component of `StrictInterl f h`, and each root-slot
intersection is witnessed by the corresponding root of `h` through
`rootSlotInterval_inter_nonempty_of_commonInterleaver`.

Together with `succDegreePairHasCommonInterleaver_nonneg_of_slotData` this shows
the slot-data hypothesis is equivalent to the actual common-interleaver goal,
so the reduction to root slots loses nothing. -/
theorem posComboNoCommonSuccDegreeSlotData_of_pairHasCommonInterleaver
    (hstmt : PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement) :
    PosComboNoCommonSuccDegreeSlotDataNonnegStatement := by
  intro f g hf_pos hg_pos hfnn hgnn hfg hsucc hno
  obtain ⟨h, hfh, hgh⟩ := hstmt hf_pos hg_pos hfnn hgnn hfg hsucc hno
  refine ⟨hfh.1, ?_⟩
  intro j hj _ _
  have hjg' : j < g.natDegree + 1 := by lia
  exact rootSlotInterval_inter_nonempty_of_commonInterleaver hfh hgh j hj hjg'

/-- **The #42 slot-data reformulation is equivalent to the target.**

Combining `succDegreePairHasCommonInterleaver_nonneg_of_slotData` with its
converse `posComboNoCommonSuccDegreeSlotData_of_pairHasCommonInterleaver`, the
root-slot statement `PosComboNoCommonSuccDegreeSlotDataNonnegStatement` holds if
and only if the common-right-interleaver statement
`PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement` does. This
pins down the exact remaining content of milestone B2: proving the slot data is
neither stronger nor weaker than proving the interleaver goal directly. -/
theorem posComboNoCommonSuccDegreeSlotData_iff_pairHasCommonInterleaver :
    PosComboNoCommonSuccDegreeSlotDataNonnegStatement ↔
      PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement :=
  ⟨succDegreePairHasCommonInterleaver_nonneg_of_slotData,
    posComboNoCommonSuccDegreeSlotData_of_pairHasCommonInterleaver⟩

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

/-- The succ-degree left endpoint follows directly from the escaping-root
continuity argument for the family `f + C μ * g`; no ASW input is needed. -/
theorem PosComboSuccDegreeLeftSplitsNonnegStatement_of_rootContinuity :
    PosComboSuccDegreeLeftSplitsNonnegStatement := by
  intro f g hf_pos hg_pos _ _ hfg hsucc
  exact
    splits_of_add_C_mul_family_of_succDegree
      (fun {μ} hμ => hfg.isRealRooted_add_right hμ) hf_pos hg_pos hsucc

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
def PosComboNoCommonSuccDegreeRootCountResidualStrictInterlStatement : Prop :=
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
    StrictInterl f g

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
def PosComboNoCommonSuccDegreeRootCountLeadRightZeroDivXStrictInterlStatement : Prop :=
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
    StrictInterl (g.divX) f

/-- The right-zero `divX` orientation target follows from proving the original
succ-degree orientation `StrictInterl f g` on this branch.  The degree-drop step is
isolated in `strictInterl_divX_left_of_strictInterl_of_hasNonnegCoeffs_coeff_zero`. -/
theorem posComboNoCommonSuccDegreeRootCountLeadRightZeroDivXStrictInterl_of_strictInterlFG
    (hstrictInterlFG :
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
        StrictInterl f g) :
    PosComboNoCommonSuccDegreeRootCountLeadRightZeroDivXStrictInterlStatement := by
  intro f g hf_pos hg_pos hfnn hgnn hfg hdeg hno hf_split hf0 hg0
  exact strictInterl_divX_left_of_strictInterl_of_hasNonnegCoeffs_coeff_zero
    (hstrictInterlFG hf_pos hg_pos hfnn hgnn hfg hdeg hno hf_split hf0 hg0) hgnn hg0 hdeg

@[deprecated
  posComboNoCommonSuccDegreeRootCountLeadRightZeroDivXStrictInterl_of_strictInterlFG
  (since := "2026-09-18")]
alias posComboNoCommonSuccDegreeRootCountLeadRightZeroDivXPrec_of_precFG :=
  posComboNoCommonSuccDegreeRootCountLeadRightZeroDivXStrictInterl_of_strictInterlFG

/-- Converse of
`posComboNoCommonSuccDegreeRootCountLeadRightZeroDivXStrictInterl_of_strictInterlFG`:
the sharper succ-degree orientation `StrictInterl f g` on the right-zero lead branch
follows from the `divX` orientation target `StrictInterl (g.divX) f`.  The degree-drop
reconstruction is isolated in
`strictInterl_of_strictInterl_divX_left_of_hasNonnegCoeffs_coeff_zero`.

Together with
`posComboNoCommonSuccDegreeRootCountLeadRightZeroDivXStrictInterl_of_strictInterlFG`
this shows that on the right-zero lead branch the sharper orientation target and
the `divX` orientation target are equivalent. -/
theorem posComboNoCommonSuccDegreeRootCountLeadRightZeroStrictInterlFG_of_divX
    (hdivX : PosComboNoCommonSuccDegreeRootCountLeadRightZeroDivXStrictInterlStatement) :
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
      StrictInterl f g := by
  intro f g hf_pos hg_pos hfnn hgnn hfg hdeg hno hf_split hf0 hg0
  exact strictInterl_of_strictInterl_divX_left_of_hasNonnegCoeffs_coeff_zero
    (hdivX hf_pos hg_pos hfnn hgnn hfg hdeg hno hf_split hf0 hg0) hfnn hgnn hg0 hdeg

@[deprecated posComboNoCommonSuccDegreeRootCountLeadRightZeroStrictInterlFG_of_divX
  (since := "2026-09-18")]
alias posComboNoCommonSuccDegreeRootCountLeadRightZeroPrecFG_of_divX :=
  posComboNoCommonSuccDegreeRootCountLeadRightZeroStrictInterlFG_of_divX

/-- On the right-zero lead branch, the sharper succ-degree orientation
`StrictInterl f g` is equivalent to the `divX` orientation target `StrictInterl (g.divX) f`. -/
theorem posComboNoCommonSuccDegreeRootCountLeadRightZeroStrictInterlFG_iff_divXStrictInterl :
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
        StrictInterl f g) ↔
      PosComboNoCommonSuccDegreeRootCountLeadRightZeroDivXStrictInterlStatement := by
  exact
    ⟨posComboNoCommonSuccDegreeRootCountLeadRightZeroDivXStrictInterl_of_strictInterlFG,
      posComboNoCommonSuccDegreeRootCountLeadRightZeroStrictInterlFG_of_divX⟩

@[deprecated
  posComboNoCommonSuccDegreeRootCountLeadRightZeroStrictInterlFG_iff_divXStrictInterl
  (since := "2026-09-18")]
alias posComboNoCommonSuccDegreeRootCountLeadRightZeroPrecFG_iff_divXPrec :=
  posComboNoCommonSuccDegreeRootCountLeadRightZeroStrictInterlFG_iff_divXStrictInterl

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
