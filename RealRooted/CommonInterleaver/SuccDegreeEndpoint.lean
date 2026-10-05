/-
# Succ-degree slots and the left endpoint

Root-slot intersections for succ-degree crossings, left-endpoint
real-rootedness, and degree-drop root-count lemmas.
-/
import RealRooted.AffineFamily
import RealRooted.CommonInterleaver.AffineBoundary
import RealRooted.CommonInterleaver.IntervalLemmas
import RealRooted.AllCombo
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
  have hgetD : ∀ {rs : List ℝ} {i : ℕ} (hi : i < rs.length), rs.getD i 0 = rs[i] :=
    fun hi => by simp [hi]
  have hstep : ∀ {rs : List ℝ}, rs.Pairwise (· ≥ ·) → ∀ {i : ℕ} (hi : i + 1 < rs.length),
      rs[i + 1] ≤ rs[i] := fun hrs i hi => by
    simpa using get_le_get_of_pairwise_ge hrs
      (i := ⟨i, by lia⟩) (j := ⟨i + 1, hi⟩) (by simp [Fin.le_def])
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · rcases rg with _ | ⟨s, rg⟩
    · simp at hlen
    rcases rf with _ | ⟨r, rf⟩
    · exact ⟨s, by simp [rootSlotInterval]⟩
    · exact ⟨max r s, by simp [rootSlotInterval]⟩
  have hjg' : j ≠ rg.length := by lia
  by_cases hjn : j = rf.length
  · obtain ⟨l, r, rfl⟩ :=
      (List.eq_nil_or_concat' rf).resolve_left (by rintro rfl; simp at hjn; lia)
    simp only [List.length_append, List.length_singleton] at hjn hlen hjf
    subst hjn
    have hc := hc1 (l.length + 1) (by lia) (by simp)
    rw [hgetD (by lia), hgetD (by simp)] at hc
    refine ⟨rg[l.length + 1], ?_, ?_⟩
    · simpa [rootSlotInterval] using hc
    · simpa [rootSlotInterval, hj0.ne', hjg'] using hstep hrg (i := l.length) (by lia)
  · have hc₁ := hc1 j hj0 (by lia)
    have hc₂ := hc2 j hj0 (by lia)
    rw [hgetD (by lia), hgetD (by lia)] at hc₁ hc₂
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by lia⟩
    simpa [rootSlotInterval, hjn, hjg'] using
      icc_inter_icc_nonempty_of_crossing (hstep hrf (by lia)) (hstep hrg (by lia)) hc₂ hc₁

/-- The succ-degree left endpoint from the proved forward ASW theorem, with no
backend argument required from the caller. -/
theorem PosComboRealRooted.left_splits_of_asw
    {f g : ℝ[X]}
    (hfg : PosComboRealRooted f g)
    (hf_pos : HasPosLeadingCoeff f)
    (hfnn : HasNonnegCoeffs f) (hgnn : HasNonnegCoeffs g) :
    f.Splits :=
  IsPFPolynomial.splits_of_forall_pos_add_C_mul
    hf_pos.ne_zero hfnn hgnn
    fun {_} hμ => (hfg.isRealRooted_add_right hμ).2

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
  have hg_ref_nonneg : HasNonnegCoeffs (reflect N g) := hgnn.reflect N
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

end RealRooted
