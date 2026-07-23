import RealRooted.Basic
import RealRooted.Linear

/-!
# Liu opposite-sign compatibility scaffolding

This file packages the root deletion operation used in Lily L. Liu's
opposite-leading-sign compatibility criterion.  If `r` is the largest root of
`p`, the relevant polynomial is `p /ₘ (X - C r)`.
-/

open Polynomial

noncomputable section

namespace RealRooted
namespace LiuOppositeSigns

/-- A certificate that `r` is a rightmost root of `p`, with roots counted in
`p.roots`. -/
structure IsLargestRoot (p : ℝ[X]) (r : ℝ) : Prop where
  isRoot : p.IsRoot r
  roots_le : ∀ s ∈ p.roots, s ≤ r

/-- Delete one copy of the root `r` from `p` by monic division.  The companion
lemmas below assume that `r` is a largest root when that information matters. -/
def deleteRootFactor (p : ℝ[X]) (r : ℝ) : ℝ[X] :=
  p /ₘ (X - C r)

/-- Liu's count `n_p(x)`: roots in `[x, ∞)`, counted with multiplicity. -/
def rootCountAtOrAbove (p : ℝ[X]) (x : ℝ) : ℕ :=
  (p.roots.filter (fun r => x ≤ r)).card

/-- Liu's root-count compatibility condition `|n_p(x) - n_q(x)| <= 1`. -/
def RootCountCompatible (p q : ℝ[X]) : Prop :=
  ∀ x : ℝ,
    |((rootCountAtOrAbove p x : ℤ) - (rootCountAtOrAbove q x : ℤ))| ≤ 1

@[simp] theorem rootCountAtOrAbove_comp_X_add_C (p : ℝ[X]) (r x : ℝ) :
    rootCountAtOrAbove (p.comp (X + C r)) x = rootCountAtOrAbove p (x + r) := by
  rw [rootCountAtOrAbove, rootCountAtOrAbove, roots_comp_X_add_C]
  rw [Multiset.filter_map, Multiset.card_map]
  congr 1
  apply Multiset.filter_congr
  intro y _hy
  constructor
  · intro h
    dsimp at h
    linarith
  · intro h
    dsimp
    linarith

theorem RootCountCompatible.refl (p : ℝ[X]) : RootCountCompatible p p := by
  intro x
  simp

theorem RootCountCompatible.comp_X_add_C {p q : ℝ[X]}
    (h : RootCountCompatible p q) (r : ℝ) :
    RootCountCompatible (p.comp (X + C r)) (q.comp (X + C r)) := by
  intro x
  rw [rootCountAtOrAbove_comp_X_add_C p r x,
    rootCountAtOrAbove_comp_X_add_C q r x]
  exact h (x + r)

theorem RootCountCompatible.symm {p q : ℝ[X]} (h : RootCountCompatible p q) :
    RootCountCompatible q p := by
  intro x
  simpa [RootCountCompatible, abs_sub_comm] using h x

theorem RootCountCompatible.left_sub_le_one {p q : ℝ[X]}
    (h : RootCountCompatible p q) (x : ℝ) :
    ((rootCountAtOrAbove p x : ℤ) - (rootCountAtOrAbove q x : ℤ)) ≤ 1 := by
  have hx := h x
  rw [abs_le] at hx
  exact hx.2

theorem RootCountCompatible.right_sub_le_one {p q : ℝ[X]}
    (h : RootCountCompatible p q) (x : ℝ) :
    ((rootCountAtOrAbove q x : ℤ) - (rootCountAtOrAbove p x : ℤ)) ≤ 1 :=
  h.symm.left_sub_le_one x

theorem RootCountCompatible.bounds {p q : ℝ[X]}
    (h : RootCountCompatible p q) (x : ℝ) :
    ((rootCountAtOrAbove p x : ℤ) - (rootCountAtOrAbove q x : ℤ)) ≤ 1 ∧
      ((rootCountAtOrAbove q x : ℤ) - (rootCountAtOrAbove p x : ℤ)) ≤ 1 :=
  ⟨h.left_sub_le_one x, h.right_sub_le_one x⟩

@[simp] theorem rootCountAtOrAbove_neg (p : ℝ[X]) (x : ℝ) :
    rootCountAtOrAbove (-p) x = rootCountAtOrAbove p x := by
  simp [rootCountAtOrAbove, Polynomial.roots_neg]

@[simp] theorem isRoot_neg_iff (p : ℝ[X]) (x : ℝ) :
    (-p).IsRoot x ↔ p.IsRoot x := by
  simp [Polynomial.IsRoot.def]

@[simp] theorem rootCountAbove_neg (p : ℝ[X]) (x : ℝ) :
    ((-p).roots.filter (x < ·)).card = (p.roots.filter (x < ·)).card := by
  simp [Polynomial.roots_neg]

theorem RootCountCompatible.neg_left {p q : ℝ[X]}
    (h : RootCountCompatible p q) :
    RootCountCompatible (-p) q := by
  intro x
  simpa using h x

theorem RootCountCompatible.neg_right {p q : ℝ[X]}
    (h : RootCountCompatible p q) :
    RootCountCompatible p (-q) := by
  intro x
  simpa using h x

theorem RootCountCompatible.neg {p q : ℝ[X]} (h : RootCountCompatible p q) :
    RootCountCompatible (-p) (-q) :=
  h.neg_left.neg_right

theorem rootCountAtOrAbove_eq_card_of_forall_le_roots {p : ℝ[X]} {x : ℝ}
    (h : ∀ r ∈ p.roots, x ≤ r) :
    rootCountAtOrAbove p x = p.roots.card := by
  have hfilter : p.roots.filter (fun r => x ≤ r) = p.roots :=
    Multiset.filter_eq_self.mpr h
  simp [rootCountAtOrAbove, hfilter]

theorem exists_root_lower_bound (p : ℝ[X]) :
    ∃ c, ∀ r ∈ p.roots, c ≤ r := by
  classical
  let S := p.roots.toFinset
  by_cases hS : S.Nonempty
  · refine ⟨S.min' hS, ?_⟩
    intro r hr
    exact Finset.min'_le S r (Multiset.mem_toFinset.mpr hr)
  · refine ⟨0, ?_⟩
    intro r hr
    exact False.elim (hS ⟨r, Multiset.mem_toFinset.mpr hr⟩)

theorem exists_common_root_lower_bound (p q : ℝ[X]) :
    ∃ c, (∀ r ∈ p.roots, c ≤ r) ∧ ∀ s ∈ q.roots, c ≤ s := by
  obtain ⟨cp, hp⟩ := exists_root_lower_bound p
  obtain ⟨cq, hq⟩ := exists_root_lower_bound q
  refine ⟨min cp cq, ?_, ?_⟩
  · intro r hr
    exact (min_le_left cp cq).trans (hp r hr)
  · intro s hs
    exact (min_le_right cp cq).trans (hq s hs)

theorem RootCountCompatible.natDegree_abs_sub_le_one {p q : ℝ[X]}
    (h : RootCountCompatible p q) (hp_splits : p.Splits) (hq_splits : q.Splits) :
    |((p.natDegree : ℤ) - (q.natDegree : ℤ))| ≤ 1 := by
  obtain ⟨x, hpx, hqx⟩ := exists_common_root_lower_bound p q
  have hp_count : rootCountAtOrAbove p x = p.roots.card :=
    rootCountAtOrAbove_eq_card_of_forall_le_roots hpx
  have hq_count : rootCountAtOrAbove q x = q.roots.card :=
    rootCountAtOrAbove_eq_card_of_forall_le_roots hqx
  have hgap := h x
  rw [hp_count, hq_count, card_roots_of_splits hp_splits,
    card_roots_of_splits hq_splits] at hgap
  exact hgap

/-- The leading coefficients have opposite signs. -/
def OppositeLeadingSigns (p q : ℝ[X]) : Prop :=
  p.leadingCoeff * q.leadingCoeff < 0

theorem OppositeLeadingSigns.symm {p q : ℝ[X]} (h : OppositeLeadingSigns p q) :
    OppositeLeadingSigns q p := by
  simpa [OppositeLeadingSigns, mul_comm] using h

theorem OppositeLeadingSigns.left_ne_zero {p q : ℝ[X]}
    (h : OppositeLeadingSigns p q) :
    p ≠ 0 := by
  have hmul : p.leadingCoeff * q.leadingCoeff ≠ 0 := ne_of_lt h
  exact leadingCoeff_ne_zero.mp (mul_ne_zero_iff.mp hmul).1

theorem OppositeLeadingSigns.right_ne_zero {p q : ℝ[X]}
    (h : OppositeLeadingSigns p q) :
    q ≠ 0 :=
  h.symm.left_ne_zero

theorem OppositeLeadingSigns.pos_neg_or_neg_pos {p q : ℝ[X]}
    (h : OppositeLeadingSigns p q) :
    (HasPosLeadingCoeff p ∧ HasPosLeadingCoeff (-q)) ∨
      (HasPosLeadingCoeff (-p) ∧ HasPosLeadingCoeff q) := by
  have hmul : p.leadingCoeff * q.leadingCoeff < 0 := h
  have hp_lc_ne : p.leadingCoeff ≠ 0 := (mul_ne_zero_iff.mp (ne_of_lt hmul)).1
  rcases lt_or_gt_of_ne hp_lc_ne with hp_neg | hp_pos
  · have hq_pos : 0 < q.leadingCoeff := by
      by_contra hq_not
      have hq_nonpos : q.leadingCoeff ≤ 0 := le_of_not_gt hq_not
      have hprod_nonneg : 0 ≤ p.leadingCoeff * q.leadingCoeff :=
        mul_nonneg_of_nonpos_of_nonpos (le_of_lt hp_neg) hq_nonpos
      linarith
    exact Or.inr ⟨hasPosLeadingCoeff_neg hp_neg, hq_pos⟩
  · have hq_neg : q.leadingCoeff < 0 := by
      by_contra hq_not
      have hq_nonneg : 0 ≤ q.leadingCoeff := le_of_not_gt hq_not
      have hprod_nonneg : 0 ≤ p.leadingCoeff * q.leadingCoeff :=
        mul_nonneg (le_of_lt hp_pos) hq_nonneg
      linarith
    exact Or.inl ⟨hp_pos, hasPosLeadingCoeff_neg hq_neg⟩

theorem natDegree_deleteRootFactor (p : ℝ[X]) (r : ℝ) :
    (deleteRootFactor p r).natDegree = p.natDegree - 1 := by
  rw [deleteRootFactor,
    Polynomial.natDegree_divByMonic p (Polynomial.monic_X_sub_C r),
    Polynomial.natDegree_X_sub_C]

theorem exists_isLargestRoot {p : ℝ[X]} (hp_ne : p ≠ 0) (hp_splits : p.Splits)
    (hdeg : 1 ≤ p.natDegree) :
    ∃ r, IsLargestRoot p r := by
  rcases exists_rightmost_root_of_isRealRooted hp_ne hp_splits hdeg with
    ⟨r, hr, hle⟩
  exact ⟨r, ⟨hr, hle⟩⟩

theorem exists_largestRoots {f g : ℝ[X]}
    (hf_splits : f.Splits) (hg_splits : g.Splits)
    (hsgn : OppositeLeadingSigns f g)
    (hf_deg : f.natDegree ≠ 0) (hg_deg : g.natDegree ≠ 0) :
    ∃ r s, IsLargestRoot f r ∧ IsLargestRoot g s := by
  obtain ⟨r, hr⟩ :=
    exists_isLargestRoot hsgn.left_ne_zero hf_splits
      (Nat.pos_of_ne_zero hf_deg)
  obtain ⟨s, hs⟩ :=
    exists_isLargestRoot hsgn.right_ne_zero hg_splits
      (Nat.pos_of_ne_zero hg_deg)
  exact ⟨r, s, hr, hs⟩

theorem natDegree_pos_of_isRoot {p : ℝ[X]} {r : ℝ} (hp_ne : p ≠ 0)
    (hr : p.IsRoot r) :
    0 < p.natDegree :=
  Polynomial.natDegree_pos_iff_degree_pos.mpr <|
    Polynomial.degree_pos_of_root hp_ne hr

theorem factor_deleteRootFactor_of_isRoot {p : ℝ[X]} {r : ℝ}
    (hr : p.IsRoot r) :
    (X - C r) * deleteRootFactor p r = p := by
  simpa [deleteRootFactor] using
    (Polynomial.mul_divByMonic_eq_iff_isRoot (p := p) (a := r)).mpr hr

theorem comp_X_add_C_eq_X_mul_deleteRootFactor_comp_of_isRoot
    {p : ℝ[X]} {r : ℝ} (hr : p.IsRoot r) :
    p.comp (X + C r) =
      X * (deleteRootFactor p r).comp (X + C r) := by
  conv_lhs => rw [← factor_deleteRootFactor_of_isRoot hr]
  simp [mul_comp, X_comp, C_comp, sub_eq_add_neg, add_assoc, add_comm]

theorem deleteRootFactor_ne_zero_of_isRoot {p : ℝ[X]} {r : ℝ}
    (hp_ne : p ≠ 0) (hr : p.IsRoot r) :
    deleteRootFactor p r ≠ 0 := by
  intro hzero
  apply hp_ne
  rw [← factor_deleteRootFactor_of_isRoot hr, hzero, mul_zero]

theorem roots_eq_singleton_add_roots_deleteRootFactor_of_isRoot
    {p : ℝ[X]} {r : ℝ} (hp_ne : p ≠ 0) (hr : p.IsRoot r) :
    p.roots = {r} + (deleteRootFactor p r).roots := by
  have hfactor := factor_deleteRootFactor_of_isRoot hr
  have hprod_ne : (X - C r) * deleteRootFactor p r ≠ 0 := by
    intro hzero
    exact hp_ne (by rw [← hfactor, hzero])
  calc
    p.roots = ((X - C r) * deleteRootFactor p r).roots := by rw [hfactor]
    _ = (X - C r).roots + (deleteRootFactor p r).roots :=
      Polynomial.roots_mul hprod_ne
    _ = {r} + (deleteRootFactor p r).roots := by simp

theorem rootCountAtOrAbove_deleteRootFactor_add_one_of_isRoot
    {p : ℝ[X]} {r x : ℝ} (hp_ne : p ≠ 0) (hr : p.IsRoot r)
    (hx : x ≤ r) :
    rootCountAtOrAbove p x =
      rootCountAtOrAbove (deleteRootFactor p r) x + 1 := by
  rw [rootCountAtOrAbove, rootCountAtOrAbove,
    roots_eq_singleton_add_roots_deleteRootFactor_of_isRoot hp_ne hr]
  simp [hx, Nat.add_comm]

theorem rootCountAtOrAbove_eq_zero_of_forall_roots_lt {p : ℝ[X]} {x : ℝ}
    (h : ∀ r ∈ p.roots, r < x) :
    rootCountAtOrAbove p x = 0 := by
  have hfilter : p.roots.filter (fun r => x ≤ r) = 0 := by
    apply Multiset.filter_eq_nil.mpr
    intro r hr
    exact not_le.mpr (h r hr)
  simp [rootCountAtOrAbove, hfilter]

theorem rootCountAtOrAbove_eq_rootCountAbove_of_not_isRoot
    {p : ℝ[X]} (hp_ne : p ≠ 0) {x : ℝ} (hx : ¬ p.IsRoot x) :
    rootCountAtOrAbove p x = (p.roots.filter (x < ·)).card := by
  have hfilter : p.roots.filter (fun r => x ≤ r) = p.roots.filter (x < ·) := by
    apply Multiset.filter_congr
    intro r hr
    constructor
    · intro hxr
      exact lt_of_le_of_ne hxr fun hx_eq => hx (by
        have hr_root : p.IsRoot r := (Polynomial.mem_roots hp_ne).mp hr
        simpa [hx_eq] using hr_root)
    · intro hxr
      exact le_of_lt hxr
  simp [rootCountAtOrAbove, hfilter]

theorem RootCountCompatible.rootCountAbove_abs_sub_le_one_of_nonRoot
    {p q : ℝ[X]} (h : RootCountCompatible p q)
    (hp_ne : p ≠ 0) (hq_ne : q ≠ 0) {x : ℝ}
    (hpx : ¬ p.IsRoot x) (hqx : ¬ q.IsRoot x) :
    |(((p.roots.filter (x < ·)).card : ℤ) -
        ((q.roots.filter (x < ·)).card : ℤ))| ≤ 1 := by
  rw [← rootCountAtOrAbove_eq_rootCountAbove_of_not_isRoot hp_ne hpx,
    ← rootCountAtOrAbove_eq_rootCountAbove_of_not_isRoot hq_ne hqx]
  exact h x

theorem RootCountCompatible.rootCountAbove_bounds_of_nonRoot
    {p q : ℝ[X]} (h : RootCountCompatible p q)
    (hp_ne : p ≠ 0) (hq_ne : q ≠ 0) {x : ℝ}
    (hpx : ¬ p.IsRoot x) (hqx : ¬ q.IsRoot x) :
    ((p.roots.filter (x < ·)).card : ℤ) -
        (q.roots.filter (x < ·)).card ≤ 1 ∧
      ((q.roots.filter (x < ·)).card : ℤ) -
        (p.roots.filter (x < ·)).card ≤ 1 := by
  have hx := h.rootCountAbove_abs_sub_le_one_of_nonRoot hp_ne hq_ne hpx hqx
  rw [abs_le] at hx
  exact ⟨hx.2, by linarith [hx.1]⟩

/-- Move a real threshold strictly downward without crossing any element of a
finite multiset. -/
theorem exists_threshold_no_mem_Ico_left (s : Multiset ℝ) (x : ℝ) :
    ∃ x' : ℝ, x' < x ∧ ∀ r ∈ s, r < x' ∨ x ≤ r := by
  classical
  set S : Finset ℝ := s.toFinset.filter (· < x) with hS
  by_cases hSne : S.Nonempty
  · set m : ℝ := S.max' hSne with hm
    have hmS : m ∈ S := Finset.max'_mem S hSne
    have hmx : m < x := by
      exact (Finset.mem_filter.mp hmS).2
    refine ⟨(m + x) / 2, by linarith, ?_⟩
    intro r hr
    by_cases hrx : r < x
    · left
      have hrS : r ∈ S := by
        rw [hS, Finset.mem_filter]
        exact ⟨Multiset.mem_toFinset.mpr hr, hrx⟩
      have hrm : r ≤ m := Finset.le_max' S r hrS
      linarith
    · right
      exact le_of_not_gt hrx
  · rw [Finset.not_nonempty_iff_eq_empty] at hSne
    have hall : ∀ r ∈ s, ¬ r < x := by
      intro r hr hrx
      have : r ∈ S := by
        rw [hS, Finset.mem_filter]
        exact ⟨Multiset.mem_toFinset.mpr hr, hrx⟩
      rw [hSne] at this
      exact absurd this (Finset.notMem_empty r)
    refine ⟨x - 1, by linarith, ?_⟩
    intro r hr
    right
    exact le_of_not_gt (hall r hr)

/-- Push a threshold down to a common non-root so that strict-upper root counts
there equal Liu's closed-at-or-above counts at the original threshold. -/
theorem exists_nonRoot_threshold_count_gt_eq_rootCountAtOrAbove
    {p q : ℝ[X]} (hp_ne : p ≠ 0) (hq_ne : q ≠ 0) (x : ℝ) :
    ∃ x' : ℝ, x' < x ∧ ¬ p.IsRoot x' ∧ ¬ q.IsRoot x' ∧
      (p.roots.filter (x' < ·)).card = rootCountAtOrAbove p x ∧
      (q.roots.filter (x' < ·)).card = rootCountAtOrAbove q x := by
  classical
  set combined : Multiset ℝ := p.roots + q.roots with hcombined
  have hmem_combined : ∀ {r : ℝ}, r ∈ p.roots ∨ r ∈ q.roots → r ∈ combined := by
    intro r hr
    rw [hcombined, Multiset.mem_add]
    exact hr
  obtain ⟨x', hx'_lt, hgap⟩ := exists_threshold_no_mem_Ico_left combined x
  refine ⟨x', hx'_lt, ?_, ?_, ?_, ?_⟩
  · intro hxroot
    have hxmem : x' ∈ p.roots := (Polynomial.mem_roots hp_ne).mpr hxroot
    rcases hgap x' (hmem_combined (Or.inl hxmem)) with hx' | hx' <;> linarith
  · intro hxroot
    have hxmem : x' ∈ q.roots := (Polynomial.mem_roots hq_ne).mpr hxroot
    rcases hgap x' (hmem_combined (Or.inr hxmem)) with hx' | hx' <;> linarith
  · have hfilter :
        p.roots.filter (x' < ·) = p.roots.filter (fun r => x ≤ r) := by
      apply Multiset.filter_congr
      intro r hr
      constructor
      · intro hx'r
        rcases hgap r (hmem_combined (Or.inl hr)) with hrx' | hxr
        · linarith
        · exact hxr
      · intro hxr
        exact lt_of_lt_of_le hx'_lt hxr
    simp [rootCountAtOrAbove, hfilter]
  · have hfilter :
        q.roots.filter (x' < ·) = q.roots.filter (fun r => x ≤ r) := by
      apply Multiset.filter_congr
      intro r hr
      constructor
      · intro hx'r
        rcases hgap r (hmem_combined (Or.inr hr)) with hrx' | hxr
        · linarith
        · exact hxr
      · intro hxr
        exact lt_of_lt_of_le hx'_lt hxr
    simp [rootCountAtOrAbove, hfilter]

theorem RootCountCompatible.of_rootCountAbove_bounds_of_nonRoot
    {p q : ℝ[X]} (hp_ne : p ≠ 0) (hq_ne : q ≠ 0)
    (hbound : ∀ x : ℝ, ¬ p.IsRoot x → ¬ q.IsRoot x →
      ((p.roots.filter (x < ·)).card : ℤ) -
          (q.roots.filter (x < ·)).card ≤ 1 ∧
        ((q.roots.filter (x < ·)).card : ℤ) -
          (p.roots.filter (x < ·)).card ≤ 1) :
    RootCountCompatible p q := by
  intro x
  obtain ⟨x', _, hpx', hqx', hpcount, hqcount⟩ :=
    exists_nonRoot_threshold_count_gt_eq_rootCountAtOrAbove hp_ne hq_ne x
  have hxbound := hbound x' hpx' hqx'
  have hxabs :
      |(((p.roots.filter (x' < ·)).card : ℤ) -
          ((q.roots.filter (x' < ·)).card : ℤ))| ≤ 1 := by
    rw [abs_le]
    exact ⟨by linarith [hxbound.2], hxbound.1⟩
  rwa [hpcount, hqcount] at hxabs

/-- A normalized positive-leading, split pair equipped with Liu's root-count
compatibility condition. -/
structure PositiveSplitRootCountPair (p q : ℝ[X]) : Prop where
  left_pos : HasPosLeadingCoeff p
  right_pos : HasPosLeadingCoeff q
  left_splits : p.Splits
  right_splits : q.Splits
  count : RootCountCompatible p q

namespace PositiveSplitRootCountPair

theorem comp_X_add_C {p q : ℝ[X]} (h : PositiveSplitRootCountPair p q) (r : ℝ) :
    PositiveSplitRootCountPair (p.comp (X + C r)) (q.comp (X + C r)) :=
  ⟨h.left_pos.comp_X_add_C r, h.right_pos.comp_X_add_C r,
    (isRealRooted_comp_X_add_C h.left_pos.ne_zero h.left_splits r).2,
    (isRealRooted_comp_X_add_C h.right_pos.ne_zero h.right_splits r).2,
    h.count.comp_X_add_C r⟩

theorem symm {p q : ℝ[X]} (h : PositiveSplitRootCountPair p q) :
    PositiveSplitRootCountPair q p :=
  ⟨h.right_pos, h.left_pos, h.right_splits, h.left_splits, h.count.symm⟩

theorem of_rootCountAbove_bounds_of_nonRoot {p q : ℝ[X]}
    (hp_pos : HasPosLeadingCoeff p) (hq_pos : HasPosLeadingCoeff q)
    (hp_splits : p.Splits) (hq_splits : q.Splits)
    (hbound : ∀ x : ℝ, ¬ p.IsRoot x → ¬ q.IsRoot x →
      ((p.roots.filter (x < ·)).card : ℤ) -
          (q.roots.filter (x < ·)).card ≤ 1 ∧
        ((q.roots.filter (x < ·)).card : ℤ) -
          (p.roots.filter (x < ·)).card ≤ 1) :
    PositiveSplitRootCountPair p q :=
  ⟨hp_pos, hq_pos, hp_splits, hq_splits,
    RootCountCompatible.of_rootCountAbove_bounds_of_nonRoot
      hp_pos.ne_zero hq_pos.ne_zero hbound⟩

theorem natDegree_abs_sub_le_one {p q : ℝ[X]}
    (h : PositiveSplitRootCountPair p q) :
    |((p.natDegree : ℤ) - (q.natDegree : ℤ))| ≤ 1 :=
  h.count.natDegree_abs_sub_le_one h.left_splits h.right_splits

theorem rootCountAbove_bounds_of_nonRoot {p q : ℝ[X]}
    (h : PositiveSplitRootCountPair p q) {x : ℝ}
    (hpx : ¬ p.IsRoot x) (hqx : ¬ q.IsRoot x) :
    ((p.roots.filter (x < ·)).card : ℤ) -
        (q.roots.filter (x < ·)).card ≤ 1 ∧
      ((q.roots.filter (x < ·)).card : ℤ) -
        (p.roots.filter (x < ·)).card ≤ 1 :=
  h.count.rootCountAbove_bounds_of_nonRoot
    h.left_pos.ne_zero h.right_pos.ne_zero hpx hqx

theorem sameDegreeRootCountAboveNonRoot {p q : ℝ[X]}
    (h : PositiveSplitRootCountPair p q)
    (_hdeg : q.natDegree = p.natDegree) :
    ∀ x : ℝ, ¬ p.IsRoot x → ¬ q.IsRoot x →
      ((p.roots.filter (x < ·)).card : ℤ) -
          (q.roots.filter (x < ·)).card ≤ 1 ∧
        ((q.roots.filter (x < ·)).card : ℤ) -
          (p.roots.filter (x < ·)).card ≤ 1 :=
  fun _ hpx hqx => h.rootCountAbove_bounds_of_nonRoot hpx hqx

theorem succDegreeRootCountAboveNonRoot {p q : ℝ[X]}
    (h : PositiveSplitRootCountPair p q)
    (_hdeg : q.natDegree = p.natDegree + 1) :
    ∀ x : ℝ, ¬ p.IsRoot x → ¬ q.IsRoot x →
      ((p.roots.filter (x < ·)).card : ℤ) -
          (q.roots.filter (x < ·)).card ≤ 1 ∧
        ((q.roots.filter (x < ·)).card : ℤ) -
          (p.roots.filter (x < ·)).card ≤ 1 :=
  fun _ hpx hqx => h.rootCountAbove_bounds_of_nonRoot hpx hqx

end PositiveSplitRootCountPair

theorem deleteRootFactor_splits_of_isRoot {p : ℝ[X]} {r : ℝ}
    (hp_splits : p.Splits) (hr : p.IsRoot r) :
    (deleteRootFactor p r).Splits := by
  have hsplit_factor : ((X - C r) * deleteRootFactor p r).Splits := by
    simpa [factor_deleteRootFactor_of_isRoot hr] using hp_splits
  exact Polynomial.splits_X_sub_C_mul_iff.mp hsplit_factor

theorem deleteRootFactor_ne_zero_and_splits_of_isRoot {p : ℝ[X]} {r : ℝ}
    (hp_ne : p ≠ 0) (hp_splits : p.Splits) (hr : p.IsRoot r) :
    deleteRootFactor p r ≠ 0 ∧ (deleteRootFactor p r).Splits :=
  ⟨deleteRootFactor_ne_zero_of_isRoot hp_ne hr,
    deleteRootFactor_splits_of_isRoot hp_splits hr⟩

theorem leadingCoeff_deleteRootFactor_of_isRoot {p : ℝ[X]} {r : ℝ}
    (hp_ne : p ≠ 0) (hr : p.IsRoot r) :
    (deleteRootFactor p r).leadingCoeff = p.leadingCoeff := by
  have hdeg_ne : p.degree ≠ 0 :=
    ne_of_gt (Polynomial.degree_pos_of_root hp_ne hr)
  simpa [deleteRootFactor] using
    Polynomial.leadingCoeff_divByMonic_X_sub_C p hdeg_ne r

namespace OppositeLeadingSigns

theorem deleteRootFactor_left {p q : ℝ[X]} {r : ℝ}
    (h : OppositeLeadingSigns p q) (hr : p.IsRoot r) :
    OppositeLeadingSigns (deleteRootFactor p r) q := by
  simpa [OppositeLeadingSigns,
    leadingCoeff_deleteRootFactor_of_isRoot h.left_ne_zero hr] using h

theorem deleteRootFactor_right {p q : ℝ[X]} {r : ℝ}
    (h : OppositeLeadingSigns p q) (hr : q.IsRoot r) :
    OppositeLeadingSigns p (deleteRootFactor q r) := by
  simpa [OppositeLeadingSigns,
    leadingCoeff_deleteRootFactor_of_isRoot h.right_ne_zero hr] using h

end OppositeLeadingSigns

namespace IsLargestRoot

theorem mem_roots {p : ℝ[X]} {r : ℝ} (hp_ne : p ≠ 0)
    (h : IsLargestRoot p r) :
    r ∈ p.roots :=
  (Polynomial.mem_roots hp_ne).mpr h.isRoot

theorem natDegree_pos {p : ℝ[X]} {r : ℝ} (hp_ne : p ≠ 0)
    (h : IsLargestRoot p r) :
    0 < p.natDegree :=
  natDegree_pos_of_isRoot hp_ne h.isRoot

theorem factor_deleteRootFactor {p : ℝ[X]} {r : ℝ}
    (h : IsLargestRoot p r) :
    (X - C r) * deleteRootFactor p r = p :=
  factor_deleteRootFactor_of_isRoot h.isRoot

theorem comp_X_add_C_eq_X_mul_deleteRootFactor_comp
    {p : ℝ[X]} {r : ℝ} (h : IsLargestRoot p r) :
    p.comp (X + C r) =
      X * (deleteRootFactor p r).comp (X + C r) :=
  comp_X_add_C_eq_X_mul_deleteRootFactor_comp_of_isRoot h.isRoot

theorem deleteRootFactor_ne_zero {p : ℝ[X]} {r : ℝ} (hp_ne : p ≠ 0)
    (h : IsLargestRoot p r) :
    deleteRootFactor p r ≠ 0 :=
  deleteRootFactor_ne_zero_of_isRoot hp_ne h.isRoot

theorem roots_eq_singleton_add_roots_deleteRootFactor
    {p : ℝ[X]} {r : ℝ} (hp_ne : p ≠ 0) (h : IsLargestRoot p r) :
    p.roots = {r} + (deleteRootFactor p r).roots :=
  roots_eq_singleton_add_roots_deleteRootFactor_of_isRoot hp_ne h.isRoot

theorem rootCountAtOrAbove_deleteRootFactor_add_one
    {p : ℝ[X]} {r x : ℝ} (hp_ne : p ≠ 0) (h : IsLargestRoot p r)
    (hx : x ≤ r) :
    rootCountAtOrAbove p x =
      rootCountAtOrAbove (deleteRootFactor p r) x + 1 :=
  rootCountAtOrAbove_deleteRootFactor_add_one_of_isRoot hp_ne h.isRoot hx

theorem rootCountAtOrAbove_eq_zero_of_lt
    {p : ℝ[X]} {r x : ℝ} (h : IsLargestRoot p r) (hx : r < x) :
    rootCountAtOrAbove p x = 0 :=
  rootCountAtOrAbove_eq_zero_of_forall_roots_lt fun s hs =>
    lt_of_le_of_lt (h.roots_le s hs) hx

theorem deleteRootFactor_splits {p : ℝ[X]} {r : ℝ} (hp_splits : p.Splits)
    (h : IsLargestRoot p r) :
    (deleteRootFactor p r).Splits :=
  deleteRootFactor_splits_of_isRoot hp_splits h.isRoot

theorem deleteRootFactor_ne_zero_and_splits {p : ℝ[X]} {r : ℝ}
    (hp_ne : p ≠ 0) (hp_splits : p.Splits) (h : IsLargestRoot p r) :
    deleteRootFactor p r ≠ 0 ∧ (deleteRootFactor p r).Splits :=
  deleteRootFactor_ne_zero_and_splits_of_isRoot hp_ne hp_splits h.isRoot

theorem leadingCoeff_deleteRootFactor {p : ℝ[X]} {r : ℝ} (hp_ne : p ≠ 0)
    (h : IsLargestRoot p r) :
    (deleteRootFactor p r).leadingCoeff = p.leadingCoeff :=
  leadingCoeff_deleteRootFactor_of_isRoot hp_ne h.isRoot

theorem root_deleteRootFactor_le {p : ℝ[X]} {r s : ℝ} (hp_ne : p ≠ 0)
    (h : IsLargestRoot p r) (hs : (deleteRootFactor p r).IsRoot s) :
    s ≤ r := by
  have hs_p : p.IsRoot s := by
    rw [← h.factor_deleteRootFactor, Polynomial.IsRoot.def, eval_mul]
    exact mul_eq_zero_of_right _ (by simpa [Polynomial.IsRoot.def] using hs)
  exact h.roots_le s ((Polynomial.mem_roots hp_ne).mpr hs_p)

theorem rootCountAtOrAbove_deleteRootFactor_eq_zero_of_lt
    {p : ℝ[X]} {r x : ℝ} (hp_ne : p ≠ 0) (h : IsLargestRoot p r)
    (hx : r < x) :
    rootCountAtOrAbove (deleteRootFactor p r) x = 0 := by
  have hdelete_ne := h.deleteRootFactor_ne_zero hp_ne
  exact rootCountAtOrAbove_eq_zero_of_forall_roots_lt fun s hs =>
    lt_of_le_of_lt
      (h.root_deleteRootFactor_le hp_ne ((Polynomial.mem_roots hdelete_ne).mp hs)) hx

end IsLargestRoot

/-- The `r_1 >= s_1` branch of Liu Theorem 2.1: delete the largest root of
`f`, then compare the closed-at-or-above root counts of `f / (X - r)` and
`g`. -/
structure LeftRootCountBranch (f g : ℝ[X]) (r s : ℝ) : Prop where
  f_largest : IsLargestRoot f r
  g_largest : IsLargestRoot g s
  largest_ge : s ≤ r
  count : RootCountCompatible (deleteRootFactor f r) g

/-- The `r_1 < s_1` branch of Liu Theorem 2.1: delete the largest root of
`g`, then compare the closed-at-or-above root counts of `f` and
`g / (X - s)`. -/
structure RightRootCountBranch (f g : ℝ[X]) (r s : ℝ) : Prop where
  f_largest : IsLargestRoot f r
  g_largest : IsLargestRoot g s
  largest_lt : r < s
  count : RootCountCompatible f (deleteRootFactor g s)

namespace RightRootCountBranch

/-- Swap a right Liu branch into the corresponding left branch for the swapped
polynomial pair. -/
theorem toLeftBranch_symm {f g : ℝ[X]} {r s : ℝ}
    (h : RightRootCountBranch f g r s) :
    LeftRootCountBranch g f s r :=
  ⟨RightRootCountBranch.g_largest h, RightRootCountBranch.f_largest h,
    le_of_lt (RightRootCountBranch.largest_lt h),
    (RightRootCountBranch.count h).symm⟩

end RightRootCountBranch

/-- The root-count branch conclusion in Liu Theorem 2.1, separated from the
larger compatibility/common-interleaver statement. -/
def theorem21RootCountBranches (f g : ℝ[X]) : Prop :=
  ∃ r s, LeftRootCountBranch f g r s ∨ RightRootCountBranch f g r s

theorem theorem21RootCountBranches_of_left {f g : ℝ[X]} {r s : ℝ}
    (h : LeftRootCountBranch f g r s) :
    theorem21RootCountBranches f g :=
  ⟨r, s, Or.inl h⟩

theorem theorem21RootCountBranches_of_right {f g : ℝ[X]} {r s : ℝ}
    (h : RightRootCountBranch f g r s) :
    theorem21RootCountBranches f g :=
  ⟨r, s, Or.inr h⟩

private theorem int_abs_sub_le_two_of_add_one_left {a b c : ℤ}
    (hab : a + 1 = b) (h : |a - c| ≤ 1) :
    |b - c| ≤ 2 := by
  rw [abs_le] at h ⊢
  constructor <;> linarith

private theorem int_abs_sub_le_two_of_add_one_right {a b c : ℤ}
    (hbc : b + 1 = c) (h : |a - b| ≤ 1) :
    |a - c| ≤ 2 := by
  rw [abs_le] at h ⊢
  constructor <;> linarith

private theorem nat_succ_eq_or_eq_succ_or_eq_succ_succ_of_abs_sub_le_one
    {m n k : ℕ} (hk : m + 1 = k)
    (h : |((m : ℤ) - (n : ℤ))| ≤ 1) :
    k = n ∨ k = n + 1 ∨ k = n + 2 := by
  rw [abs_le] at h
  have hk' : (k : ℤ) = (m : ℤ) + 1 := by exact_mod_cast hk.symm
  have hkn_low_int : (n : ℤ) ≤ (k : ℤ) := by linarith
  have hkn_high_int : (k : ℤ) ≤ (n : ℤ) + 2 := by linarith
  have hkn_low : n ≤ k := by exact_mod_cast hkn_low_int
  have hkn_high : k ≤ n + 2 := by exact_mod_cast hkn_high_int
  rcases Nat.exists_eq_add_of_le hkn_low with ⟨d, rfl⟩
  have hd : d ≤ 2 := by linarith
  rcases d with _ | d
  · simp
  rcases d with _ | d
  · simp
  rcases d with _ | d
  · simp
  · exfalso
    linarith

namespace LeftRootCountBranch

theorem delete_splits {f g : ℝ[X]} {r s : ℝ}
    (h : LeftRootCountBranch f g r s) (hf_splits : f.Splits) :
    (deleteRootFactor f r).Splits :=
  h.f_largest.deleteRootFactor_splits hf_splits

theorem delete_ne_zero {f g : ℝ[X]} {r s : ℝ}
    (h : LeftRootCountBranch f g r s) (hf_ne : f ≠ 0) :
    deleteRootFactor f r ≠ 0 :=
  h.f_largest.deleteRootFactor_ne_zero hf_ne

theorem delete_ne_zero_and_splits {f g : ℝ[X]} {r s : ℝ}
    (h : LeftRootCountBranch f g r s) (hf_ne : f ≠ 0)
    (hf_splits : f.Splits) :
    deleteRootFactor f r ≠ 0 ∧ (deleteRootFactor f r).Splits :=
  h.f_largest.deleteRootFactor_ne_zero_and_splits hf_ne hf_splits

theorem delete_oppositeLeadingSigns {f g : ℝ[X]} {r s : ℝ}
    (h : LeftRootCountBranch f g r s) (hsgn : OppositeLeadingSigns f g) :
    OppositeLeadingSigns (deleteRootFactor f r) g :=
  hsgn.deleteRootFactor_left h.f_largest.isRoot

theorem positiveDeletionCount {f g : ℝ[X]} {r s : ℝ}
    (h : LeftRootCountBranch f g r s) (hsgn : OppositeLeadingSigns f g) :
    (HasPosLeadingCoeff (deleteRootFactor f r) ∧ HasPosLeadingCoeff (-g) ∧
        RootCountCompatible (deleteRootFactor f r) (-g)) ∨
      (HasPosLeadingCoeff (-(deleteRootFactor f r)) ∧ HasPosLeadingCoeff g ∧
        RootCountCompatible (-(deleteRootFactor f r)) g) := by
  rcases (h.delete_oppositeLeadingSigns hsgn).pos_neg_or_neg_pos with hpos | hpos
  · exact Or.inl ⟨hpos.1, hpos.2, h.count.neg_right⟩
  · exact Or.inr ⟨hpos.1, hpos.2, h.count.neg_left⟩

theorem positiveSplitDeletionCount {f g : ℝ[X]} {r s : ℝ}
    (h : LeftRootCountBranch f g r s) (hsgn : OppositeLeadingSigns f g)
    (hf_splits : f.Splits) (hg_splits : g.Splits) :
    PositiveSplitRootCountPair (deleteRootFactor f r) (-g) ∨
      PositiveSplitRootCountPair (-(deleteRootFactor f r)) g := by
  rcases h.positiveDeletionCount hsgn with hpos | hpos
  · exact Or.inl
      ⟨hpos.1, hpos.2.1, h.delete_splits hf_splits, hg_splits.neg, hpos.2.2⟩
  · exact Or.inr
      ⟨hpos.1, hpos.2.1, (h.delete_splits hf_splits).neg, hg_splits, hpos.2.2⟩

theorem rootCountAbove_delete_abs_sub_le_one_of_nonRoot
    {f g : ℝ[X]} {r s x : ℝ} (h : LeftRootCountBranch f g r s)
    (hf_ne : f ≠ 0) (hg_ne : g ≠ 0)
    (hfx : ¬ (deleteRootFactor f r).IsRoot x) (hgx : ¬ g.IsRoot x) :
    |((((deleteRootFactor f r).roots.filter (x < ·)).card : ℤ) -
        ((g.roots.filter (x < ·)).card : ℤ))| ≤ 1 :=
  h.count.rootCountAbove_abs_sub_le_one_of_nonRoot
    (h.delete_ne_zero hf_ne) hg_ne hfx hgx

theorem rootCountAbove_delete_bounds_of_nonRoot
    {f g : ℝ[X]} {r s x : ℝ} (h : LeftRootCountBranch f g r s)
    (hf_ne : f ≠ 0) (hg_ne : g ≠ 0)
    (hfx : ¬ (deleteRootFactor f r).IsRoot x) (hgx : ¬ g.IsRoot x) :
    (((deleteRootFactor f r).roots.filter (x < ·)).card : ℤ) -
        (g.roots.filter (x < ·)).card ≤ 1 ∧
      ((g.roots.filter (x < ·)).card : ℤ) -
        ((deleteRootFactor f r).roots.filter (x < ·)).card ≤ 1 :=
  h.count.rootCountAbove_bounds_of_nonRoot
    (h.delete_ne_zero hf_ne) hg_ne hfx hgx

theorem rootCountAtOrAbove_delete_add_one {f g : ℝ[X]} {r s x : ℝ}
    (h : LeftRootCountBranch f g r s) (hf_ne : f ≠ 0) (hx : x ≤ r) :
    rootCountAtOrAbove f x =
      rootCountAtOrAbove (deleteRootFactor f r) x + 1 :=
  h.f_largest.rootCountAtOrAbove_deleteRootFactor_add_one hf_ne hx

theorem rootCountAtOrAbove_abs_sub_le_two {f g : ℝ[X]} {r s : ℝ}
    (h : LeftRootCountBranch f g r s) (hf_ne : f ≠ 0) :
    ∀ x : ℝ,
      |((rootCountAtOrAbove f x : ℤ) - (rootCountAtOrAbove g x : ℤ))| ≤ 2 := by
  intro x
  by_cases hx : x ≤ r
  · have hdelete := h.rootCountAtOrAbove_delete_add_one hf_ne hx
    have hdelete_int :
        ((rootCountAtOrAbove (deleteRootFactor f r) x : ℤ) + 1 =
          (rootCountAtOrAbove f x : ℤ)) := by
      exact_mod_cast hdelete.symm
    exact int_abs_sub_le_two_of_add_one_left hdelete_int (h.count x)
  · have hx_lt : r < x := lt_of_not_ge hx
    have hf_zero := h.f_largest.rootCountAtOrAbove_eq_zero_of_lt hx_lt
    have hdelete_zero :=
      h.f_largest.rootCountAtOrAbove_deleteRootFactor_eq_zero_of_lt hf_ne hx_lt
    have hgap := h.count x
    rw [hdelete_zero] at hgap
    rw [hf_zero]
    exact le_trans hgap (by norm_num)

theorem rootCountAtOrAbove_right_sub_left_le_one {f g : ℝ[X]} {r s : ℝ}
    (h : LeftRootCountBranch f g r s) (hf_ne : f ≠ 0) :
    ∀ x : ℝ,
      ((rootCountAtOrAbove g x : ℤ) - (rootCountAtOrAbove f x : ℤ)) ≤ 1 := by
  intro x
  by_cases hx : x ≤ r
  · have hdelete := h.rootCountAtOrAbove_delete_add_one hf_ne hx
    have hdelete_int :
        (rootCountAtOrAbove f x : ℤ) =
          (rootCountAtOrAbove (deleteRootFactor f r) x : ℤ) + 1 := by
      exact_mod_cast hdelete
    have hgap := h.count.right_sub_le_one x
    rw [hdelete_int]
    linarith
  · have hx_lt : r < x := lt_of_not_ge hx
    have hf_zero := h.f_largest.rootCountAtOrAbove_eq_zero_of_lt hx_lt
    have hdelete_zero :=
      h.f_largest.rootCountAtOrAbove_deleteRootFactor_eq_zero_of_lt hf_ne hx_lt
    simpa [hf_zero, hdelete_zero] using h.count.right_sub_le_one x

theorem rootCountAtOrAbove_bounds {f g : ℝ[X]} {r s : ℝ}
    (h : LeftRootCountBranch f g r s) (hf_ne : f ≠ 0) :
    ∀ x : ℝ,
      ((rootCountAtOrAbove f x : ℤ) - (rootCountAtOrAbove g x : ℤ)) ≤ 2 ∧
        ((rootCountAtOrAbove g x : ℤ) - (rootCountAtOrAbove f x : ℤ)) ≤ 1 := by
  intro x
  have h_abs := h.rootCountAtOrAbove_abs_sub_le_two hf_ne x
  rw [abs_le] at h_abs
  exact ⟨h_abs.2, h.rootCountAtOrAbove_right_sub_left_le_one hf_ne x⟩

theorem root_delete_le {f g : ℝ[X]} {r s t : ℝ}
    (h : LeftRootCountBranch f g r s) (hf_ne : f ≠ 0)
    (ht : (deleteRootFactor f r).IsRoot t) :
    t ≤ r :=
  h.f_largest.root_deleteRootFactor_le hf_ne ht

theorem delete_roots_le_largest {f g : ℝ[X]} {r s : ℝ}
    (h : LeftRootCountBranch f g r s) (hf_ne : f ≠ 0) :
    ∀ t ∈ (deleteRootFactor f r).roots, t ≤ r := by
  intro t ht
  exact h.root_delete_le hf_ne
    ((Polynomial.mem_roots (h.delete_ne_zero hf_ne)).mp ht)

theorem right_roots_le_left_largest {f g : ℝ[X]} {r s : ℝ}
    (h : LeftRootCountBranch f g r s) :
    ∀ t ∈ g.roots, t ≤ r := by
  intro t ht
  exact (h.g_largest.roots_le t ht).trans h.largest_ge

theorem deletionPair_roots_le_left_largest {f g : ℝ[X]} {r s : ℝ}
    (h : LeftRootCountBranch f g r s) (hf_ne : f ≠ 0) :
    (∀ t ∈ (deleteRootFactor f r).roots, t ≤ r) ∧
      ∀ t ∈ g.roots, t ≤ r :=
  ⟨h.delete_roots_le_largest hf_ne, h.right_roots_le_left_largest⟩

theorem left_comp_X_add_C_eq_X_mul_deleteRootFactor_comp
    {f g : ℝ[X]} {r s : ℝ} (h : LeftRootCountBranch f g r s) :
    f.comp (X + C r) =
      X * (deleteRootFactor f r).comp (X + C r) :=
  h.f_largest.comp_X_add_C_eq_X_mul_deleteRootFactor_comp

theorem delete_natDegree_add_one_eq {f g : ℝ[X]} {r s : ℝ}
    (h : LeftRootCountBranch f g r s) (hf_ne : f ≠ 0) :
    (deleteRootFactor f r).natDegree + 1 = f.natDegree := by
  have hf_degree_pos : 0 < f.natDegree :=
    h.f_largest.natDegree_pos hf_ne
  rw [natDegree_deleteRootFactor]
  simpa [Nat.succ_eq_add_one] using Nat.succ_pred_eq_of_pos hf_degree_pos

theorem delete_natDegree_add_one_eq_of_sameDegree {f g : ℝ[X]} {r s : ℝ}
    (h : LeftRootCountBranch f g r s) (hf_ne : f ≠ 0)
    (hdeg : f.natDegree = g.natDegree) :
    (deleteRootFactor f r).natDegree + 1 = g.natDegree :=
  (h.delete_natDegree_add_one_eq hf_ne).trans hdeg

theorem delete_natDegree_eq_of_succDegree {f g : ℝ[X]} {r s : ℝ}
    (h : LeftRootCountBranch f g r s) (hf_ne : f ≠ 0)
    (hdeg : f.natDegree = g.natDegree + 1) :
    (deleteRootFactor f r).natDegree = g.natDegree := by
  have hdelete_succ := h.delete_natDegree_add_one_eq hf_ne
  lia

theorem delete_natDegree_eq_succ_of_twoDegree {f g : ℝ[X]} {r s : ℝ}
    (h : LeftRootCountBranch f g r s) (hf_ne : f ≠ 0)
    (hdeg : f.natDegree = g.natDegree + 2) :
    (deleteRootFactor f r).natDegree = g.natDegree + 1 := by
  have hdelete_succ := h.delete_natDegree_add_one_eq hf_ne
  lia

theorem commonInterleaver_natDegree_eq_of_sameDegree
    {f g k : ℝ[X]} {r s : ℝ}
    (h : LeftRootCountBranch f g r s) (hf_ne : f ≠ 0)
    (hdeg : f.natDegree = g.natDegree)
    (hcommon : Prec (deleteRootFactor f r) k ∧ Prec g k) :
    k.natDegree = g.natDegree := by
  have hdelete_succ :=
    h.delete_natDegree_add_one_eq_of_sameDegree hf_ne hdeg
  have hdelete_bounds := natDegree_bounds_of_prec hcommon.1
  have hright_bounds := natDegree_bounds_of_prec hcommon.2
  lia

theorem commonInterleaver_natDegree_eq_or_eq_succ_of_succDegree
    {f g k : ℝ[X]} {r s : ℝ}
    (h : LeftRootCountBranch f g r s) (hf_ne : f ≠ 0)
    (hdeg : f.natDegree = g.natDegree + 1)
    (hcommon : Prec (deleteRootFactor f r) k ∧ Prec g k) :
    k.natDegree = g.natDegree ∨ k.natDegree = g.natDegree + 1 := by
  have hdelete := h.delete_natDegree_eq_of_succDegree hf_ne hdeg
  have hdelete_bounds := natDegree_bounds_of_prec hcommon.1
  have hright_bounds := natDegree_bounds_of_prec hcommon.2
  by_cases hk : k.natDegree = g.natDegree
  · exact Or.inl hk
  · right
    lia

theorem commonInterleaver_natDegree_eq_delete_of_twoDegree
    {f g k : ℝ[X]} {r s : ℝ}
    (h : LeftRootCountBranch f g r s) (hf_ne : f ≠ 0)
    (hdeg : f.natDegree = g.natDegree + 2)
    (hcommon : Prec (deleteRootFactor f r) k ∧ Prec g k) :
    k.natDegree = (deleteRootFactor f r).natDegree := by
  have hdelete := h.delete_natDegree_eq_succ_of_twoDegree hf_ne hdeg
  have hdelete_bounds := natDegree_bounds_of_prec hcommon.1
  have hright_bounds := natDegree_bounds_of_prec hcommon.2
  lia

theorem commonInterleaver_natDegree_eq_succ_of_twoDegree
    {f g k : ℝ[X]} {r s : ℝ}
    (h : LeftRootCountBranch f g r s) (hf_ne : f ≠ 0)
    (hdeg : f.natDegree = g.natDegree + 2)
    (hcommon : Prec (deleteRootFactor f r) k ∧ Prec g k) :
    k.natDegree = g.natDegree + 1 := by
  rw [h.commonInterleaver_natDegree_eq_delete_of_twoDegree hf_ne hdeg hcommon]
  exact h.delete_natDegree_eq_succ_of_twoDegree hf_ne hdeg

theorem natDegree_abs_sub_le_two {f g : ℝ[X]} {r s : ℝ}
    (h : LeftRootCountBranch f g r s) (hf_ne : f ≠ 0)
    (hf_splits : f.Splits) (hg_splits : g.Splits) :
    |((f.natDegree : ℤ) - (g.natDegree : ℤ))| ≤ 2 := by
  have hgap := h.count.natDegree_abs_sub_le_one (h.delete_splits hf_splits)
    hg_splits
  have hdelete_succ := h.delete_natDegree_add_one_eq hf_ne
  have hdelete_int :
      ((deleteRootFactor f r).natDegree : ℤ) + 1 = (f.natDegree : ℤ) := by
    exact_mod_cast hdelete_succ
  exact int_abs_sub_le_two_of_add_one_left hdelete_int hgap

/-- In the left Liu branch, restoring the deleted root of `f` leaves only the
same-degree, right-succ-degree, or right-plus-two-degree alternatives. -/
theorem natDegree_eq_or_eq_succ_or_eq_succ_succ {f g : ℝ[X]} {r s : ℝ}
    (h : LeftRootCountBranch f g r s) (hf_ne : f ≠ 0)
    (hf_splits : f.Splits) (hg_splits : g.Splits) :
    f.natDegree = g.natDegree ∨
      f.natDegree = g.natDegree + 1 ∨
        f.natDegree = g.natDegree + 2 := by
  have hgap := h.count.natDegree_abs_sub_le_one (h.delete_splits hf_splits)
    hg_splits
  have hdelete_succ := h.delete_natDegree_add_one_eq hf_ne
  exact nat_succ_eq_or_eq_succ_or_eq_succ_succ_of_abs_sub_le_one
    hdelete_succ hgap

end LeftRootCountBranch

namespace RightRootCountBranch

theorem delete_splits {f g : ℝ[X]} {r s : ℝ}
    (h : RightRootCountBranch f g r s) (hg_splits : g.Splits) :
    (deleteRootFactor g s).Splits :=
  h.g_largest.deleteRootFactor_splits hg_splits

theorem delete_ne_zero {f g : ℝ[X]} {r s : ℝ}
    (h : RightRootCountBranch f g r s) (hg_ne : g ≠ 0) :
    deleteRootFactor g s ≠ 0 :=
  h.g_largest.deleteRootFactor_ne_zero hg_ne

theorem delete_ne_zero_and_splits {f g : ℝ[X]} {r s : ℝ}
    (h : RightRootCountBranch f g r s) (hg_ne : g ≠ 0)
    (hg_splits : g.Splits) :
    deleteRootFactor g s ≠ 0 ∧ (deleteRootFactor g s).Splits :=
  h.g_largest.deleteRootFactor_ne_zero_and_splits hg_ne hg_splits

theorem delete_oppositeLeadingSigns {f g : ℝ[X]} {r s : ℝ}
    (h : RightRootCountBranch f g r s) (hsgn : OppositeLeadingSigns f g) :
    OppositeLeadingSigns f (deleteRootFactor g s) :=
  hsgn.deleteRootFactor_right h.g_largest.isRoot

theorem positiveDeletionCount {f g : ℝ[X]} {r s : ℝ}
    (h : RightRootCountBranch f g r s) (hsgn : OppositeLeadingSigns f g) :
    (HasPosLeadingCoeff f ∧ HasPosLeadingCoeff (-(deleteRootFactor g s)) ∧
        RootCountCompatible f (-(deleteRootFactor g s))) ∨
      (HasPosLeadingCoeff (-f) ∧ HasPosLeadingCoeff (deleteRootFactor g s) ∧
        RootCountCompatible (-f) (deleteRootFactor g s)) := by
  rcases (h.delete_oppositeLeadingSigns hsgn).pos_neg_or_neg_pos with hpos | hpos
  · exact Or.inl ⟨hpos.1, hpos.2, h.count.neg_right⟩
  · exact Or.inr ⟨hpos.1, hpos.2, h.count.neg_left⟩

theorem positiveSplitDeletionCount {f g : ℝ[X]} {r s : ℝ}
    (h : RightRootCountBranch f g r s) (hsgn : OppositeLeadingSigns f g)
    (hf_splits : f.Splits) (hg_splits : g.Splits) :
    PositiveSplitRootCountPair f (-(deleteRootFactor g s)) ∨
      PositiveSplitRootCountPair (-f) (deleteRootFactor g s) := by
  rcases h.positiveDeletionCount hsgn with hpos | hpos
  · exact Or.inl
      ⟨hpos.1, hpos.2.1, hf_splits, (h.delete_splits hg_splits).neg, hpos.2.2⟩
  · exact Or.inr
      ⟨hpos.1, hpos.2.1, hf_splits.neg, h.delete_splits hg_splits, hpos.2.2⟩

theorem rootCountAbove_delete_abs_sub_le_one_of_nonRoot
    {f g : ℝ[X]} {r s x : ℝ} (h : RightRootCountBranch f g r s)
    (hf_ne : f ≠ 0) (hg_ne : g ≠ 0)
    (hfx : ¬ f.IsRoot x) (hgx : ¬ (deleteRootFactor g s).IsRoot x) :
    |(((f.roots.filter (x < ·)).card : ℤ) -
        (((deleteRootFactor g s).roots.filter (x < ·)).card : ℤ))| ≤ 1 :=
  h.count.rootCountAbove_abs_sub_le_one_of_nonRoot
    hf_ne (h.delete_ne_zero hg_ne) hfx hgx

theorem rootCountAbove_delete_bounds_of_nonRoot
    {f g : ℝ[X]} {r s x : ℝ} (h : RightRootCountBranch f g r s)
    (hf_ne : f ≠ 0) (hg_ne : g ≠ 0)
    (hfx : ¬ f.IsRoot x) (hgx : ¬ (deleteRootFactor g s).IsRoot x) :
    ((f.roots.filter (x < ·)).card : ℤ) -
        ((deleteRootFactor g s).roots.filter (x < ·)).card ≤ 1 ∧
      (((deleteRootFactor g s).roots.filter (x < ·)).card : ℤ) -
        (f.roots.filter (x < ·)).card ≤ 1 :=
  h.count.rootCountAbove_bounds_of_nonRoot
    hf_ne (h.delete_ne_zero hg_ne) hfx hgx

theorem rootCountAtOrAbove_delete_add_one {f g : ℝ[X]} {r s x : ℝ}
    (h : RightRootCountBranch f g r s) (hg_ne : g ≠ 0) (hx : x ≤ s) :
    rootCountAtOrAbove g x =
      rootCountAtOrAbove (deleteRootFactor g s) x + 1 :=
  h.g_largest.rootCountAtOrAbove_deleteRootFactor_add_one hg_ne hx

theorem rootCountAtOrAbove_abs_sub_le_two {f g : ℝ[X]} {r s : ℝ}
    (h : RightRootCountBranch f g r s) (hg_ne : g ≠ 0) :
    ∀ x : ℝ,
      |((rootCountAtOrAbove f x : ℤ) - (rootCountAtOrAbove g x : ℤ))| ≤ 2 := by
  intro x
  by_cases hx : x ≤ s
  · have hdelete := h.rootCountAtOrAbove_delete_add_one hg_ne hx
    have hdelete_int :
        ((rootCountAtOrAbove (deleteRootFactor g s) x : ℤ) + 1 =
          (rootCountAtOrAbove g x : ℤ)) := by
      exact_mod_cast hdelete.symm
    exact int_abs_sub_le_two_of_add_one_right hdelete_int (h.count x)
  · have hx_lt : s < x := lt_of_not_ge hx
    have hg_zero := h.g_largest.rootCountAtOrAbove_eq_zero_of_lt hx_lt
    have hdelete_zero :=
      h.g_largest.rootCountAtOrAbove_deleteRootFactor_eq_zero_of_lt hg_ne hx_lt
    have hgap := h.count x
    rw [hdelete_zero] at hgap
    rw [hg_zero]
    exact le_trans hgap (by norm_num)

theorem rootCountAtOrAbove_left_sub_right_le_one {f g : ℝ[X]} {r s : ℝ}
    (h : RightRootCountBranch f g r s) (hg_ne : g ≠ 0) :
    ∀ x : ℝ,
      ((rootCountAtOrAbove f x : ℤ) - (rootCountAtOrAbove g x : ℤ)) ≤ 1 := by
  intro x
  by_cases hx : x ≤ s
  · have hdelete := h.rootCountAtOrAbove_delete_add_one hg_ne hx
    have hdelete_int :
        (rootCountAtOrAbove g x : ℤ) =
          (rootCountAtOrAbove (deleteRootFactor g s) x : ℤ) + 1 := by
      exact_mod_cast hdelete
    have hgap := h.count.left_sub_le_one x
    rw [hdelete_int]
    linarith
  · have hx_lt : s < x := lt_of_not_ge hx
    have hg_zero := h.g_largest.rootCountAtOrAbove_eq_zero_of_lt hx_lt
    have hdelete_zero :=
      h.g_largest.rootCountAtOrAbove_deleteRootFactor_eq_zero_of_lt hg_ne hx_lt
    simpa [hg_zero, hdelete_zero] using h.count.left_sub_le_one x

theorem rootCountAtOrAbove_bounds {f g : ℝ[X]} {r s : ℝ}
    (h : RightRootCountBranch f g r s) (hg_ne : g ≠ 0) :
    ∀ x : ℝ,
      ((rootCountAtOrAbove f x : ℤ) - (rootCountAtOrAbove g x : ℤ)) ≤ 1 ∧
        ((rootCountAtOrAbove g x : ℤ) - (rootCountAtOrAbove f x : ℤ)) ≤ 2 := by
  intro x
  have h_abs := h.rootCountAtOrAbove_abs_sub_le_two hg_ne x
  rw [abs_le] at h_abs
  exact ⟨h.rootCountAtOrAbove_left_sub_right_le_one hg_ne x, by linarith [h_abs.1]⟩

theorem root_delete_le {f g : ℝ[X]} {r s t : ℝ}
    (h : RightRootCountBranch f g r s) (hg_ne : g ≠ 0)
    (ht : (deleteRootFactor g s).IsRoot t) :
    t ≤ s :=
  h.g_largest.root_deleteRootFactor_le hg_ne ht

theorem left_roots_le_right_largest {f g : ℝ[X]} {r s : ℝ}
    (h : RightRootCountBranch f g r s) :
    ∀ t ∈ f.roots, t ≤ s := by
  intro t ht
  exact (h.f_largest.roots_le t ht).trans (le_of_lt h.largest_lt)

theorem delete_roots_le_largest {f g : ℝ[X]} {r s : ℝ}
    (h : RightRootCountBranch f g r s) (hg_ne : g ≠ 0) :
    ∀ t ∈ (deleteRootFactor g s).roots, t ≤ s := by
  intro t ht
  exact h.root_delete_le hg_ne
    ((Polynomial.mem_roots (h.delete_ne_zero hg_ne)).mp ht)

theorem deletionPair_roots_le_right_largest {f g : ℝ[X]} {r s : ℝ}
    (h : RightRootCountBranch f g r s) (hg_ne : g ≠ 0) :
    (∀ t ∈ f.roots, t ≤ s) ∧
      ∀ t ∈ (deleteRootFactor g s).roots, t ≤ s :=
  ⟨h.left_roots_le_right_largest, h.delete_roots_le_largest hg_ne⟩

theorem right_comp_X_add_C_eq_X_mul_deleteRootFactor_comp
    {f g : ℝ[X]} {r s : ℝ} (h : RightRootCountBranch f g r s) :
    g.comp (X + C s) =
      X * (deleteRootFactor g s).comp (X + C s) :=
  h.g_largest.comp_X_add_C_eq_X_mul_deleteRootFactor_comp

theorem delete_natDegree_add_one_eq {f g : ℝ[X]} {r s : ℝ}
    (h : RightRootCountBranch f g r s) (hg_ne : g ≠ 0) :
    (deleteRootFactor g s).natDegree + 1 = g.natDegree := by
  have hg_degree_pos : 0 < g.natDegree :=
    h.g_largest.natDegree_pos hg_ne
  rw [natDegree_deleteRootFactor]
  simpa [Nat.succ_eq_add_one] using Nat.succ_pred_eq_of_pos hg_degree_pos

theorem delete_natDegree_add_one_eq_of_sameDegree {f g : ℝ[X]} {r s : ℝ}
    (h : RightRootCountBranch f g r s) (hg_ne : g ≠ 0)
    (hdeg : g.natDegree = f.natDegree) :
    (deleteRootFactor g s).natDegree + 1 = f.natDegree :=
  (h.delete_natDegree_add_one_eq hg_ne).trans hdeg

theorem delete_natDegree_eq_of_succDegree {f g : ℝ[X]} {r s : ℝ}
    (h : RightRootCountBranch f g r s) (hg_ne : g ≠ 0)
    (hdeg : g.natDegree = f.natDegree + 1) :
    (deleteRootFactor g s).natDegree = f.natDegree := by
  have hdelete_succ := h.delete_natDegree_add_one_eq hg_ne
  lia

theorem delete_natDegree_eq_succ_of_twoDegree {f g : ℝ[X]} {r s : ℝ}
    (h : RightRootCountBranch f g r s) (hg_ne : g ≠ 0)
    (hdeg : g.natDegree = f.natDegree + 2) :
    (deleteRootFactor g s).natDegree = f.natDegree + 1 := by
  have hdelete_succ := h.delete_natDegree_add_one_eq hg_ne
  lia

theorem commonInterleaver_natDegree_eq_of_sameDegree
    {f g k : ℝ[X]} {r s : ℝ}
    (h : RightRootCountBranch f g r s) (hg_ne : g ≠ 0)
    (hdeg : g.natDegree = f.natDegree)
    (hcommon : Prec f k ∧ Prec (deleteRootFactor g s) k) :
    k.natDegree = f.natDegree := by
  have hdelete_succ :=
    h.delete_natDegree_add_one_eq_of_sameDegree hg_ne hdeg
  have hleft_bounds := natDegree_bounds_of_prec hcommon.1
  have hdelete_bounds := natDegree_bounds_of_prec hcommon.2
  lia

theorem commonInterleaver_natDegree_eq_or_eq_succ_of_succDegree
    {f g k : ℝ[X]} {r s : ℝ}
    (h : RightRootCountBranch f g r s) (hg_ne : g ≠ 0)
    (hdeg : g.natDegree = f.natDegree + 1)
    (hcommon : Prec f k ∧ Prec (deleteRootFactor g s) k) :
    k.natDegree = f.natDegree ∨ k.natDegree = f.natDegree + 1 := by
  have hdelete := h.delete_natDegree_eq_of_succDegree hg_ne hdeg
  have hleft_bounds := natDegree_bounds_of_prec hcommon.1
  have hdelete_bounds := natDegree_bounds_of_prec hcommon.2
  by_cases hk : k.natDegree = f.natDegree
  · exact Or.inl hk
  · right
    lia

theorem commonInterleaver_natDegree_eq_delete_of_twoDegree
    {f g k : ℝ[X]} {r s : ℝ}
    (h : RightRootCountBranch f g r s) (hg_ne : g ≠ 0)
    (hdeg : g.natDegree = f.natDegree + 2)
    (hcommon : Prec f k ∧ Prec (deleteRootFactor g s) k) :
    k.natDegree = (deleteRootFactor g s).natDegree := by
  have hdelete := h.delete_natDegree_eq_succ_of_twoDegree hg_ne hdeg
  have hleft_bounds := natDegree_bounds_of_prec hcommon.1
  have hdelete_bounds := natDegree_bounds_of_prec hcommon.2
  lia

theorem commonInterleaver_natDegree_eq_succ_of_twoDegree
    {f g k : ℝ[X]} {r s : ℝ}
    (h : RightRootCountBranch f g r s) (hg_ne : g ≠ 0)
    (hdeg : g.natDegree = f.natDegree + 2)
    (hcommon : Prec f k ∧ Prec (deleteRootFactor g s) k) :
    k.natDegree = f.natDegree + 1 := by
  rw [h.commonInterleaver_natDegree_eq_delete_of_twoDegree hg_ne hdeg hcommon]
  exact h.delete_natDegree_eq_succ_of_twoDegree hg_ne hdeg

theorem natDegree_abs_sub_le_two {f g : ℝ[X]} {r s : ℝ}
    (h : RightRootCountBranch f g r s) (hg_ne : g ≠ 0)
    (hf_splits : f.Splits) (hg_splits : g.Splits) :
    |((f.natDegree : ℤ) - (g.natDegree : ℤ))| ≤ 2 := by
  have hgap := h.count.natDegree_abs_sub_le_one hf_splits
    (h.delete_splits hg_splits)
  have hdelete_succ := h.delete_natDegree_add_one_eq hg_ne
  have hdelete_int :
      ((deleteRootFactor g s).natDegree : ℤ) + 1 = (g.natDegree : ℤ) := by
    exact_mod_cast hdelete_succ
  exact int_abs_sub_le_two_of_add_one_right hdelete_int hgap

/-- In the right Liu branch, restoring the deleted root of `g` leaves only the
same-degree, left-succ-degree, or left-plus-two-degree alternatives. -/
theorem natDegree_eq_or_eq_succ_or_eq_succ_succ {f g : ℝ[X]} {r s : ℝ}
    (h : RightRootCountBranch f g r s) (hg_ne : g ≠ 0)
    (hf_splits : f.Splits) (hg_splits : g.Splits) :
    g.natDegree = f.natDegree ∨
      g.natDegree = f.natDegree + 1 ∨
        g.natDegree = f.natDegree + 2 := by
  have hgap := h.count.natDegree_abs_sub_le_one hf_splits
    (h.delete_splits hg_splits)
  have hdelete_succ := h.delete_natDegree_add_one_eq hg_ne
  have hgap' : |(((deleteRootFactor g s).natDegree : ℤ) - (f.natDegree : ℤ))| ≤ 1 := by
    simpa [abs_sub_comm] using hgap
  exact nat_succ_eq_or_eq_succ_or_eq_succ_succ_of_abs_sub_le_one
    hdelete_succ hgap'

end RightRootCountBranch

theorem rootCountAtOrAbove_abs_sub_le_two_of_theorem21RootCountBranches
    {f g : ℝ[X]} (hsgn : OppositeLeadingSigns f g)
    (h : theorem21RootCountBranches f g) :
    ∀ x : ℝ,
      |((rootCountAtOrAbove f x : ℤ) - (rootCountAtOrAbove g x : ℤ))| ≤ 2 := by
  rcases h with ⟨r, s, hleft | hright⟩
  · exact hleft.rootCountAtOrAbove_abs_sub_le_two hsgn.left_ne_zero
  · exact hright.rootCountAtOrAbove_abs_sub_le_two hsgn.right_ne_zero

theorem rootCountAtOrAbove_branch_bounds_of_theorem21RootCountBranches
    {f g : ℝ[X]} (hsgn : OppositeLeadingSigns f g)
    (h : theorem21RootCountBranches f g) :
    (∀ x : ℝ,
      ((rootCountAtOrAbove f x : ℤ) - (rootCountAtOrAbove g x : ℤ)) ≤ 2 ∧
        ((rootCountAtOrAbove g x : ℤ) - (rootCountAtOrAbove f x : ℤ)) ≤ 1) ∨
      (∀ x : ℝ,
        ((rootCountAtOrAbove f x : ℤ) - (rootCountAtOrAbove g x : ℤ)) ≤ 1 ∧
          ((rootCountAtOrAbove g x : ℤ) - (rootCountAtOrAbove f x : ℤ)) ≤ 2) := by
  rcases h with ⟨r, s, hleft | hright⟩
  · exact Or.inl (hleft.rootCountAtOrAbove_bounds hsgn.left_ne_zero)
  · exact Or.inr (hright.rootCountAtOrAbove_bounds hsgn.right_ne_zero)

/-- Liu branch data after normalizing the compared deletion pair so that both
leading coefficients are positive. -/
def theorem21PositiveDeletionCountBranches (f g : ℝ[X]) : Prop :=
  ∃ r s,
    (PositiveSplitRootCountPair (deleteRootFactor f r) (-g) ∨
        PositiveSplitRootCountPair (-(deleteRootFactor f r)) g) ∨
      (PositiveSplitRootCountPair f (-(deleteRootFactor g s)) ∨
        PositiveSplitRootCountPair (-f) (deleteRootFactor g s))

theorem theorem21PositiveDeletionCountBranches_of_theorem21RootCountBranches
    {f g : ℝ[X]} (hf_splits : f.Splits) (hg_splits : g.Splits)
    (hsgn : OppositeLeadingSigns f g) (h : theorem21RootCountBranches f g) :
    theorem21PositiveDeletionCountBranches f g := by
  rcases h with ⟨r, s, hleft | hright⟩
  · exact ⟨r, s, Or.inl (hleft.positiveSplitDeletionCount
      hsgn hf_splits hg_splits)⟩
  · exact ⟨r, s, Or.inr (hright.positiveSplitDeletionCount
      hsgn hf_splits hg_splits)⟩

theorem natDegree_abs_sub_le_two_of_theorem21RootCountBranches {f g : ℝ[X]}
    (hf_splits : f.Splits) (hg_splits : g.Splits)
    (hsgn : OppositeLeadingSigns f g) (h : theorem21RootCountBranches f g) :
    |((f.natDegree : ℤ) - (g.natDegree : ℤ))| ≤ 2 := by
  rcases h with ⟨r, s, hleft | hright⟩
  · exact hleft.natDegree_abs_sub_le_two hsgn.left_ne_zero hf_splits hg_splits
  · exact hright.natDegree_abs_sub_le_two hsgn.right_ne_zero hf_splits hg_splits

/-- Swapped-branch form of the Liu Theorem 2.1 degree-gap consequence. -/
theorem natDegree_abs_sub_le_two_of_theorem21RootCountBranches_symm {f g : ℝ[X]}
    (hf_splits : f.Splits) (hg_splits : g.Splits)
    (hsgn : OppositeLeadingSigns f g) (h : theorem21RootCountBranches g f) :
    |((f.natDegree : ℤ) - (g.natDegree : ℤ))| ≤ 2 := by
  simpa [abs_sub_comm] using
    natDegree_abs_sub_le_two_of_theorem21RootCountBranches
      hg_splits hf_splits hsgn.symm h

end LiuOppositeSigns
end RealRooted
