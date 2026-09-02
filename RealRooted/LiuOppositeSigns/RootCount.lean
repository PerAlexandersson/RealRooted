import RealRooted.Basic
import RealRooted.Linear
import RealRooted.Mathlib.Algebra.Polynomial.Eval.Defs
import RealRooted.RootCountJump

/-!
# Liu root-count compatibility foundation

This module packages Liu's root-count function, root deletion operation, and
the reusable threshold lemmas for root-count-compatible polynomial pairs.
Positive-leading normalization and the left/right deletion branches remain in
`RealRooted.LiuOppositeSigns`.
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

theorem rootCountAtOrAbove_le_natDegree_of_splits {p : ℝ[X]}
    (hp_splits : p.Splits) (x : ℝ) :
    rootCountAtOrAbove p x ≤ p.natDegree := by
  have hfilter_le :
      (p.roots.filter (fun r => x ≤ r)).card ≤ p.roots.card :=
    Multiset.card_le_card (Multiset.filter_le (fun r => x ≤ r) p.roots)
  simpa [rootCountAtOrAbove, card_roots_of_splits hp_splits] using hfilter_le

theorem rootCountAtOrAbove_eq_zero_of_splits_natDegree_eq_zero {p : ℝ[X]}
    (hp_splits : p.Splits) (hpdeg : p.natDegree = 0) (x : ℝ) :
    rootCountAtOrAbove p x = 0 := by
  exact Nat.eq_zero_of_le_zero
    (by simpa [hpdeg] using rootCountAtOrAbove_le_natDegree_of_splits hp_splits x)

theorem RootCountCompatible.of_left_natDegree_zero_right_natDegree_le_one
    {p q : ℝ[X]} (hp_splits : p.Splits) (hq_splits : q.Splits)
    (hpdeg : p.natDegree = 0) (hqdeg : q.natDegree ≤ 1) :
    RootCountCompatible p q := by
  intro x
  have hp_count :
      rootCountAtOrAbove p x = 0 :=
    rootCountAtOrAbove_eq_zero_of_splits_natDegree_eq_zero
      hp_splits hpdeg x
  have hq_le : rootCountAtOrAbove q x ≤ 1 :=
    (rootCountAtOrAbove_le_natDegree_of_splits hq_splits x).trans hqdeg
  have hq_nonneg : (0 : ℤ) ≤ (rootCountAtOrAbove q x : ℤ) := by
    exact_mod_cast Nat.zero_le (rootCountAtOrAbove q x)
  have hq_le_int : (rootCountAtOrAbove q x : ℤ) ≤ 1 := by exact_mod_cast hq_le
  calc
    |((rootCountAtOrAbove p x : ℤ) - (rootCountAtOrAbove q x : ℤ))|
        = |(rootCountAtOrAbove q x : ℤ)| := by
          rw [hp_count]
          simp
    _ = (rootCountAtOrAbove q x : ℤ) := abs_of_nonneg hq_nonneg
    _ ≤ 1 := hq_le_int

theorem RootCountCompatible.of_natDegree_le_one
    {p q : ℝ[X]} (hp_splits : p.Splits) (hq_splits : q.Splits)
    (hpdeg : p.natDegree ≤ 1) (hqdeg : q.natDegree ≤ 1) :
    RootCountCompatible p q := by
  intro x
  have hp_le : rootCountAtOrAbove p x ≤ 1 :=
    (rootCountAtOrAbove_le_natDegree_of_splits hp_splits x).trans hpdeg
  have hq_le : rootCountAtOrAbove q x ≤ 1 :=
    (rootCountAtOrAbove_le_natDegree_of_splits hq_splits x).trans hqdeg
  have hp_nonneg : (0 : ℤ) ≤ (rootCountAtOrAbove p x : ℤ) := by
    exact_mod_cast Nat.zero_le (rootCountAtOrAbove p x)
  have hq_nonneg : (0 : ℤ) ≤ (rootCountAtOrAbove q x : ℤ) := by
    exact_mod_cast Nat.zero_le (rootCountAtOrAbove q x)
  have hp_le_int : (rootCountAtOrAbove p x : ℤ) ≤ 1 := by exact_mod_cast hp_le
  have hq_le_int : (rootCountAtOrAbove q x : ℤ) ≤ 1 := by exact_mod_cast hq_le
  rw [abs_le]
  constructor <;> linarith

/-- A two-root polynomial and a one-root polynomial have Liu-compatible root
counts when the lower root of the two-root side lies weakly below the singleton
root. -/
theorem RootCountCompatible.of_roots_pair_singleton
    {p q : ℝ[X]} {a b c : ℝ} (hac : a ≤ c)
    (hproots : p.roots = {a, b}) (hqroots : q.roots = {c}) :
    RootCountCompatible p q := by
  intro x
  rw [rootCountAtOrAbove, rootCountAtOrAbove, hproots, hqroots]
  simp only [Multiset.insert_eq_cons, Multiset.filter_cons,
    Multiset.filter_singleton]
  by_cases hxa : x ≤ a
  · have hxc : x ≤ c := hxa.trans hac
    by_cases hxb : x ≤ b <;> norm_num [hxa, hxb, hxc]
  · by_cases hxb : x ≤ b <;> by_cases hxc : x ≤ c <;> norm_num [hxa, hxb, hxc]

/-- A one-root polynomial and a two-root polynomial have Liu-compatible root
counts when the lower root of the two-root side lies weakly below the singleton
root. -/
theorem RootCountCompatible.of_roots_singleton_pair
    {p q : ℝ[X]} {a c d : ℝ} (hca : c ≤ a)
    (hproots : p.roots = {a}) (hqroots : q.roots = {c, d}) :
    RootCountCompatible p q := by
  intro x
  rw [rootCountAtOrAbove, rootCountAtOrAbove, hproots, hqroots]
  simp only [Multiset.insert_eq_cons, Multiset.filter_cons,
    Multiset.filter_singleton]
  by_cases hxc : x ≤ c
  · have hxa : x ≤ a := hxc.trans hca
    by_cases hxd : x ≤ d <;> norm_num [hxa, hxc, hxd]
  · by_cases hxa : x ≤ a <;> by_cases hxd : x ≤ d <;> norm_num [hxa, hxc, hxd]

/-- Two two-root polynomials have Liu-compatible root counts when the two
closed root intervals overlap. -/
theorem RootCountCompatible.of_roots_pair_pair
    {p q : ℝ[X]} {a b c d : ℝ} (had : a ≤ d) (hcb : c ≤ b)
    (hproots : p.roots = {a, b}) (hqroots : q.roots = {c, d}) :
    RootCountCompatible p q := by
  intro x
  rw [rootCountAtOrAbove, rootCountAtOrAbove, hproots, hqroots]
  simp only [Multiset.insert_eq_cons, Multiset.filter_cons,
    Multiset.filter_singleton]
  by_cases hxa : x ≤ a <;>
    by_cases hxb : x ≤ b <;>
    by_cases hxc : x ≤ c <;>
    by_cases hxd : x ≤ d <;>
    norm_num [hxa, hxb, hxc, hxd] <;> linarith

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

/-- The same-degree leading-term cancellation parameter is positive for an
opposite-leading-sign pair. -/
theorem OppositeLeadingSigns.cancelParameter_pos {p q : ℝ[X]}
    (h : OppositeLeadingSigns p q) :
    0 < -p.leadingCoeff / q.leadingCoeff := by
  rw [neg_div]
  exact neg_pos.mpr
    ((div_neg_iff.mpr (mul_neg_iff.mp h)) : p.leadingCoeff / q.leadingCoeff < 0)

/-- Swapping an opposite-leading-sign pair inverts the leading-term
cancellation parameter. -/
theorem OppositeLeadingSigns.cancelParameter_symm_eq_inv {p q : ℝ[X]}
    (h : OppositeLeadingSigns p q) :
    -q.leadingCoeff / p.leadingCoeff =
      (-p.leadingCoeff / q.leadingCoeff)⁻¹ := by
  have hp_lc : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr h.left_ne_zero
  have hq_lc : q.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr h.right_ne_zero
  field_simp [hp_lc, hq_lc]

/-- For two splitting polynomials with opposite leading signs, the signed
difference of the numbers of roots strictly above a common non-root is odd
exactly when the two values at the point have the same sign. -/
theorem OppositeLeadingSigns.odd_intCard_roots_gt_sub_iff_eval_pos_iff
    {p q : ℝ[X]} (h : OppositeLeadingSigns p q)
    (hp : p.Splits) (hq : q.Splits)
    {x : ℝ} (hxp : ¬ p.IsRoot x) (hxq : ¬ q.IsRoot x) :
    (Odd (((p.roots.filter (x < ·)).card : ℤ) -
        (q.roots.filter (x < ·)).card) ↔
      (0 < p.eval x ↔ 0 < q.eval x)) := by
  let d : ℤ :=
    ((p.roots.filter (x < ·)).card : ℤ) -
      (q.roots.filter (x < ·)).card
  have hp_eval_ne : p.eval x ≠ 0 :=
    (Polynomial.not_isRoot_iff_eval_ne_zero p x).mp hxp
  have hq_eval_ne : q.eval x ≠ 0 :=
    (Polynomial.not_isRoot_iff_eval_ne_zero q x).mp hxq
  have hneg_pos_iff_not_pos {y : ℝ} (hy : y ≠ 0) : 0 < -y ↔ ¬ 0 < y := by
    rw [neg_pos]
    exact Iff.intro (fun h hy_pos => by linarith)
      (fun h => lt_of_le_of_ne (le_of_not_gt h) hy)
  rcases h.pos_neg_or_neg_pos with ⟨hp_pos, hnegq_pos⟩ | ⟨hnegp_pos, hq_pos⟩
  · have hxnegq : ¬ (-q).IsRoot x := by simpa using hxq
    have hparity :
        Even d ↔ ¬ (0 < p.eval x ↔ 0 < q.eval x) := by
      have hpos :=
        hp.even_intCard_roots_gt_sub_iff_eval_pos_iff
          (q := -q) hq.neg hp_pos hnegq_pos hxp hxnegq
      rw [Polynomial.roots_neg] at hpos
      change Even d ↔ (0 < p.eval x ↔ 0 < (-q).eval x) at hpos
      rw [hpos]
      have hnegq_eval : 0 < (-q).eval x ↔ ¬ 0 < q.eval x := by
        simpa using hneg_pos_iff_not_pos hq_eval_ne
      rw [hnegq_eval]
      tauto
    rw [Int.not_even_iff_odd.symm, hparity]
    tauto
  · have hxnegp : ¬ (-p).IsRoot x := by simpa using hxp
    have hparity :
        Even d ↔ ¬ (0 < p.eval x ↔ 0 < q.eval x) := by
      have hpos :=
        hp.neg.even_intCard_roots_gt_sub_iff_eval_pos_iff
          (q := q) hq hnegp_pos hq_pos hxnegp hxq
      rw [Polynomial.roots_neg] at hpos
      change Even d ↔ (0 < (-p).eval x ↔ 0 < q.eval x) at hpos
      rw [hpos]
      have hnegp_eval : 0 < (-p).eval x ↔ ¬ 0 < p.eval x := by
        simpa using hneg_pos_iff_not_pos hp_eval_ne
      rw [hnegp_eval]
      tauto
    rw [Int.not_even_iff_odd.symm, hparity]
    tauto

theorem natDegree_deleteRootFactor (p : ℝ[X]) (r : ℝ) :
    (deleteRootFactor p r).natDegree = p.natDegree - 1 := by
  simpa [deleteRootFactor] using Polynomial.natDegree_divByMonic_X_sub_C p r

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

theorem not_isRoot_of_not_deleteRootFactor_isRoot_of_lt
    {p : ℝ[X]} {r x : ℝ} (hr : p.IsRoot r) (hx : x < r)
    (hdelete : ¬ (deleteRootFactor p r).IsRoot x) :
    ¬ p.IsRoot x := by
  intro hpx
  have hx_factor : (X - C r : ℝ[X]).eval x ≠ 0 := by simp [sub_ne_zero, ne_of_lt hx]
  rw [← factor_deleteRootFactor_of_isRoot hr, Polynomial.IsRoot.def,
    eval_mul] at hpx
  exact hdelete (by
    rw [Polynomial.IsRoot.def]
    exact (mul_eq_zero.mp hpx).resolve_left hx_factor)

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

/-- Deleting a root strictly below the root-count threshold leaves the count
above the threshold unchanged. -/
theorem rootCountAtOrAbove_deleteRootFactor_eq_of_isRoot_of_lt
    {p : ℝ[X]} {r x : ℝ} (hp_ne : p ≠ 0) (hr : p.IsRoot r)
    (hx : r < x) :
    rootCountAtOrAbove p x =
      rootCountAtOrAbove (deleteRootFactor p r) x := by
  rw [rootCountAtOrAbove, rootCountAtOrAbove,
    roots_eq_singleton_add_roots_deleteRootFactor_of_isRoot hp_ne hr]
  simp [not_le.mpr hx]

/-- Deleting the same common root from two endpoints preserves Liu's
root-count compatibility condition. -/
theorem RootCountCompatible.deleteRootFactor_commonRoot
    {p q : ℝ[X]} (h : RootCountCompatible p q)
    (hp_ne : p ≠ 0) (hq_ne : q ≠ 0) {r : ℝ}
    (hp : p.IsRoot r) (hq : q.IsRoot r) :
    RootCountCompatible (deleteRootFactor p r) (deleteRootFactor q r) := by
  intro x
  by_cases hx : x ≤ r
  · have hp_count :=
      rootCountAtOrAbove_deleteRootFactor_add_one_of_isRoot hp_ne hp hx
    have hq_count :=
      rootCountAtOrAbove_deleteRootFactor_add_one_of_isRoot hq_ne hq hx
    have hbound := h x
    rw [hp_count, hq_count] at hbound
    simpa [Int.natCast_add] using hbound
  · have hrx : r < x := lt_of_not_ge hx
    have hp_count :=
      rootCountAtOrAbove_deleteRootFactor_eq_of_isRoot_of_lt hp_ne hp hrx
    have hq_count :=
      rootCountAtOrAbove_deleteRootFactor_eq_of_isRoot_of_lt hq_ne hq hrx
    simpa [hp_count, hq_count] using h x

theorem rootCountAbove_deleteRootFactor_add_one_of_isRoot
    {p : ℝ[X]} {r x : ℝ} (hp_ne : p ≠ 0) (hr : p.IsRoot r)
    (hx : x < r) :
    (p.roots.filter (x < ·)).card =
      ((deleteRootFactor p r).roots.filter (x < ·)).card + 1 := by
  rw [roots_eq_singleton_add_roots_deleteRootFactor_of_isRoot hp_ne hr]
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
  have hx_not_mem : x ∉ p.roots := by
    intro hx_mem
    exact hx ((Polynomial.mem_roots hp_ne).mp hx_mem)
  have hfilter := Multiset.filter_ge_eq_filter_gt_of_not_mem p.roots hx_not_mem
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

theorem RootCountCompatible.rootCountAbove_left_sub_le_one_of_nonRoot
    {p q : ℝ[X]} (h : RootCountCompatible p q)
    (hp_ne : p ≠ 0) (hq_ne : q ≠ 0) {x : ℝ}
    (hpx : ¬ p.IsRoot x) (hqx : ¬ q.IsRoot x) :
    ((p.roots.filter (x < ·)).card : ℤ) -
        (q.roots.filter (x < ·)).card ≤ 1 :=
  (abs_le.mp (h.rootCountAbove_abs_sub_le_one_of_nonRoot hp_ne hq_ne hpx hqx)).2

theorem RootCountCompatible.rootCountAbove_bounds_of_nonRoot
    {p q : ℝ[X]} (h : RootCountCompatible p q)
    (hp_ne : p ≠ 0) (hq_ne : q ≠ 0) {x : ℝ}
    (hpx : ¬ p.IsRoot x) (hqx : ¬ q.IsRoot x) :
    ((p.roots.filter (x < ·)).card : ℤ) -
        (q.roots.filter (x < ·)).card ≤ 1 ∧
      ((q.roots.filter (x < ·)).card : ℤ) -
        (p.roots.filter (x < ·)).card ≤ 1 :=
  ⟨h.rootCountAbove_left_sub_le_one_of_nonRoot hp_ne hq_ne hpx hqx,
    h.symm.rootCountAbove_left_sub_le_one_of_nonRoot hq_ne hp_ne hqx hpx⟩

/-- A root-count-compatible bound at the upper endpoint of `(a, b]` shifts to
the lower endpoint after subtracting the explicit roots in the window. -/
theorem RootCountCompatible.rootCountAbove_shift_Ioc_abs_le_one
    {p q : ℝ[X]} (h : RootCountCompatible p q)
    (hp_ne : p ≠ 0) (hq_ne : q ≠ 0) {a b : ℝ} (hab : a ≤ b)
    (hpb : ¬ p.IsRoot b) (hqb : ¬ q.IsRoot b) :
    |(((p.roots.filter (a < ·)).card : ℤ) -
          (q.roots.filter (a < ·)).card) -
        (((p.roots.filter (fun r => a < r ∧ r ≤ b)).card : ℤ) -
          (q.roots.filter (fun r => a < r ∧ r ≤ b)).card)| ≤ 1 := by
  have hbabs :=
    h.rootCountAbove_abs_sub_le_one_of_nonRoot hp_ne hq_ne hpb hqb
  have hjump := card_filter_gt_sub_eq_card_filter_Ioc_sub_add
    (s := p.roots) (t := q.roots) hab
  rw [hjump]
  simpa using hbabs

/-- If the left polynomial has no roots in `(a, b)` and the right polynomial
has at least two roots in `(a, b)`, Liu-compatible root counts force the right
strict-upper count at `a` to exceed the left strict-upper count by exactly one.
-/
theorem RootCountCompatible.card_right_roots_gt_eq_left_roots_gt_add_one_of_left_no_isRoot_Ioo
    {p q : ℝ[X]} (h : RootCountCompatible p q)
    (hp_ne : p ≠ 0) (hq_ne : q ≠ 0) {a b : ℝ}
    (hab : a < b)
    (hp_no : ∀ z : ℝ, a < z → z < b → ¬ p.IsRoot z)
    (hqb : ¬ q.IsRoot b)
    (htwo : 2 ≤ (q.roots.filter (fun r => a < r ∧ r < b)).card) :
    (q.roots.filter (a < ·)).card = (p.roots.filter (a < ·)).card + 1 := by
  let P := (p.roots.filter (a < ·)).card
  let Qa := (q.roots.filter (a < ·)).card
  let Qb := (q.roots.filter (b < ·)).card
  let I := (q.roots.filter (fun r => a < r ∧ r < b)).card
  have hP_at_b : rootCountAtOrAbove p b = P := by
    have hfilter :
        p.roots.filter (fun r => b ≤ r) = p.roots.filter (a < ·) := by
      apply Multiset.filter_congr
      intro r hr
      constructor
      · intro hbr
        exact lt_of_lt_of_le hab hbr
      · intro har
        by_contra hbr
        exact hp_no r har (lt_of_not_ge hbr)
          ((Polynomial.mem_roots hp_ne).mp hr)
    simp [rootCountAtOrAbove, P, hfilter]
  have hQ_at_b : rootCountAtOrAbove q b = Qb := by
    simpa [Qb] using rootCountAtOrAbove_eq_rootCountAbove_of_not_isRoot
      hq_ne hqb
  have hP_Qb_le : ((P : ℤ) - Qb) ≤ 1 := by simpa [hP_at_b, hQ_at_b] using (h.bounds b).1
  have habove :=
    rootCountAbove_diff_le_one_of_nonRoot_isRoot hp_ne hq_ne
      (fun x hpx hqx =>
        h.rootCountAbove_bounds_of_nonRoot hp_ne hq_ne hpx hqx) a
  have hQa_P_le : ((Qa : ℤ) - P) ≤ 1 := by simpa [P, Qa] using habove.2
  have hq_not_mem_b : b ∉ q.roots := by
    intro hb_mem
    exact hqb ((Polynomial.mem_roots hq_ne).mp hb_mem)
  have hpart : I + Qb = Qa := by
    simpa [I, Qb, Qa] using
      card_filter_Ioo_add_card_filter_gt_eq_card_filter_gt_of_not_mem
        q.roots (le_of_lt hab) hq_not_mem_b
  have htwo' : 2 ≤ I := by simpa [I] using htwo
  have hQa_eq_int : (Qa : ℤ) = (P : ℤ) + 1 := by
    have hpart_int : (I : ℤ) + Qb = Qa := by exact_mod_cast hpart
    have htwo_int : (2 : ℤ) ≤ I := by exact_mod_cast htwo'
    linarith
  have hQa_eq : Qa = P + 1 := by exact_mod_cast hQa_eq_int
  simpa [P, Qa] using hQa_eq

/-- If the left polynomial has no roots in `(a, b)` and the right polynomial
has at least two roots in `(a, b)`, Liu-compatible root counts force opposite
parity between the left strict-upper count at `a` and the right strict-upper
count at `a`. -/
theorem RootCountCompatible.odd_card_roots_gt_add_of_left_no_isRoot_Ioo
    {p q : ℝ[X]} (h : RootCountCompatible p q)
    (hp_ne : p ≠ 0) (hq_ne : q ≠ 0) {a b : ℝ}
    (hab : a < b)
    (hp_no : ∀ z : ℝ, a < z → z < b → ¬ p.IsRoot z)
    (hqb : ¬ q.IsRoot b)
    (htwo : 2 ≤ (q.roots.filter (fun r => a < r ∧ r < b)).card) :
    Odd ((p.roots.filter (a < ·)).card +
      (q.roots.filter (a < ·)).card) := by
  let P := (p.roots.filter (a < ·)).card
  have hQa_eq :
      (q.roots.filter (a < ·)).card = P + 1 := by
    simpa [P] using
      h.card_right_roots_gt_eq_left_roots_gt_add_one_of_left_no_isRoot_Ioo
        hp_ne hq_ne hab hp_no hqb htwo
  refine ⟨P, ?_⟩
  change P + (q.roots.filter (a < ·)).card = 2 * P + 1
  rw [hQa_eq]
  ring

/-- Move a real threshold strictly downward without crossing any element of a
finite multiset. -/
theorem exists_threshold_no_mem_Ico_left (s : Multiset ℝ) (x : ℝ) :
    ∃ x' : ℝ, x' < x ∧ ∀ r ∈ s, r < x' ∨ x ≤ r := by
  classical
  set S : Finset ℝ := s.toFinset.filter (· < x) with hS
  by_cases hSne : S.Nonempty
  · set m : ℝ := S.max' hSne with hm
    have hmS : m ∈ S := Finset.max'_mem S hSne
    have hmx : m < x := by exact (Finset.mem_filter.mp hmS).2
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

/-- To prove Liu root-count compatibility, it is enough to prove the
corresponding strict-upper count bound at common non-root thresholds. -/
theorem RootCountCompatible.of_rootCountAbove_abs_sub_le_one_of_nonRoot
    {p q : ℝ[X]} (hp_ne : p ≠ 0) (hq_ne : q ≠ 0)
    (hbound : ∀ x : ℝ, ¬ p.IsRoot x → ¬ q.IsRoot x →
      |(((p.roots.filter (x < ·)).card : ℤ) -
          ((q.roots.filter (x < ·)).card : ℤ))| ≤ 1) :
    RootCountCompatible p q := by
  intro x
  obtain ⟨x', _, hpx', hqx', hpcount, hqcount⟩ :=
    exists_nonRoot_threshold_count_gt_eq_rootCountAtOrAbove hp_ne hq_ne x
  have hxabs := hbound x' hpx' hqx'
  rwa [hpcount, hqcount] at hxabs

theorem RootCountCompatible.of_rootCountAbove_bounds_of_nonRoot
    {p q : ℝ[X]} (hp_ne : p ≠ 0) (hq_ne : q ≠ 0)
    (hbound : ∀ x : ℝ, ¬ p.IsRoot x → ¬ q.IsRoot x →
      ((p.roots.filter (x < ·)).card : ℤ) -
          (q.roots.filter (x < ·)).card ≤ 1 ∧
        ((q.roots.filter (x < ·)).card : ℤ) -
          (p.roots.filter (x < ·)).card ≤ 1) :
    RootCountCompatible p q :=
  RootCountCompatible.of_rootCountAbove_abs_sub_le_one_of_nonRoot hp_ne hq_ne
    fun x hpx hqx => by
      have hxbound := hbound x hpx hqx
      rw [abs_le]
      exact ⟨by linarith [hxbound.2], hxbound.1⟩

end LiuOppositeSigns
end RealRooted
