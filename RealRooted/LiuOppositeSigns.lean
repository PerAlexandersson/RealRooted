import RealRooted.Basic
import RealRooted.Linear
import RealRooted.Mathlib.Algebra.Polynomial.Eval.Defs
import RealRooted.RootCountJump

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
  have hq_le_int : (rootCountAtOrAbove q x : ℤ) ≤ 1 := by
    exact_mod_cast hq_le
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
  have hp_le_int : (rootCountAtOrAbove p x : ℤ) ≤ 1 := by
    exact_mod_cast hp_le
  have hq_le_int : (rootCountAtOrAbove q x : ℤ) ≤ 1 := by
    exact_mod_cast hq_le
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
    by_cases hxb : x ≤ b
    · norm_num [hxa, hxb, hxc]
    · norm_num [hxa, hxb, hxc]
  · by_cases hxb : x ≤ b
    · by_cases hxc : x ≤ c
      · norm_num [hxa, hxb, hxc]
      · norm_num [hxa, hxb, hxc]
    · by_cases hxc : x ≤ c
      · norm_num [hxa, hxb, hxc]
      · norm_num [hxa, hxb, hxc]

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
    by_cases hxd : x ≤ d
    · norm_num [hxa, hxc, hxd]
    · norm_num [hxa, hxc, hxd]
  · by_cases hxa : x ≤ a
    · by_cases hxd : x ≤ d
      · norm_num [hxa, hxc, hxd]
      · norm_num [hxa, hxc, hxd]
    · by_cases hxd : x ≤ d
      · norm_num [hxa, hxc, hxd]
      · norm_num [hxa, hxc, hxd]

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
  · have hxnegq : ¬ (-q).IsRoot x := by
      simpa using hxq
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
  · have hxnegp : ¬ (-p).IsRoot x := by
      simpa using hxp
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

theorem not_isRoot_of_not_deleteRootFactor_isRoot_of_lt
    {p : ℝ[X]} {r x : ℝ} (hr : p.IsRoot r) (hx : x < r)
    (hdelete : ¬ (deleteRootFactor p r).IsRoot x) :
    ¬ p.IsRoot x := by
  intro hpx
  have hx_factor : (X - C r : ℝ[X]).eval x ≠ 0 := by
    simp [sub_ne_zero, ne_of_lt hx]
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
  have hP_Qb_le : ((P : ℤ) - Qb) ≤ 1 := by
    simpa [hP_at_b, hQ_at_b] using (h.bounds b).1
  have habove :=
    rootCountAbove_diff_le_one_of_nonRoot_isRoot hp_ne hq_ne
      (fun x hpx hqx =>
        h.rootCountAbove_bounds_of_nonRoot hp_ne hq_ne hpx hqx) a
  have hQa_P_le : ((Qa : ℤ) - P) ≤ 1 := by
    simpa [P, Qa] using habove.2
  have hq_not_mem_b : b ∉ q.roots := by
    intro hb_mem
    exact hqb ((Polynomial.mem_roots hq_ne).mp hb_mem)
  have hpart : I + Qb = Qa := by
    simpa [I, Qb, Qa] using
      card_filter_Ioo_add_card_filter_gt_eq_card_filter_gt_of_not_mem
        q.roots (le_of_lt hab) hq_not_mem_b
  have htwo' : 2 ≤ I := by
    simpa [I] using htwo
  have hQa_eq_int : (Qa : ℤ) = (P : ℤ) + 1 := by
    have hpart_int : (I : ℤ) + Qb = Qa := by
      exact_mod_cast hpart
    have htwo_int : (2 : ℤ) ≤ I := by
      exact_mod_cast htwo'
    linarith
  have hQa_eq : Qa = P + 1 := by
    exact_mod_cast hQa_eq_int
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

theorem of_natDegree_le_one {p q : ℝ[X]}
    (hp_pos : HasPosLeadingCoeff p) (hq_pos : HasPosLeadingCoeff q)
    (hp_splits : p.Splits) (hq_splits : q.Splits)
    (hpdeg : p.natDegree ≤ 1) (hqdeg : q.natDegree ≤ 1) :
    PositiveSplitRootCountPair p q :=
  ⟨hp_pos, hq_pos, hp_splits, hq_splits,
    RootCountCompatible.of_natDegree_le_one hp_splits hq_splits hpdeg hqdeg⟩

theorem natDegree_abs_sub_le_one {p q : ℝ[X]}
    (h : PositiveSplitRootCountPair p q) :
    |((p.natDegree : ℤ) - (q.natDegree : ℤ))| ≤ 1 :=
  h.count.natDegree_abs_sub_le_one h.left_splits h.right_splits

/-- The x-subtraction pencil has degree at most one more than the left endpoint
polynomial under Liu's root-count-compatible positive split hypotheses. -/
theorem natDegree_X_mul_sub_C_mul_le_left_natDegree_add_one {p q : ℝ[X]}
    (h : PositiveSplitRootCountPair p q) (μ : ℝ) :
    (X * p - C μ * q).natDegree ≤ p.natDegree + 1 := by
  have hleft : (X * p).natDegree ≤ p.natDegree + 1 := by
    rw [Polynomial.natDegree_X_mul h.left_pos.ne_zero]
  have hq_le : q.natDegree ≤ p.natDegree + 1 := by
    have hgap := h.natDegree_abs_sub_le_one
    rw [abs_le] at hgap
    have hq_le_int : (q.natDegree : ℤ) ≤ (p.natDegree : ℤ) + 1 := by
      linarith
    exact_mod_cast hq_le_int
  have hright : (C μ * q).natDegree ≤ p.natDegree + 1 :=
    (Polynomial.natDegree_C_mul_le μ q).trans hq_le
  simpa using Polynomial.natDegree_sub_le_of_le hleft hright

theorem rootCountAbove_bounds_of_nonRoot {p q : ℝ[X]}
    (h : PositiveSplitRootCountPair p q) {x : ℝ}
    (hpx : ¬ p.IsRoot x) (hqx : ¬ q.IsRoot x) :
    ((p.roots.filter (x < ·)).card : ℤ) -
        (q.roots.filter (x < ·)).card ≤ 1 ∧
      ((q.roots.filter (x < ·)).card : ℤ) -
        (p.roots.filter (x < ·)).card ≤ 1 :=
  h.count.rootCountAbove_bounds_of_nonRoot
    h.left_pos.ne_zero h.right_pos.ne_zero hpx hqx

theorem card_right_roots_filter_gt_le_one_of_left_largest_root
    {p q : ℝ[X]} (h : PositiveSplitRootCountPair p q) {a : ℝ}
    (ha : IsLargestRoot p a) :
    (q.roots.filter (a < ·)).card ≤ 1 := by
  have hbound :=
    rootCountAbove_diff_le_one_of_nonRoot_isRoot
      h.left_pos.ne_zero h.right_pos.ne_zero
      (fun x hpx hqx => h.rootCountAbove_bounds_of_nonRoot hpx hqx) a
  have hp_zero : (p.roots.filter (a < ·)).card = 0 :=
    rootCountAbove_eq_zero_of_forall_roots_le fun r hr => ha.roots_le r hr
  have hq_le_int : ((q.roots.filter (a < ·)).card : ℤ) ≤ 1 := by
    simpa [hp_zero] using hbound.2
  exact_mod_cast hq_le_int

theorem card_right_roots_filter_lt_eq_zero_of_left_roots_ge_of_left_natDegree_eq_right_add_one
    {p q : ℝ[X]} (h : PositiveSplitRootCountPair p q) {a : ℝ}
    (hroots_ge : ∀ r ∈ p.roots, a ≤ r)
    (hdeg : p.natDegree = q.natDegree + 1) :
    (q.roots.filter (fun r => r < a)).card = 0 := by
  let lower := (q.roots.filter (fun r => r < a)).card
  let upper := rootCountAtOrAbove q a
  have hp_count : rootCountAtOrAbove p a = p.natDegree := by
    have hfilter : p.roots.filter (fun r => a ≤ r) = p.roots :=
      Multiset.filter_eq_self.mpr hroots_ge
    simp [rootCountAtOrAbove, hfilter, card_roots_of_splits h.left_splits]
  have hpart : lower + upper = q.natDegree := by
    have hcard := congrArg Multiset.card
      (Multiset.filter_add_not (p := fun r : ℝ => r < a) q.roots)
    have hnot : q.roots.filter (fun r : ℝ => ¬ r < a) =
        q.roots.filter (fun r : ℝ => a ≤ r) := by
      apply Multiset.filter_congr
      intro r _hr
      simp [not_lt]
    rw [Multiset.card_add] at hcard
    simpa [lower, upper, rootCountAtOrAbove, hnot, card_roots_of_splits h.right_splits]
      using hcard
  by_contra hlower_ne
  have hlower_pos : 0 < lower := Nat.pos_of_ne_zero hlower_ne
  have hbound : ((p.natDegree : ℤ) - upper) ≤ 1 := by
    simpa [hp_count, upper] using (h.count.bounds a).1
  have hpart_int : (lower : ℤ) + upper = q.natDegree := by
    exact_mod_cast hpart
  have hlower_int : (1 : ℤ) ≤ lower := by
    exact_mod_cast hlower_pos
  have hdeg_int : (p.natDegree : ℤ) = q.natDegree + 1 := by
    exact_mod_cast hdeg
  linarith

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

theorem
    rootCountCompatible_deleteRootFactor_left_of_natDegree_le_two_right_le_one
    {f g : ℝ[X]} {r : ℝ}
    (hf_splits : f.Splits) (hg_splits : g.Splits)
    (hr : f.IsRoot r) (hfdeg : f.natDegree ≤ 2)
    (hgdeg : g.natDegree ≤ 1) :
    RootCountCompatible (deleteRootFactor f r) g := by
  have hdelete_deg : (deleteRootFactor f r).natDegree ≤ 1 := by
    rw [natDegree_deleteRootFactor]
    lia
  exact RootCountCompatible.of_natDegree_le_one
    (deleteRootFactor_splits_of_isRoot hf_splits hr) hg_splits
    hdelete_deg hgdeg

theorem
    rootCountCompatible_left_deleteRootFactor_of_left_le_one_right_le_two
    {f g : ℝ[X]} {s : ℝ}
    (hf_splits : f.Splits) (hg_splits : g.Splits)
    (hs : g.IsRoot s) (hfdeg : f.natDegree ≤ 1)
    (hgdeg : g.natDegree ≤ 2) :
    RootCountCompatible f (deleteRootFactor g s) := by
  have hdelete_deg : (deleteRootFactor g s).natDegree ≤ 1 := by
    rw [natDegree_deleteRootFactor]
    lia
  exact RootCountCompatible.of_natDegree_le_one hf_splits
    (deleteRootFactor_splits_of_isRoot hg_splits hs) hfdeg hdelete_deg

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

theorem rootCountAbove_deleteRootFactor_add_one
    {p : ℝ[X]} {r x : ℝ} (hp_ne : p ≠ 0) (h : IsLargestRoot p r)
    (hx : x < r) :
    (p.roots.filter (x < ·)).card =
      ((deleteRootFactor p r).roots.filter (x < ·)).card + 1 :=
  rootCountAbove_deleteRootFactor_add_one_of_isRoot hp_ne h.isRoot hx

theorem rootCountAtOrAbove_eq_zero_of_lt
    {p : ℝ[X]} {r x : ℝ} (h : IsLargestRoot p r) (hx : r < x) :
    rootCountAtOrAbove p x = 0 :=
  rootCountAtOrAbove_eq_zero_of_forall_roots_lt fun s hs =>
    lt_of_le_of_lt (h.roots_le s hs) hx

theorem rootCountAbove_eq_zero_of_le
    {p : ℝ[X]} {r x : ℝ} (h : IsLargestRoot p r) (hx : r ≤ x) :
    (p.roots.filter (x < ·)).card = 0 :=
  rootCountAbove_eq_zero_of_forall_roots_le fun s hs =>
    (h.roots_le s hs).trans hx

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

theorem rootCountAbove_deleteRootFactor_eq_zero_of_le
    {p : ℝ[X]} {r x : ℝ} (hp_ne : p ≠ 0) (h : IsLargestRoot p r)
    (hx : r ≤ x) :
    ((deleteRootFactor p r).roots.filter (x < ·)).card = 0 := by
  have hdelete_ne := h.deleteRootFactor_ne_zero hp_ne
  exact rootCountAbove_eq_zero_of_forall_roots_le fun s hs =>
    (h.root_deleteRootFactor_le hp_ne ((Polynomial.mem_roots hdelete_ne).mp hs)).trans hx

/-- For an ordered two-root multiset, the largest-root certificate selects the
right entry. -/
theorem eq_right_of_roots_pair {p : ℝ[X]} {r a b : ℝ}
    (hp_ne : p ≠ 0) (h : IsLargestRoot p r) (hab : a ≤ b)
    (hroots : p.roots = {a, b}) :
    r = b := by
  have hb_mem : b ∈ p.roots := by
    rw [hroots]
    simp only [Multiset.insert_eq_cons]
    simp
  have hb_le_r : b ≤ r := h.roots_le b hb_mem
  have hr_mem : r ∈ p.roots := h.mem_roots hp_ne
  have hr_le_b : r ≤ b := by
    rw [hroots] at hr_mem
    simp only [Multiset.insert_eq_cons] at hr_mem
    simp only [Multiset.mem_cons, Multiset.mem_singleton] at hr_mem
    rcases hr_mem with hr_eq_a | hr_eq_b
    · rw [hr_eq_a]
      exact hab
    · rw [hr_eq_b]
  exact le_antisymm hr_le_b hb_le_r

/-- For an ordered three-root multiset, the largest-root certificate selects
the right entry. -/
theorem eq_right_of_roots_triple {p : ℝ[X]} {r a b c : ℝ}
    (hp_ne : p ≠ 0) (h : IsLargestRoot p r) (hab : a ≤ b) (hbc : b ≤ c)
    (hroots : p.roots = {a, b, c}) :
    r = c := by
  have hc_mem : c ∈ p.roots := by
    rw [hroots]
    simp only [Multiset.insert_eq_cons]
    simp
  have hc_le_r : c ≤ r := h.roots_le c hc_mem
  have hr_mem : r ∈ p.roots := h.mem_roots hp_ne
  have hr_le_c : r ≤ c := by
    rw [hroots] at hr_mem
    simp only [Multiset.insert_eq_cons] at hr_mem
    simp only [Multiset.mem_cons, Multiset.mem_singleton] at hr_mem
    rcases hr_mem with hr_eq_a | hr_eq_b | hr_eq_c
    · rw [hr_eq_a]
      exact hab.trans hbc
    · rw [hr_eq_b]
      exact hbc
    · rw [hr_eq_c]
  exact le_antisymm hr_le_c hc_le_r

end IsLargestRoot

/-- If a split quadratic has roots `{a, b}` and is factored accordingly, then
deleting the right root leaves the singleton root `{a}`. -/
theorem roots_deleteRootFactor_eq_singleton_of_roots_pair_right
    {p : ℝ[X]} {a b : ℝ} (hp_ne : p ≠ 0)
    (hroots : p.roots = {a, b})
    (hfac : p = C p.leadingCoeff * ((X - C a) * (X - C b))) :
    (deleteRootFactor p b).roots = {a} := by
  have hbroot : p.IsRoot b :=
    (Polynomial.mem_roots hp_ne).mp (by
      rw [hroots]
      simp only [Multiset.insert_eq_cons]
      simp)
  have hlc : p.leadingCoeff ≠ 0 := mt leadingCoeff_eq_zero.mp hp_ne
  have hdelete_eq : deleteRootFactor p b = C p.leadingCoeff * (X - C a) := by
    apply mul_left_cancel₀ (X_sub_C_ne_zero b)
    calc
      (X - C b) * deleteRootFactor p b = p :=
        factor_deleteRootFactor_of_isRoot hbroot
      _ = C p.leadingCoeff * ((X - C a) * (X - C b)) := hfac
      _ = (X - C b) * (C p.leadingCoeff * (X - C a)) := by ring
  rw [hdelete_eq, Polynomial.roots_C_mul _ hlc, roots_X_sub_C]

/-- If a split cubic has roots `{a, b, c}` and is factored accordingly, then
deleting the right root leaves the pair of remaining roots `{a, b}`. -/
theorem roots_deleteRootFactor_eq_pair_of_roots_triple_right
    {p : ℝ[X]} {a b c : ℝ} (hp_ne : p ≠ 0)
    (hroots : p.roots = {a, b, c})
    (hfac : p = C p.leadingCoeff * ((X - C a) * (X - C b) * (X - C c))) :
    (deleteRootFactor p c).roots = {a, b} := by
  have hcroot : p.IsRoot c :=
    (Polynomial.mem_roots hp_ne).mp (by
      rw [hroots]
      simp only [Multiset.insert_eq_cons]
      simp)
  have hlc : p.leadingCoeff ≠ 0 := mt leadingCoeff_eq_zero.mp hp_ne
  have hdelete_eq :
      deleteRootFactor p c = C p.leadingCoeff * ((X - C a) * (X - C b)) := by
    apply mul_left_cancel₀ (X_sub_C_ne_zero c)
    calc
      (X - C c) * deleteRootFactor p c = p :=
        factor_deleteRootFactor_of_isRoot hcroot
      _ = C p.leadingCoeff * ((X - C a) * (X - C b) * (X - C c)) := hfac
      _ = (X - C c) * (C p.leadingCoeff * ((X - C a) * (X - C b))) := by ring
  rw [hdelete_eq, Polynomial.roots_C_mul _ hlc]
  have hprod_ne : (X - C a) * (X - C b) ≠ (0 : ℝ[X]) :=
    mul_ne_zero (X_sub_C_ne_zero a) (X_sub_C_ne_zero b)
  rw [Polynomial.roots_mul hprod_ne, roots_X_sub_C, roots_X_sub_C]
  rfl

/-- Consecutive combined roots in a root-free gap are owned by opposite
polynomials whenever the strict-upper root-count difference is not odd at a
sample point in the gap. -/
def CrossOwnedNotOddGaps (f g : ℝ[X]) : Prop :=
  ∀ a b x : ℝ, a < x → x < b →
    (f.IsRoot a ∨ g.IsRoot a) →
    (f.IsRoot b ∨ g.IsRoot b) →
    (∀ z : ℝ, a < z → z < b → ¬ f.IsRoot z ∧ ¬ g.IsRoot z) →
    ¬ Odd (((f.roots.filter (x < ·)).card : ℤ) -
      (g.roots.filter (x < ·)).card) →
    (f.IsRoot a ∧ g.IsRoot b) ∨ (g.IsRoot a ∧ f.IsRoot b)

theorem CrossOwnedNotOddGaps.symm {f g : ℝ[X]} (h : CrossOwnedNotOddGaps f g) :
    CrossOwnedNotOddGaps g f := by
  intro a b x hax hxb ha_root hb_root hgap hnot_odd
  refine (h a b x hax hxb ha_root.symm hb_root.symm
    (fun z haz hzb => (hgap z haz hzb).symm) ?_).symm
  intro hodd
  have hneg := hodd.neg
  rw [neg_sub] at hneg
  exact hnot_odd hneg

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

/-- If `f` is linear and `g` has degree at most two, the right deletion branch
has Liu-compatible root counts by degree alone. -/
theorem of_largestRoots_left_le_one_right_le_two
    {f g : ℝ[X]} {r s : ℝ}
    (hf_splits : f.Splits) (hg_splits : g.Splits)
    (hr : IsLargestRoot f r) (hs : IsLargestRoot g s)
    (hlargest : r < s) (hfdeg : f.natDegree ≤ 1)
    (hgdeg : g.natDegree ≤ 2) :
    RightRootCountBranch f g r s where
  f_largest := hr
  g_largest := hs
  largest_lt := hlargest
  count :=
    rootCountCompatible_left_deleteRootFactor_of_left_le_one_right_le_two
      hf_splits hg_splits hs.isRoot hfdeg hgdeg

/-- If the right endpoint is cubic and deleting its displayed largest root
leaves two roots whose interval overlaps the left two-root interval, then the
right Liu branch has compatible root counts. -/
theorem of_roots_pair_triple_right
    {f g : ℝ[X]} {r s a b c d : ℝ}
    (hr : IsLargestRoot f r) (hs : IsLargestRoot g s) (hlargest : r < s)
    (had : a ≤ d) (hcb : c ≤ b)
    (hfroots : f.roots = {a, b}) (hgroots : g.roots = {c, d, s})
    (hgfac : g = C g.leadingCoeff * ((X - C c) * (X - C d) * (X - C s)))
    (hg_ne : g ≠ 0) :
    RightRootCountBranch f g r s where
  f_largest := hr
  g_largest := hs
  largest_lt := hlargest
  count := by
    have hdelete_roots : (deleteRootFactor g s).roots = {c, d} :=
      roots_deleteRootFactor_eq_pair_of_roots_triple_right hg_ne hgroots hgfac
    exact RootCountCompatible.of_roots_pair_pair had hcb hfroots hdelete_roots

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

/-- If `f` has degree at most two and `g` is linear, the left deletion branch
has Liu-compatible root counts by degree alone. -/
theorem of_largestRoots_natDegree_le_two_right_le_one
    {f g : ℝ[X]} {r s : ℝ}
    (hf_splits : f.Splits) (hg_splits : g.Splits)
    (hr : IsLargestRoot f r) (hs : IsLargestRoot g s)
    (hlargest : s ≤ r) (hfdeg : f.natDegree ≤ 2)
    (hgdeg : g.natDegree ≤ 1) :
    LeftRootCountBranch f g r s where
  f_largest := hr
  g_largest := hs
  largest_ge := hlargest
  count :=
    rootCountCompatible_deleteRootFactor_left_of_natDegree_le_two_right_le_one
      hf_splits hg_splits hr.isRoot hfdeg hgdeg

/-- If the left endpoint is cubic and deleting its displayed largest root
leaves two roots whose interval overlaps the right two-root interval, then the
left Liu branch has compatible root counts. -/
theorem of_roots_triple_pair_right
    {f g : ℝ[X]} {r s a b c d : ℝ}
    (hr : IsLargestRoot f r) (hs : IsLargestRoot g s) (hlargest : s ≤ r)
    (had : a ≤ d) (hcb : c ≤ b)
    (hfroots : f.roots = {a, b, r})
    (hffac : f = C f.leadingCoeff * ((X - C a) * (X - C b) * (X - C r)))
    (hgroots : g.roots = {c, d}) (hf_ne : f ≠ 0) :
    LeftRootCountBranch f g r s where
  f_largest := hr
  g_largest := hs
  largest_ge := hlargest
  count := by
    have hdelete_roots : (deleteRootFactor f r).roots = {a, b} :=
      roots_deleteRootFactor_eq_pair_of_roots_triple_right hf_ne hfroots hffac
    exact RootCountCompatible.of_roots_pair_pair had hcb hdelete_roots hgroots

/-- To prove the left Liu deletion branch, it is enough to control the
strict-upper root counts of the deletion pair at common non-root thresholds. -/
theorem of_rootCountAbove_delete_abs_sub_le_one_of_nonRoot
    {f g : ℝ[X]} {r s : ℝ} (hf_ne : f ≠ 0) (hg_ne : g ≠ 0)
    (hr : IsLargestRoot f r) (hs : IsLargestRoot g s) (hlargest : s ≤ r)
    (hbound : ∀ x : ℝ, ¬ (deleteRootFactor f r).IsRoot x → ¬ g.IsRoot x →
      |((((deleteRootFactor f r).roots.filter (x < ·)).card : ℤ) -
          ((g.roots.filter (x < ·)).card : ℤ))| ≤ 1) :
    LeftRootCountBranch f g r s where
  f_largest := hr
  g_largest := hs
  largest_ge := hlargest
  count :=
    RootCountCompatible.of_rootCountAbove_abs_sub_le_one_of_nonRoot
      (hr.deleteRootFactor_ne_zero hf_ne) hg_ne hbound

theorem of_rootCountAbove_left_sub_right_bounds_of_nonRoot
    {f g : ℝ[X]} {r s : ℝ} (hf_ne : f ≠ 0) (hg_ne : g ≠ 0)
    (hr : IsLargestRoot f r) (hs : IsLargestRoot g s) (hlargest : s ≤ r)
    (hbound : ∀ x : ℝ, ¬ f.IsRoot x → ¬ g.IsRoot x →
      0 ≤ ((f.roots.filter (x < ·)).card : ℤ) -
          (g.roots.filter (x < ·)).card ∧
        ((f.roots.filter (x < ·)).card : ℤ) -
          (g.roots.filter (x < ·)).card ≤ 2) :
    LeftRootCountBranch f g r s := by
  refine LeftRootCountBranch.of_rootCountAbove_delete_abs_sub_le_one_of_nonRoot
    hf_ne hg_ne hr hs hlargest ?_
  intro x hdeletex hgx
  by_cases hx : x < r
  · have hfx : ¬ f.IsRoot x :=
      not_isRoot_of_not_deleteRootFactor_isRoot_of_lt hr.isRoot hx hdeletex
    have hwin := hbound x hfx hgx
    have hcount :
        ((f.roots.filter (x < ·)).card : ℤ) =
          ((deleteRootFactor f r).roots.filter (x < ·)).card + 1 := by
      exact_mod_cast hr.rootCountAbove_deleteRootFactor_add_one hf_ne hx
    rw [hcount] at hwin
    rw [abs_le]
    constructor <;> linarith
  · have hx_ge : r ≤ x := le_of_not_gt hx
    have hdelete_zero :=
      hr.rootCountAbove_deleteRootFactor_eq_zero_of_le hf_ne hx_ge
    have hg_zero := hs.rootCountAbove_eq_zero_of_le (hlargest.trans hx_ge)
    rw [hdelete_zero, hg_zero]
    norm_num

/-- A below-largest suffix-count criterion for the left branch.  It is enough
to prove the original strict-upper `f`-minus-`g` root-count bounds at common
non-root thresholds below the largest root of `f`; thresholds at or above that
largest root have zero strict-upper counts for both polynomials. -/
theorem of_rootCountAbove_left_sub_right_bounds_below_largest_of_nonRoot
    {f g : ℝ[X]} {r s : ℝ} (hf_ne : f ≠ 0) (hg_ne : g ≠ 0)
    (hr : IsLargestRoot f r) (hs : IsLargestRoot g s) (hlargest : s ≤ r)
    (hbound : ∀ x : ℝ, x < r → ¬ f.IsRoot x → ¬ g.IsRoot x →
      0 ≤ ((f.roots.filter (x < ·)).card : ℤ) -
          (g.roots.filter (x < ·)).card ∧
        ((f.roots.filter (x < ·)).card : ℤ) -
          (g.roots.filter (x < ·)).card ≤ 2) :
    LeftRootCountBranch f g r s := by
  refine LeftRootCountBranch.of_rootCountAbove_left_sub_right_bounds_of_nonRoot
    hf_ne hg_ne hr hs hlargest ?_
  intro x hfx hgx
  by_cases hx : x < r
  · exact hbound x hx hfx hgx
  · have hx_ge : r ≤ x := not_lt.mp hx
    have hf_zero := hr.rootCountAbove_eq_zero_of_le hx_ge
    have hg_zero := hs.rootCountAbove_eq_zero_of_le (hlargest.trans hx_ge)
    rw [hf_zero, hg_zero]
    norm_num

/-- Finite descent for the left Liu branch.  A one-sided root-count upper bound
and parity-guarded cross-ownership in root-free gaps force the least combined
root above a common non-root threshold to carry the exact owner/difference
invariant needed for the left strict-upper count bound. -/
theorem owner_diff_of_crossOwned_consecutive_roots_of_left_sub_le_one
    {f g : ℝ[X]} {r s : ℝ} (hf_ne : f ≠ 0) (hg_ne : g ≠ 0)
    (hr : IsLargestRoot f r) (hs : IsLargestRoot g s) (hlargest : s ≤ r)
    (hupper : ∀ x : ℝ, ¬ f.IsRoot x → ¬ g.IsRoot x →
      ((f.roots.filter (x < ·)).card : ℤ) -
        (g.roots.filter (x < ·)).card ≤ 1)
    (hsimple_f : ∀ c : ℝ, f.IsRoot c → f.roots.count c = 1)
    (hsimple_g : ∀ c : ℝ, g.IsRoot c → g.roots.count c = 1)
    (hdisj : ∀ c : ℝ, f.IsRoot c → ¬ g.IsRoot c)
    (hcross : CrossOwnedNotOddGaps f g) :
    ∀ x : ℝ, x < r → ¬ f.IsRoot x → ¬ g.IsRoot x →
      ∃ c : ℝ, x < c ∧ (f.IsRoot c ∨ g.IsRoot c) ∧
        (∀ z : ℝ, x < z → f.IsRoot z ∨ g.IsRoot z → c ≤ z) ∧
          ((f.IsRoot c ∧
              ((f.roots.filter (x < ·)).card : ℤ) -
                (g.roots.filter (x < ·)).card = 1) ∨
            (g.IsRoot c ∧
              ((f.roots.filter (x < ·)).card : ℤ) -
                (g.roots.filter (x < ·)).card = 0)) := by
  let μ : ℝ → ℕ := fun x => ((f.roots + g.roots).filter (x < ·)).card
  let P : ℝ → Prop := fun x =>
    x < r → ¬ f.IsRoot x → ¬ g.IsRoot x →
      ∃ c : ℝ, x < c ∧ (f.IsRoot c ∨ g.IsRoot c) ∧
        (∀ z : ℝ, x < z → f.IsRoot z ∨ g.IsRoot z → c ≤ z) ∧
          ((f.IsRoot c ∧
              ((f.roots.filter (x < ·)).card : ℤ) -
                (g.roots.filter (x < ·)).card = 1) ∨
            (g.IsRoot c ∧
              ((f.roots.filter (x < ·)).card : ℤ) -
                (g.roots.filter (x < ·)).card = 0))
  change ∀ x : ℝ, P x
  refine WellFounded.fix (measure μ).wf ?_
  intro x ih hx hfx hgx
  obtain ⟨c, hcroot, hxc, hleast⟩ :=
    exists_least_isRoot_or_isRoot_gt hf_ne hg_ne (Or.inl hr.isRoot) hx
  have hc_mem : c ∈ f.roots + g.roots :=
    (mem_roots_add_iff_isRoot_or_isRoot hf_ne hg_ne).mpr hcroot
  obtain ⟨b, hcb, hfb, hgb, hgap_f, hgap_g⟩ :=
    exists_common_nonRoot_threshold_no_mem_Ioc hf_ne hg_ne c
  have hxb : x < b := hxc.trans hcb
  have hmeasure : μ b < μ x := by
    dsimp [μ]
    exact card_filter_gt_lt_of_mem_Ioc (f.roots + g.roots)
      (le_of_lt hxb) hc_mem hxc (le_of_lt hcb)
  have hstep_f : ∀ {k : ℤ}, f.IsRoot c →
      ((f.roots.filter (b < ·)).card : ℤ) - (g.roots.filter (b < ·)).card = k →
      ((f.roots.filter (x < ·)).card : ℤ) - (g.roots.filter (x < ·)).card =
        k + 1 := by
    intro k hfc hk
    exact card_roots_filter_gt_sub_eq_add_one_of_left_least_root_no_mem_Ioc
      hf_ne hg_ne hxc (le_of_lt hcb) (hdisj c hfc) (hsimple_f c hfc)
      hleast hgap_f hgap_g hk
  refine ⟨c, hxc, hcroot, hleast, ?_⟩
  by_cases hnext : ∃ d : ℝ, b < d ∧ (f.IsRoot d ∨ g.IsRoot d)
  · obtain ⟨d₀, hbd₀, hd₀root⟩ := hnext
    have hd₀_le_r : d₀ ≤ r := by
      rcases hd₀root with hdf | hdg
      · exact hr.roots_le d₀ ((Polynomial.mem_roots hf_ne).mpr hdf)
      · exact (hs.roots_le d₀ ((Polynomial.mem_roots hg_ne).mpr hdg)).trans hlargest
    have hbr : b < r := hbd₀.trans_le hd₀_le_r
    obtain ⟨d, hbd, hdroot, hdleast, howner_d⟩ := ih b hmeasure hbr hfb hgb
    have hbetween :
        ∀ z : ℝ, c < z → z < d → ¬ f.IsRoot z ∧ ¬ g.IsRoot z := by
      intro z hcz hzd
      constructor
      · intro hfz
        have hz_mem : z ∈ f.roots := (Polynomial.mem_roots hf_ne).mpr hfz
        rcases hgap_f z hz_mem with hzc | hbz
        · exact (not_lt_of_ge hzc) hcz
        · exact (not_lt_of_ge (hdleast z hbz (Or.inl hfz))) hzd
      · intro hgz
        have hz_mem : z ∈ g.roots := (Polynomial.mem_roots hg_ne).mpr hgz
        rcases hgap_g z hz_mem with hzc | hbz
        · exact (not_lt_of_ge hzc) hcz
        · exact (not_lt_of_ge (hdleast z hbz (Or.inr hgz))) hzd
    rcases howner_d with ⟨hdf, hdiff_b⟩ | ⟨hdg, hdiff_b⟩
    · rcases hcroot with hfc | hgc
      · have hdiff := hstep_f hfc hdiff_b
        have hle :
            ((f.roots.filter (x < ·)).card : ℤ) -
                (g.roots.filter (x < ·)).card ≤ 1 :=
          hupper x hfx hgx
        exact False.elim (by linarith)
      · have hfc_not : ¬ f.IsRoot c := by
          intro hfc
          exact hdisj c hfc hgc
        have hdiff :=
          card_roots_filter_gt_sub_eq_sub_one_of_right_least_root_no_mem_Ioc
            hf_ne hg_ne hxc (le_of_lt hcb) hfc_not (hsimple_g c hgc)
            hleast hgap_f hgap_g hdiff_b
        exact Or.inr ⟨hgc, by simpa using hdiff⟩
    · have hnot_odd_b : ¬ Odd (((f.roots.filter (b < ·)).card : ℤ) -
          (g.roots.filter (b < ·)).card) := by
        simp [hdiff_b]
      have hcross_cd := hcross c d b hcb hbd hcroot hdroot hbetween hnot_odd_b
      have hfc : f.IsRoot c := by
        rcases hcross_cd with ⟨hfc, _hgd⟩ | ⟨_hgc, hfd⟩
        · exact hfc
        · exact False.elim (hdisj d hfd hdg)
      have hdiff := hstep_f hfc hdiff_b
      exact Or.inl ⟨hfc, by simpa using hdiff⟩
  · have hno_above :
        ∀ z : ℝ, b < z → ¬ f.IsRoot z ∧ ¬ g.IsRoot z := by
      intro z hbz
      constructor
      · intro hfz
        exact hnext ⟨z, hbz, Or.inl hfz⟩
      · intro hgz
        exact hnext ⟨z, hbz, Or.inr hgz⟩
    have hdiff_b :=
      card_roots_filter_gt_sub_eq_zero_of_no_isRoot_or_isRoot_gt
        hf_ne hg_ne hno_above
    have hcr : c ≤ r := hleast r hx (Or.inl hr.isRoot)
    have hrc : r ≤ c := by
      by_contra hnot
      have hcr_lt : c < r := lt_of_not_ge hnot
      by_cases hrb : r ≤ b
      · have hr_mem : r ∈ f.roots := (Polynomial.mem_roots hf_ne).mpr hr.isRoot
        rcases hgap_f r hr_mem with hle | hlt <;> linarith
      · exact False.elim (hnext ⟨r, lt_of_not_ge hrb, Or.inl hr.isRoot⟩)
    have hcr_eq : c = r := le_antisymm hcr hrc
    have hfc : f.IsRoot c := by
      simpa [hcr_eq] using hr.isRoot
    have hdiff := hstep_f hfc hdiff_b
    exact Or.inl ⟨hfc, hdiff⟩

/-- Compatible root counts supply the one-sided upper bound used by the finite
descent. -/
theorem rootCountAbove_owner_diff_of_crossOwned_consecutive_roots
    {f g : ℝ[X]} {r s : ℝ} (hf_ne : f ≠ 0) (hg_ne : g ≠ 0)
    (hr : IsLargestRoot f r) (hs : IsLargestRoot g s) (hlargest : s ≤ r)
    (hcount : RootCountCompatible f g)
    (hsimple_f : ∀ c : ℝ, f.IsRoot c → f.roots.count c = 1)
    (hsimple_g : ∀ c : ℝ, g.IsRoot c → g.roots.count c = 1)
    (hdisj : ∀ c : ℝ, f.IsRoot c → ¬ g.IsRoot c)
    (hcross : CrossOwnedNotOddGaps f g) :
    ∀ x : ℝ, x < r → ¬ f.IsRoot x → ¬ g.IsRoot x →
      ∃ c : ℝ, x < c ∧ (f.IsRoot c ∨ g.IsRoot c) ∧
        (∀ z : ℝ, x < z → f.IsRoot z ∨ g.IsRoot z → c ≤ z) ∧
          ((f.IsRoot c ∧
              ((f.roots.filter (x < ·)).card : ℤ) -
                (g.roots.filter (x < ·)).card = 1) ∨
            (g.IsRoot c ∧
              ((f.roots.filter (x < ·)).card : ℤ) -
                (g.roots.filter (x < ·)).card = 0)) :=
  owner_diff_of_crossOwned_consecutive_roots_of_left_sub_le_one
    hf_ne hg_ne hr hs hlargest
    (fun _ hfx hgx => hcount.rootCountAbove_left_sub_le_one_of_nonRoot
      hf_ne hg_ne hfx hgx)
    hsimple_f hsimple_g hdisj hcross

/-- Finite descent for the left Liu branch with the root-count window that
appears in Theorem 2.1.  In the `r_1 >= s_1` orientation, cross-owned finite
gaps force the original strict-upper difference to stay in `[0, 2]`; the
owner of the least root above the threshold gives the sharper local alternative
used in the induction. -/
theorem owner_diff_bounds_of_crossOwned_consecutive_roots
    {f g : ℝ[X]} {r s : ℝ} (hf_ne : f ≠ 0) (hg_ne : g ≠ 0)
    (hr : IsLargestRoot f r) (hs : IsLargestRoot g s) (hlargest : s ≤ r)
    (hsimple_f : ∀ c : ℝ, f.IsRoot c → f.roots.count c = 1)
    (hsimple_g : ∀ c : ℝ, g.IsRoot c → g.roots.count c = 1)
    (hdisj : ∀ c : ℝ, f.IsRoot c → ¬ g.IsRoot c)
    (hcross : CrossOwnedNotOddGaps f g) :
    ∀ x : ℝ, x < r → ¬ f.IsRoot x → ¬ g.IsRoot x →
      ∃ c : ℝ, x < c ∧ (f.IsRoot c ∨ g.IsRoot c) ∧
        (∀ z : ℝ, x < z → f.IsRoot z ∨ g.IsRoot z → c ≤ z) ∧
          ((f.IsRoot c ∧
              1 ≤ ((f.roots.filter (x < ·)).card : ℤ) -
                (g.roots.filter (x < ·)).card ∧
              ((f.roots.filter (x < ·)).card : ℤ) -
                (g.roots.filter (x < ·)).card ≤ 2) ∨
            (g.IsRoot c ∧
              0 ≤ ((f.roots.filter (x < ·)).card : ℤ) -
                (g.roots.filter (x < ·)).card ∧
              ((f.roots.filter (x < ·)).card : ℤ) -
                (g.roots.filter (x < ·)).card ≤ 1)) := by
  let μ : ℝ → ℕ := fun x => ((f.roots + g.roots).filter (x < ·)).card
  let P : ℝ → Prop := fun x =>
    x < r → ¬ f.IsRoot x → ¬ g.IsRoot x →
      ∃ c : ℝ, x < c ∧ (f.IsRoot c ∨ g.IsRoot c) ∧
        (∀ z : ℝ, x < z → f.IsRoot z ∨ g.IsRoot z → c ≤ z) ∧
          ((f.IsRoot c ∧
              1 ≤ ((f.roots.filter (x < ·)).card : ℤ) -
                (g.roots.filter (x < ·)).card ∧
              ((f.roots.filter (x < ·)).card : ℤ) -
                (g.roots.filter (x < ·)).card ≤ 2) ∨
            (g.IsRoot c ∧
              0 ≤ ((f.roots.filter (x < ·)).card : ℤ) -
                (g.roots.filter (x < ·)).card ∧
              ((f.roots.filter (x < ·)).card : ℤ) -
                (g.roots.filter (x < ·)).card ≤ 1))
  change ∀ x : ℝ, P x
  refine WellFounded.fix (measure μ).wf ?_
  intro x ih hx hfx hgx
  obtain ⟨c, hcroot, hxc, hleast⟩ :=
    exists_least_isRoot_or_isRoot_gt hf_ne hg_ne (Or.inl hr.isRoot) hx
  have hc_mem : c ∈ f.roots + g.roots :=
    (mem_roots_add_iff_isRoot_or_isRoot hf_ne hg_ne).mpr hcroot
  obtain ⟨b, hcb, hfb, hgb, hgap_f, hgap_g⟩ :=
    exists_common_nonRoot_threshold_no_mem_Ioc hf_ne hg_ne c
  have hxb : x < b := hxc.trans hcb
  have hmeasure : μ b < μ x := by
    dsimp [μ]
    exact card_filter_gt_lt_of_mem_Ioc (f.roots + g.roots)
      (le_of_lt hxb) hc_mem hxc (le_of_lt hcb)
  have hstep_f : f.IsRoot c →
      ((f.roots.filter (x < ·)).card : ℤ) -
          (g.roots.filter (x < ·)).card =
        ((f.roots.filter (b < ·)).card : ℤ) -
          (g.roots.filter (b < ·)).card + 1 := by
    intro hfc
    exact card_roots_filter_gt_sub_eq_add_one_of_left_least_root_no_mem_Ioc
      hf_ne hg_ne hxc (le_of_lt hcb) (hdisj c hfc) (hsimple_f c hfc)
      hleast hgap_f hgap_g rfl
  have hstep_g : g.IsRoot c →
      ((f.roots.filter (x < ·)).card : ℤ) -
          (g.roots.filter (x < ·)).card =
        ((f.roots.filter (b < ·)).card : ℤ) -
          (g.roots.filter (b < ·)).card - 1 := by
    intro hgc
    have hfc_not : ¬ f.IsRoot c := by
      intro hfc
      exact hdisj c hfc hgc
    exact card_roots_filter_gt_sub_eq_sub_one_of_right_least_root_no_mem_Ioc
      hf_ne hg_ne hxc (le_of_lt hcb) hfc_not (hsimple_g c hgc)
      hleast hgap_f hgap_g rfl
  refine ⟨c, hxc, hcroot, hleast, ?_⟩
  by_cases hnext : ∃ d : ℝ, b < d ∧ (f.IsRoot d ∨ g.IsRoot d)
  · have hbr : b < r := by
      obtain ⟨d₀, hbd₀, hd₀root⟩ := hnext
      have hd₀_le_r : d₀ ≤ r := by
        rcases hd₀root with hdf | hdg
        · exact hr.roots_le d₀ ((Polynomial.mem_roots hf_ne).mpr hdf)
        · exact (hs.roots_le d₀ ((Polynomial.mem_roots hg_ne).mpr hdg)).trans hlargest
      exact hbd₀.trans_le hd₀_le_r
    obtain ⟨d, hbd, hdroot, hdleast, howner_d⟩ := ih b hmeasure hbr hfb hgb
    have hbetween :
        ∀ z : ℝ, c < z → z < d → ¬ f.IsRoot z ∧ ¬ g.IsRoot z := by
      intro z hcz hzd
      constructor
      · intro hfz
        have hz_mem : z ∈ f.roots := (Polynomial.mem_roots hf_ne).mpr hfz
        rcases hgap_f z hz_mem with hzc | hbz
        · exact (not_lt_of_ge hzc) hcz
        · exact (not_lt_of_ge (hdleast z hbz (Or.inl hfz))) hzd
      · intro hgz
        have hz_mem : z ∈ g.roots := (Polynomial.mem_roots hg_ne).mpr hgz
        rcases hgap_g z hz_mem with hzc | hbz
        · exact (not_lt_of_ge hzc) hcz
        · exact (not_lt_of_ge (hdleast z hbz (Or.inr hgz))) hzd
    rcases howner_d with ⟨hdf, hdiff_b_low, hdiff_b_high⟩ |
        ⟨hdg, hdiff_b_low, hdiff_b_high⟩
    · rcases hcroot with hfc | hgc
      · have hdiff_b_ne_two :
            ((f.roots.filter (b < ·)).card : ℤ) -
                (g.roots.filter (b < ·)).card ≠ 2 := by
          intro hdiff_b_eq
          have hnot_odd_b : ¬ Odd (((f.roots.filter (b < ·)).card : ℤ) -
              (g.roots.filter (b < ·)).card) := by
            simp [hdiff_b_eq]
          have hcross_cd :=
            hcross c d b hcb hbd (Or.inl hfc) hdroot hbetween hnot_odd_b
          rcases hcross_cd with ⟨_hfc, hgd⟩ | ⟨hgc, _hfd⟩
          · exact hdisj d hdf hgd
          · exact hdisj c hfc hgc
        have hdiff_b_lt_two :
            ((f.roots.filter (b < ·)).card : ℤ) -
                (g.roots.filter (b < ·)).card < 2 :=
          lt_of_le_of_ne hdiff_b_high hdiff_b_ne_two
        have hdiff := hstep_f hfc
        exact Or.inl ⟨hfc, by linarith, by linarith⟩
      · have hdiff := hstep_g hgc
        exact Or.inr ⟨hgc, by linarith, by linarith⟩
    · rcases hcroot with hfc | hgc
      · have hdiff := hstep_f hfc
        exact Or.inl ⟨hfc, by linarith, by linarith⟩
      · have hdiff_b_ne_zero :
            ((f.roots.filter (b < ·)).card : ℤ) -
                (g.roots.filter (b < ·)).card ≠ 0 := by
          intro hdiff_b_eq
          have hnot_odd_b : ¬ Odd (((f.roots.filter (b < ·)).card : ℤ) -
              (g.roots.filter (b < ·)).card) := by
            simp [hdiff_b_eq]
          have hcross_cd :=
            hcross c d b hcb hbd (Or.inr hgc) hdroot hbetween hnot_odd_b
          rcases hcross_cd with ⟨hfc, _hgd⟩ | ⟨_hgc, hfd⟩
          · exact hdisj c hfc hgc
          · exact hdisj d hfd hdg
        have hdiff_b_pos :
            0 < ((f.roots.filter (b < ·)).card : ℤ) -
                (g.roots.filter (b < ·)).card :=
          lt_of_le_of_ne hdiff_b_low (Ne.symm hdiff_b_ne_zero)
        have hdiff := hstep_g hgc
        exact Or.inr ⟨hgc, by linarith, by linarith⟩
  · have hno_above :
        ∀ z : ℝ, b < z → ¬ f.IsRoot z ∧ ¬ g.IsRoot z := by
      intro z hbz
      constructor
      · intro hfz
        exact hnext ⟨z, hbz, Or.inl hfz⟩
      · intro hgz
        exact hnext ⟨z, hbz, Or.inr hgz⟩
    have hdiff_b :=
      card_roots_filter_gt_sub_eq_zero_of_no_isRoot_or_isRoot_gt
        hf_ne hg_ne hno_above
    have hcr : c ≤ r := hleast r hx (Or.inl hr.isRoot)
    have hrc : r ≤ c := by
      by_contra hnot
      have hcr_lt : c < r := lt_of_not_ge hnot
      by_cases hrb : r ≤ b
      · have hr_mem : r ∈ f.roots := (Polynomial.mem_roots hf_ne).mpr hr.isRoot
        rcases hgap_f r hr_mem with hle | hlt <;> linarith
      · exact False.elim (hnext ⟨r, lt_of_not_ge hrb, Or.inl hr.isRoot⟩)
    have hcr_eq : c = r := le_antisymm hcr hrc
    have hfc : f.IsRoot c := by
      simpa [hcr_eq] using hr.isRoot
    have hdiff := hstep_f hfc
    exact Or.inl ⟨hfc, by linarith, by linarith⟩

theorem rootCountAbove_bounds_of_crossOwned_consecutive_roots
    {f g : ℝ[X]} {r s : ℝ} (hf_ne : f ≠ 0) (hg_ne : g ≠ 0)
    (hr : IsLargestRoot f r) (hs : IsLargestRoot g s) (hlargest : s ≤ r)
    (hsimple_f : ∀ c : ℝ, f.IsRoot c → f.roots.count c = 1)
    (hsimple_g : ∀ c : ℝ, g.IsRoot c → g.roots.count c = 1)
    (hdisj : ∀ c : ℝ, f.IsRoot c → ¬ g.IsRoot c)
    (hcross : CrossOwnedNotOddGaps f g) :
    ∀ x : ℝ, x < r → ¬ f.IsRoot x → ¬ g.IsRoot x →
      0 ≤ ((f.roots.filter (x < ·)).card : ℤ) -
          (g.roots.filter (x < ·)).card ∧
        ((f.roots.filter (x < ·)).card : ℤ) -
          (g.roots.filter (x < ·)).card ≤ 2 := by
  intro x hx hfx hgx
  obtain ⟨_c, _hxc, _hcroot, _hleast, howner⟩ :=
    owner_diff_bounds_of_crossOwned_consecutive_roots
      hf_ne hg_ne hr hs hlargest hsimple_f hsimple_g hdisj hcross
      x hx hfx hgx
  rcases howner with ⟨_hfc, hlow, hhigh⟩ | ⟨_hgc, hlow, hhigh⟩
  · exact ⟨by linarith, hhigh⟩
  · exact ⟨hlow, by linarith⟩

theorem of_crossOwned_consecutive_roots
    {f g : ℝ[X]} {r s : ℝ} (hf_ne : f ≠ 0) (hg_ne : g ≠ 0)
    (hr : IsLargestRoot f r) (hs : IsLargestRoot g s) (hlargest : s ≤ r)
    (hsimple_f : ∀ c : ℝ, f.IsRoot c → f.roots.count c = 1)
    (hsimple_g : ∀ c : ℝ, g.IsRoot c → g.roots.count c = 1)
    (hdisj : ∀ c : ℝ, f.IsRoot c → ¬ g.IsRoot c)
    (hcross : CrossOwnedNotOddGaps f g) :
    LeftRootCountBranch f g r s :=
  LeftRootCountBranch.of_rootCountAbove_left_sub_right_bounds_below_largest_of_nonRoot
    hf_ne hg_ne hr hs hlargest
    (rootCountAbove_bounds_of_crossOwned_consecutive_roots
      hf_ne hg_ne hr hs hlargest hsimple_f hsimple_g hdisj hcross)

theorem right_le_left_of_crossOwned_consecutive_roots_of_left_sub_le_one
    {f g : ℝ[X]} {r s : ℝ} (hf_ne : f ≠ 0) (hg_ne : g ≠ 0)
    (hr : IsLargestRoot f r) (hs : IsLargestRoot g s) (hlargest : s ≤ r)
    (hupper : ∀ x : ℝ, ¬ f.IsRoot x → ¬ g.IsRoot x →
      ((f.roots.filter (x < ·)).card : ℤ) -
        (g.roots.filter (x < ·)).card ≤ 1)
    (hsimple_f : ∀ c : ℝ, f.IsRoot c → f.roots.count c = 1)
    (hsimple_g : ∀ c : ℝ, g.IsRoot c → g.roots.count c = 1)
    (hdisj : ∀ c : ℝ, f.IsRoot c → ¬ g.IsRoot c)
    (hcross : CrossOwnedNotOddGaps f g) :
    ∀ x : ℝ, x < r → ¬ f.IsRoot x → ¬ g.IsRoot x →
      (g.roots.filter (x < ·)).card ≤ (f.roots.filter (x < ·)).card := by
  intro x hx hfx hgx
  obtain ⟨_c, _hxc, _hcroot, _hleast, howner⟩ :=
    owner_diff_of_crossOwned_consecutive_roots_of_left_sub_le_one
      hf_ne hg_ne hr hs hlargest hupper hsimple_f hsimple_g hdisj hcross
      x hx hfx hgx
  have hle_int :
      ((g.roots.filter (x < ·)).card : ℤ) ≤
        (f.roots.filter (x < ·)).card := by
    rcases howner with ⟨_hfc, hdiff⟩ | ⟨_hgc, hdiff⟩ <;> linarith
  exact_mod_cast hle_int

theorem rootCountAbove_right_le_left_of_crossOwned_consecutive_roots
    {f g : ℝ[X]} {r s : ℝ} (hf_ne : f ≠ 0) (hg_ne : g ≠ 0)
    (hr : IsLargestRoot f r) (hs : IsLargestRoot g s) (hlargest : s ≤ r)
    (hcount : RootCountCompatible f g)
    (hsimple_f : ∀ c : ℝ, f.IsRoot c → f.roots.count c = 1)
    (hsimple_g : ∀ c : ℝ, g.IsRoot c → g.roots.count c = 1)
    (hdisj : ∀ c : ℝ, f.IsRoot c → ¬ g.IsRoot c)
    (hcross : CrossOwnedNotOddGaps f g) :
    ∀ x : ℝ, x < r → ¬ f.IsRoot x → ¬ g.IsRoot x →
      (g.roots.filter (x < ·)).card ≤ (f.roots.filter (x < ·)).card :=
  right_le_left_of_crossOwned_consecutive_roots_of_left_sub_le_one
    hf_ne hg_ne hr hs hlargest
    (fun _ hfx hgx => hcount.rootCountAbove_left_sub_le_one_of_nonRoot
      hf_ne hg_ne hfx hgx)
    hsimple_f hsimple_g hdisj hcross

theorem of_left_sub_right_upper_of_right_le_left
    {f g : ℝ[X]} {r s : ℝ} (hf_ne : f ≠ 0) (hg_ne : g ≠ 0)
    (hr : IsLargestRoot f r) (hs : IsLargestRoot g s) (hlargest : s ≤ r)
    (hupper : ∀ x : ℝ, ¬ f.IsRoot x → ¬ g.IsRoot x →
      ((f.roots.filter (x < ·)).card : ℤ) -
        (g.roots.filter (x < ·)).card ≤ 2)
    (hle : ∀ x : ℝ, x < r → ¬ f.IsRoot x → ¬ g.IsRoot x →
      (g.roots.filter (x < ·)).card ≤ (f.roots.filter (x < ·)).card) :
    LeftRootCountBranch f g r s := by
  refine
    LeftRootCountBranch.of_rootCountAbove_left_sub_right_bounds_below_largest_of_nonRoot
      hf_ne hg_ne hr hs hlargest ?_
  intro x hx hfx hgx
  constructor
  · have hxle :
        ((g.roots.filter (x < ·)).card : ℤ) ≤
          (f.roots.filter (x < ·)).card := by
      exact_mod_cast hle x hx hfx hgx
    linarith
  · exact hupper x hfx hgx

private theorem of_left_sub_right_le_one_of_right_le_left
    {f g : ℝ[X]} {r s : ℝ} (hf_ne : f ≠ 0) (hg_ne : g ≠ 0)
    (hr : IsLargestRoot f r) (hs : IsLargestRoot g s) (hlargest : s ≤ r)
    (hupper : ∀ x : ℝ, ¬ f.IsRoot x → ¬ g.IsRoot x →
      ((f.roots.filter (x < ·)).card : ℤ) -
        (g.roots.filter (x < ·)).card ≤ 1)
    (hle : ∀ x : ℝ, x < r → ¬ f.IsRoot x → ¬ g.IsRoot x →
      (g.roots.filter (x < ·)).card ≤ (f.roots.filter (x < ·)).card) :
    LeftRootCountBranch f g r s :=
  of_left_sub_right_upper_of_right_le_left hf_ne hg_ne hr hs hlargest
    (fun x hfx hgx => by
      have hle_one := hupper x hfx hgx
      linarith)
    hle

theorem of_rootCountCompatible_of_rootCountAbove_right_le_left
    {f g : ℝ[X]} {r s : ℝ} (hf_ne : f ≠ 0) (hg_ne : g ≠ 0)
    (hr : IsLargestRoot f r) (hs : IsLargestRoot g s) (hlargest : s ≤ r)
    (hcount : RootCountCompatible f g)
    (hle : ∀ x : ℝ, x < r → ¬ f.IsRoot x → ¬ g.IsRoot x →
      (g.roots.filter (x < ·)).card ≤ (f.roots.filter (x < ·)).card) :
    LeftRootCountBranch f g r s :=
  of_left_sub_right_le_one_of_right_le_left hf_ne hg_ne hr hs hlargest
    (fun _ hfx hgx => hcount.rootCountAbove_left_sub_le_one_of_nonRoot
      hf_ne hg_ne hfx hgx)
    hle

/-- Swap a left Liu branch for `(g, f)` into the corresponding right branch
for `(f, g)`.  The extra strict inequality supplies the strict largest-root
condition required by the right branch, while the root-count field is obtained
by `RootCountCompatible.symm`. -/
theorem toRightBranch_symm_of_lt {f g : ℝ[X]} {r s : ℝ}
    (h : LeftRootCountBranch g f s r) (hlargest : r < s) :
    RightRootCountBranch f g r s where
  f_largest := h.g_largest
  g_largest := h.f_largest
  largest_lt := hlargest
  count := h.count.symm

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
  have hupper := hcommon.1.natDegree_le_succ
  have hlower := hcommon.2.natDegree_le
  lia

theorem commonInterleaver_natDegree_eq_or_eq_succ_of_succDegree
    {f g k : ℝ[X]} {r s : ℝ}
    (h : LeftRootCountBranch f g r s) (hf_ne : f ≠ 0)
    (hdeg : f.natDegree = g.natDegree + 1)
    (hcommon : Prec (deleteRootFactor f r) k ∧ Prec g k) :
    k.natDegree = g.natDegree ∨ k.natDegree = g.natDegree + 1 := by
  have hdelete := h.delete_natDegree_eq_of_succDegree hf_ne hdeg
  have hupper := hcommon.1.natDegree_le_succ
  have hlower := hcommon.2.natDegree_le
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
  have hlower := hcommon.1.natDegree_le
  have hupper := hcommon.2.natDegree_le_succ
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

/-- To prove the right Liu deletion branch, it is enough to control the
strict-upper root counts of the deletion pair at common non-root thresholds. -/
theorem of_rootCountAbove_delete_abs_sub_le_one_of_nonRoot
    {f g : ℝ[X]} {r s : ℝ} (hf_ne : f ≠ 0) (hg_ne : g ≠ 0)
    (hr : IsLargestRoot f r) (hs : IsLargestRoot g s) (hlargest : r < s)
    (hbound : ∀ x : ℝ, ¬ f.IsRoot x → ¬ (deleteRootFactor g s).IsRoot x →
      |(((f.roots.filter (x < ·)).card : ℤ) -
          (((deleteRootFactor g s).roots.filter (x < ·)).card : ℤ))| ≤ 1) :
    RightRootCountBranch f g r s where
  f_largest := hr
  g_largest := hs
  largest_lt := hlargest
  count :=
    RootCountCompatible.of_rootCountAbove_abs_sub_le_one_of_nonRoot
      hf_ne (hs.deleteRootFactor_ne_zero hg_ne) hbound

theorem of_rootCountAbove_right_sub_left_bounds_of_nonRoot
    {f g : ℝ[X]} {r s : ℝ} (hf_ne : f ≠ 0) (hg_ne : g ≠ 0)
    (hr : IsLargestRoot f r) (hs : IsLargestRoot g s) (hlargest : r < s)
    (hbound : ∀ x : ℝ, ¬ f.IsRoot x → ¬ g.IsRoot x →
      0 ≤ ((g.roots.filter (x < ·)).card : ℤ) -
          (f.roots.filter (x < ·)).card ∧
        ((g.roots.filter (x < ·)).card : ℤ) -
          (f.roots.filter (x < ·)).card ≤ 2) :
    RightRootCountBranch f g r s := by
  have hleft : LeftRootCountBranch g f s r :=
    LeftRootCountBranch.of_rootCountAbove_left_sub_right_bounds_of_nonRoot
      hg_ne hf_ne hs hr hlargest.le fun x hgx hfx => hbound x hfx hgx
  exact hleft.toRightBranch_symm_of_lt hlargest

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
  have hlower := hcommon.1.natDegree_le
  have hupper := hcommon.2.natDegree_le_succ
  lia

theorem commonInterleaver_natDegree_eq_or_eq_succ_of_succDegree
    {f g k : ℝ[X]} {r s : ℝ}
    (h : RightRootCountBranch f g r s) (hg_ne : g ≠ 0)
    (hdeg : g.natDegree = f.natDegree + 1)
    (hcommon : Prec f k ∧ Prec (deleteRootFactor g s) k) :
    k.natDegree = f.natDegree ∨ k.natDegree = f.natDegree + 1 := by
  have hdelete := h.delete_natDegree_eq_of_succDegree hg_ne hdeg
  have hlower := hcommon.1.natDegree_le
  have hupper := hcommon.2.natDegree_le_succ
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
  have hupper := hcommon.1.natDegree_le_succ
  have hlower := hcommon.2.natDegree_le
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

/-- Choose Liu's deletion branch from the two possible largest-root
orientations.  If `s ≤ r`, use the supplied left branch for `(f, g)`; if
`r < s`, use the supplied left branch for `(g, f)` and swap it to a right
branch. -/
theorem theorem21RootCountBranches_of_leftBranch_orientations
    {f g : ℝ[X]} {r s : ℝ}
    (hfg : s ≤ r → LeftRootCountBranch f g r s)
    (hgf : r < s → LeftRootCountBranch g f s r) :
    theorem21RootCountBranches f g := by
  rcases le_or_gt s r with hsr | hrs
  · exact theorem21RootCountBranches_of_left (hfg hsr)
  · exact theorem21RootCountBranches_of_right ((hgf hrs).toRightBranch_symm_of_lt hrs)

/-- Branch-level bridge from parity-guarded cross-owned consecutive roots to
Liu's largest-root deletion branch predicate.  In the larger-largest-root
orientation, the finite descent proves the `0..2` original strict-upper window
needed after deleting that largest root. -/
theorem theorem21RootCountBranches_of_crossOwned_consecutive_roots
    {f g : ℝ[X]} (hf_ne : f ≠ 0) (hg_ne : g ≠ 0)
    {r s : ℝ} (hr : IsLargestRoot f r) (hs : IsLargestRoot g s)
    (hsimple_f : ∀ c : ℝ, f.IsRoot c → f.roots.count c = 1)
    (hsimple_g : ∀ c : ℝ, g.IsRoot c → g.roots.count c = 1)
    (hdisj : ∀ c : ℝ, f.IsRoot c → ¬ g.IsRoot c)
    (hcross : CrossOwnedNotOddGaps f g) :
    theorem21RootCountBranches f g :=
  theorem21RootCountBranches_of_leftBranch_orientations (r := r) (s := s)
    (fun hsr =>
      LeftRootCountBranch.of_crossOwned_consecutive_roots
        hf_ne hg_ne hr hs hsr hsimple_f hsimple_g hdisj hcross)
    (fun hrs =>
      LeftRootCountBranch.of_crossOwned_consecutive_roots
        hg_ne hf_ne hs hr hrs.le hsimple_g hsimple_f
        (fun c hgc hfc => hdisj c hfc hgc) hcross.symm)

/-- Branch-level bridge from parity-guarded cross-owned consecutive roots and
one-sided strict-upper root-count bounds to Liu's largest-root deletion branch.
This route requires stronger one-sided `≤ 1` hypotheses than the general
cross-owned count-window theorem
`theorem21RootCountBranches_of_crossOwned_consecutive_roots`. -/
theorem theorem21RootCountBranches_of_left_sub_le_one_of_crossOwned_consecutive_roots
    {f g : ℝ[X]} (hf_ne : f ≠ 0) (hg_ne : g ≠ 0)
    {r s : ℝ} (hr : IsLargestRoot f r) (hs : IsLargestRoot g s)
    (hupper_fg : ∀ x : ℝ, ¬ f.IsRoot x → ¬ g.IsRoot x →
      ((f.roots.filter (x < ·)).card : ℤ) -
        (g.roots.filter (x < ·)).card ≤ 1)
    (hupper_gf : ∀ x : ℝ, ¬ g.IsRoot x → ¬ f.IsRoot x →
      ((g.roots.filter (x < ·)).card : ℤ) -
        (f.roots.filter (x < ·)).card ≤ 1)
    (hsimple_f : ∀ c : ℝ, f.IsRoot c → f.roots.count c = 1)
    (hsimple_g : ∀ c : ℝ, g.IsRoot c → g.roots.count c = 1)
    (hdisj : ∀ c : ℝ, f.IsRoot c → ¬ g.IsRoot c)
    (hcross : CrossOwnedNotOddGaps f g) :
    theorem21RootCountBranches f g := by
  refine theorem21RootCountBranches_of_leftBranch_orientations (r := r) (s := s) ?_ ?_
  · intro hsr
    exact
      LeftRootCountBranch.of_left_sub_right_le_one_of_right_le_left
        hf_ne hg_ne hr hs hsr hupper_fg
        (LeftRootCountBranch.right_le_left_of_crossOwned_consecutive_roots_of_left_sub_le_one
          hf_ne hg_ne hr hs hsr hupper_fg hsimple_f hsimple_g hdisj hcross)
  · intro hrs
    exact
      LeftRootCountBranch.of_left_sub_right_le_one_of_right_le_left
        hg_ne hf_ne hs hr hrs.le hupper_gf
        (LeftRootCountBranch.right_le_left_of_crossOwned_consecutive_roots_of_left_sub_le_one
          hg_ne hf_ne hs hr hrs.le hupper_gf hsimple_g hsimple_f
          (fun c hgc hfc => hdisj c hfc hgc) hcross.symm)

/-- Branch-level bridge from parity-guarded cross-owned consecutive roots to
Liu's largest-root deletion branch predicate.  Compatible root counts supply the
two one-sided strict-upper bounds needed by the one-sided descent theorem. -/
theorem theorem21RootCountBranches_of_rootCountCompatible_of_crossOwned_consecutive_roots
    {f g : ℝ[X]} (hf_ne : f ≠ 0) (hg_ne : g ≠ 0)
    {r s : ℝ} (hr : IsLargestRoot f r) (hs : IsLargestRoot g s)
    (hcount : RootCountCompatible f g)
    (hsimple_f : ∀ c : ℝ, f.IsRoot c → f.roots.count c = 1)
    (hsimple_g : ∀ c : ℝ, g.IsRoot c → g.roots.count c = 1)
    (hdisj : ∀ c : ℝ, f.IsRoot c → ¬ g.IsRoot c)
    (hcross : CrossOwnedNotOddGaps f g) :
    theorem21RootCountBranches f g :=
  theorem21RootCountBranches_of_left_sub_le_one_of_crossOwned_consecutive_roots
    hf_ne hg_ne hr hs
    (fun _ hfx hgx => hcount.rootCountAbove_left_sub_le_one_of_nonRoot
      hf_ne hg_ne hfx hgx)
    (fun _ hgx hfx => hcount.symm.rootCountAbove_left_sub_le_one_of_nonRoot
      hg_ne hf_ne hgx hfx)
    hsimple_f hsimple_g hdisj hcross

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
