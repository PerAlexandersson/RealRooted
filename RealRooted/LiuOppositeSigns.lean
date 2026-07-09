import RealRooted.Basic

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

theorem RootCountCompatible.refl (p : ℝ[X]) : RootCountCompatible p p := by
  intro x
  simp

theorem RootCountCompatible.symm {p q : ℝ[X]} (h : RootCountCompatible p q) :
    RootCountCompatible q p := by
  intro x
  simpa [RootCountCompatible, abs_sub_comm] using h x

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

theorem deleteRootFactor_ne_zero_of_isRoot {p : ℝ[X]} {r : ℝ}
    (hp_ne : p ≠ 0) (hr : p.IsRoot r) :
    deleteRootFactor p r ≠ 0 := by
  intro hzero
  apply hp_ne
  rw [← factor_deleteRootFactor_of_isRoot hr, hzero, mul_zero]

theorem deleteRootFactor_splits_of_isRoot {p : ℝ[X]} {r : ℝ}
    (hp_splits : p.Splits) (hr : p.IsRoot r) :
    (deleteRootFactor p r).Splits := by
  have hsplit_factor : ((X - C r) * deleteRootFactor p r).Splits := by
    simpa [factor_deleteRootFactor_of_isRoot hr] using hp_splits
  exact Polynomial.splits_X_sub_C_mul_iff.mp hsplit_factor

theorem leadingCoeff_deleteRootFactor_of_isRoot {p : ℝ[X]} {r : ℝ}
    (hp_ne : p ≠ 0) (hr : p.IsRoot r) :
    (deleteRootFactor p r).leadingCoeff = p.leadingCoeff := by
  have hdeg_ne : p.degree ≠ 0 :=
    ne_of_gt (Polynomial.degree_pos_of_root hp_ne hr)
  simpa [deleteRootFactor] using
    Polynomial.leadingCoeff_divByMonic_X_sub_C p hdeg_ne r

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

theorem deleteRootFactor_ne_zero {p : ℝ[X]} {r : ℝ} (hp_ne : p ≠ 0)
    (h : IsLargestRoot p r) :
    deleteRootFactor p r ≠ 0 :=
  deleteRootFactor_ne_zero_of_isRoot hp_ne h.isRoot

theorem deleteRootFactor_splits {p : ℝ[X]} {r : ℝ} (hp_splits : p.Splits)
    (h : IsLargestRoot p r) :
    (deleteRootFactor p r).Splits :=
  deleteRootFactor_splits_of_isRoot hp_splits h.isRoot

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

/-- The root-count branch conclusion in Liu Theorem 2.1, separated from the
larger compatibility/common-interleaver statement. -/
def theorem21RootCountBranches (f g : ℝ[X]) : Prop :=
  ∃ r s, LeftRootCountBranch f g r s ∨ RightRootCountBranch f g r s

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

namespace LeftRootCountBranch

theorem delete_splits {f g : ℝ[X]} {r s : ℝ}
    (h : LeftRootCountBranch f g r s) (hf_splits : f.Splits) :
    (deleteRootFactor f r).Splits :=
  h.f_largest.deleteRootFactor_splits hf_splits

theorem delete_ne_zero {f g : ℝ[X]} {r s : ℝ}
    (h : LeftRootCountBranch f g r s) (hf_ne : f ≠ 0) :
    deleteRootFactor f r ≠ 0 :=
  h.f_largest.deleteRootFactor_ne_zero hf_ne

theorem root_delete_le {f g : ℝ[X]} {r s t : ℝ}
    (h : LeftRootCountBranch f g r s) (hf_ne : f ≠ 0)
    (ht : (deleteRootFactor f r).IsRoot t) :
    t ≤ r :=
  h.f_largest.root_deleteRootFactor_le hf_ne ht

theorem natDegree_abs_sub_le_two {f g : ℝ[X]} {r s : ℝ}
    (h : LeftRootCountBranch f g r s) (hf_ne : f ≠ 0)
    (hf_splits : f.Splits) (hg_splits : g.Splits) :
    |((f.natDegree : ℤ) - (g.natDegree : ℤ))| ≤ 2 := by
  have hgap := h.count.natDegree_abs_sub_le_one (h.delete_splits hf_splits)
    hg_splits
  have hf_degree_pos : 0 < f.natDegree :=
    h.f_largest.natDegree_pos hf_ne
  have hdelete_succ : (deleteRootFactor f r).natDegree + 1 = f.natDegree := by
    rw [natDegree_deleteRootFactor]
    simpa [Nat.succ_eq_add_one] using Nat.succ_pred_eq_of_pos hf_degree_pos
  have hdelete_int :
      ((deleteRootFactor f r).natDegree : ℤ) + 1 = (f.natDegree : ℤ) := by
    exact_mod_cast hdelete_succ
  exact int_abs_sub_le_two_of_add_one_left hdelete_int hgap

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

theorem root_delete_le {f g : ℝ[X]} {r s t : ℝ}
    (h : RightRootCountBranch f g r s) (hg_ne : g ≠ 0)
    (ht : (deleteRootFactor g s).IsRoot t) :
    t ≤ s :=
  h.g_largest.root_deleteRootFactor_le hg_ne ht

theorem natDegree_abs_sub_le_two {f g : ℝ[X]} {r s : ℝ}
    (h : RightRootCountBranch f g r s) (hg_ne : g ≠ 0)
    (hf_splits : f.Splits) (hg_splits : g.Splits) :
    |((f.natDegree : ℤ) - (g.natDegree : ℤ))| ≤ 2 := by
  have hgap := h.count.natDegree_abs_sub_le_one hf_splits
    (h.delete_splits hg_splits)
  have hg_degree_pos : 0 < g.natDegree :=
    h.g_largest.natDegree_pos hg_ne
  have hdelete_succ : (deleteRootFactor g s).natDegree + 1 = g.natDegree := by
    rw [natDegree_deleteRootFactor]
    simpa [Nat.succ_eq_add_one] using Nat.succ_pred_eq_of_pos hg_degree_pos
  have hdelete_int :
      ((deleteRootFactor g s).natDegree : ℤ) + 1 = (g.natDegree : ℤ) := by
    exact_mod_cast hdelete_succ
  exact int_abs_sub_le_two_of_add_one_right hdelete_int hgap

end RightRootCountBranch

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
