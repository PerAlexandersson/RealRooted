import RealRooted.LiuOppositeSigns.RootCount

/-!
# Root deletion for Liu root-count arguments

This module contains the general cofactor, largest-root, and root-multiset
deletion lemmas used by Liu-style root-count arguments. It is independent of
positive-leading normalization and of the later left/right branch machinery.
-/

open Polynomial

noncomputable section

namespace RealRooted
namespace LiuOppositeSigns

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

/-- If both endpoints have a common root, the x-subtraction pencil factors by
the same linear root factor and the corresponding cofactor pencil. -/
theorem X_mul_sub_C_mul_eq_X_sub_C_mul_deleteRootFactor_of_commonRoot
    {p q : ℝ[X]} {r μ : ℝ} (hp : p.IsRoot r) (hq : q.IsRoot r) :
    X * p - C μ * q =
      (X - C r) * (X * deleteRootFactor p r -
        C μ * deleteRootFactor q r) := by
  calc
    X * p - C μ * q =
        X * ((X - C r) * deleteRootFactor p r) -
          C μ * ((X - C r) * deleteRootFactor q r) := by
        rw [factor_deleteRootFactor_of_isRoot hp,
          factor_deleteRootFactor_of_isRoot hq]
    _ = (X - C r) * (X * deleteRootFactor p r -
          C μ * deleteRootFactor q r) := by
        ring

/-- Splitting of the cofactor x-subtraction pencil lifts across a common
linear root factor, and conversely descends through that nonzero linear factor.
-/
theorem X_mul_sub_C_mul_splits_iff_deleteRootFactor_splits_of_commonRoot
    {p q : ℝ[X]} {r μ : ℝ} (hp : p.IsRoot r) (hq : q.IsRoot r) :
    (X * p - C μ * q).Splits ↔
      (X * deleteRootFactor p r -
        C μ * deleteRootFactor q r).Splits := by
  rw [X_mul_sub_C_mul_eq_X_sub_C_mul_deleteRootFactor_of_commonRoot hp hq]
  exact splits_mul_iff_right (X_sub_C_ne_zero r) (Polynomial.Splits.X_sub_C r)

/-- Deleting one degree from both endpoints preserves the left-successor degree
relation when the right endpoint has positive degree. -/
theorem natDegree_deleteRootFactor_left_eq_right_add_one_of_natDegree_eq
    {p q : ℝ[X]} {r : ℝ}
    (hdeg : p.natDegree = q.natDegree + 1) (hq_pos : 0 < q.natDegree) :
    (deleteRootFactor p r).natDegree =
      (deleteRootFactor q r).natDegree + 1 := by
  rw [natDegree_deleteRootFactor, natDegree_deleteRootFactor, hdeg]
  lia

/-- Deleting one degree from both endpoints preserves the right-successor degree
relation when the left endpoint has positive degree. -/
theorem natDegree_deleteRootFactor_right_eq_left_add_one_of_natDegree_eq
    {p q : ℝ[X]} {r : ℝ}
    (hdeg : q.natDegree = p.natDegree + 1) (hp_pos : 0 < p.natDegree) :
    (deleteRootFactor q r).natDegree =
      (deleteRootFactor p r).natDegree + 1 := by
  rw [natDegree_deleteRootFactor, natDegree_deleteRootFactor, hdeg]
  lia

/-- Deleting one root from both endpoints preserves the same-degree relation. -/
theorem natDegree_deleteRootFactor_eq_of_natDegree_eq
    {p q : ℝ[X]} {r : ℝ} (hdeg : p.natDegree = q.natDegree) :
    (deleteRootFactor p r).natDegree =
      (deleteRootFactor q r).natDegree := by
  rw [natDegree_deleteRootFactor, natDegree_deleteRootFactor, hdeg]

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

end LiuOppositeSigns
end RealRooted
