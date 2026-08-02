import RealRooted.LiuOppositeSigns
import RealRooted.Mathlib.Data.Multiset.Rel

/-!
# Sorted root matching

An arbitrary close perfect matching of two real multisets can be uncrossed into
a close pointwise matching of their ascending sorts.  This is the finite
ordered-root input for limiting interlacing and root-count inequalities.
-/

namespace RealRooted

/-- A close multiset matching pairs corresponding ascending order statistics. -/
theorem forall₂_sort_of_rel_abs_sub_lt
    {s t : Multiset ℝ} {ρ : ℝ}
    (hrel : Multiset.Rel (fun x y : ℝ => |y - x| < ρ) s t) :
    List.Forall₂ (fun x y : ℝ => |y - x| < ρ)
      (s.sort (· ≤ ·)) (t.sort (· ≤ ·)) := by
  refine Multiset.Rel.forall₂_sort ?_ hrel
  intro a c b d hac hbd had hcb
  rw [abs_lt] at had hcb ⊢
  constructor <;> constructor <;> linarith

/-- A close multiset matching pairs corresponding descending order statistics. -/
theorem forall₂_sort_ge_of_rel_abs_sub_lt
    {s t : Multiset ℝ} {ρ : ℝ}
    (hrel : Multiset.Rel (fun x y : ℝ => |y - x| < ρ) s t) :
    List.Forall₂ (fun x y : ℝ => |y - x| < ρ)
      (s.sort (· ≥ ·)) (t.sort (· ≥ ·)) := by
  change List.Forall₂
    (fun x y : OrderDual ℝ =>
      |OrderDual.ofDual y - OrderDual.ofDual x| < ρ)
    ((show Multiset (OrderDual ℝ) from s).sort (· ≤ ·))
    ((show Multiset (OrderDual ℝ) from t).sort (· ≤ ·))
  apply Multiset.Rel.forall₂_sort
  · intro a c b d hac hbd had hcb
    change OrderDual.ofDual c ≤ OrderDual.ofDual a at hac
    change OrderDual.ofDual d ≤ OrderDual.ofDual b at hbd
    rw [abs_lt] at had hcb ⊢
    constructor <;> constructor <;> linarith
  · exact hrel

/-- A largest root is the head of the descending root list. -/
theorem IsLargestRoot.roots_sort_ge_eq_cons
    {p : ℝ[X]} {r : ℝ} (hp_ne : p ≠ 0) (h : IsLargestRoot p r) :
    p.roots.sort (· ≥ ·) =
      r :: (deleteRootFactor p r).roots.sort (· ≥ ·) := by
  rw [h.roots_eq_singleton_add_roots_deleteRootFactor hp_ne,
    Multiset.singleton_add]
  apply Multiset.sort_cons
  intro x hx
  exact h.root_deleteRootFactor_le hp_ne
    ((Polynomial.mem_roots (h.deleteRootFactor_ne_zero hp_ne)).mp hx)

/-- Deleting matched largest roots preserves the matching of descending roots. -/
theorem forall₂_sort_ge_deleteRootFactor_of_roots_rel
    {p q : ℝ[X]} {r s ρ : ℝ} (hp_ne : p ≠ 0) (hq_ne : q ≠ 0)
    (hr : IsLargestRoot p r) (hs : IsLargestRoot q s)
    (hrel : Multiset.Rel
      (fun x y : ℝ => |y - x| < ρ) p.roots q.roots) :
    List.Forall₂ (fun x y : ℝ => |y - x| < ρ)
      ((deleteRootFactor p r).roots.sort (· ≥ ·))
      ((deleteRootFactor q s).roots.sort (· ≥ ·)) := by
  have hsort := forall₂_sort_ge_of_rel_abs_sub_lt hrel
  rw [hr.roots_sort_ge_eq_cons hp_ne,
    hs.roots_sort_ge_eq_cons hq_ne] at hsort
  exact (List.forall₂_cons.mp hsort).2

/-- A weak scalar inequality is closed under arbitrarily close approximations. -/
theorem le_of_forall_pos_exists_close_le {x y : ℝ}
    (h : ∀ ρ : ℝ, 0 < ρ →
      ∃ x' y' : ℝ, |x' - x| < ρ ∧ |y' - y| < ρ ∧ x' ≤ y') :
    x ≤ y := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨x', y', hx, hy, hxy⟩ := h (ε / 2) (half_pos hε)
  rw [abs_lt] at hx hy
  linarith

/-- Pointwise list inequalities are closed under arbitrarily close approximations. -/
theorem forall₂_le_of_forall_pos_exists_close
    {xs ys : List ℝ}
    (h : ∀ ρ : ℝ, 0 < ρ →
      ∃ xs' ys' : List ℝ,
        List.Forall₂ (fun x x' => |x' - x| < ρ) xs xs' ∧
        List.Forall₂ (fun y y' => |y' - y| < ρ) ys ys' ∧
        List.Forall₂ (· ≤ ·) xs' ys') :
    List.Forall₂ (· ≤ ·) xs ys := by
  have hlen : xs.length = ys.length := by
    obtain ⟨xs', ys', hxs, hys, hxy⟩ := h 1 zero_lt_one
    exact hxs.length_eq.trans (hxy.length_eq.trans hys.length_eq.symm)
  apply List.forall₂_of_length_eq_of_get hlen
  intro i hix hiy
  apply le_of_forall_pos_exists_close_le
  intro ρ hρ
  obtain ⟨xs', ys', hxs, hys, hxy⟩ := h ρ hρ
  have hix' : i < xs'.length := by
    simpa only [hxs.length_eq] using hix
  have hiy' : i < ys'.length := by
    simpa only [hys.length_eq] using hiy
  exact ⟨xs'.get ⟨i, hix'⟩, ys'.get ⟨i, hiy'⟩,
    hxs.get hix hix', hys.get hiy hiy', hxy.get hix' hiy'⟩

end RealRooted
