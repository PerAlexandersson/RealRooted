import Mathlib.Algebra.Order.BigOperators.Ring.Multiset
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Tactic.Linarith

/-!
# Ordered multiset product inequalities

Additional upstream-shaped inequalities for products of terms in the unit
interval.
-/

namespace Multiset

/-- For a multiset of values in `[0, 1]`, the product of their complements is
at least one minus their sum. -/
theorem one_sub_sum_le_prod_one_sub {R : Type*} [CommRing R] [LinearOrder R]
    [IsStrictOrderedRing R]
    (s : Multiset R) (hnonnegative : ∀ x ∈ s, 0 ≤ x)
    (hle_one : ∀ x ∈ s, x ≤ 1) :
    1 - s.sum ≤ (s.map (fun x => 1 - x)).prod := by
  induction s using Multiset.induction with
  | empty => simp
  | @cons a s ih =>
      have ha0 : 0 ≤ a := hnonnegative a (Multiset.mem_cons_self a s)
      have ha1 : a ≤ 1 := hle_one a (Multiset.mem_cons_self a s)
      have hs0 : ∀ x ∈ s, 0 ≤ x :=
        fun x hx => hnonnegative x (Multiset.mem_cons_of_mem hx)
      have hs1 : ∀ x ∈ s, x ≤ 1 :=
        fun x hx => hle_one x (Multiset.mem_cons_of_mem hx)
      have hsum : 0 ≤ s.sum := Multiset.sum_nonneg hs0
      have hstep := ih hs0 hs1
      rw [Multiset.sum_cons, Multiset.map_cons, Multiset.prod_cons]
      nlinarith

/-- Elementary symmetric functions of a nonnegative real multiset are nonnegative. -/
theorem esymm_nonneg_of_forall_nonneg {s : Multiset ℝ} (hs : ∀ x ∈ s, 0 ≤ x) (n : ℕ) :
    0 ≤ s.esymm n := by
  rw [Multiset.esymm]
  apply Multiset.sum_nonneg
  intro y hy
  rw [Multiset.mem_map] at hy
  obtain ⟨t, ht, rfl⟩ := hy
  rw [Multiset.mem_powersetCard] at ht
  exact Multiset.prod_nonneg (fun x hx => hs x (Multiset.mem_of_le ht.1 hx))

end Multiset
