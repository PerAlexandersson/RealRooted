/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
import Mathlib.Algebra.Order.BigOperators.Ring.Multiset
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Ordered multiset product inequalities

Additional upstream-shaped inequalities for products of terms in the unit
interval.
-/

namespace Multiset

/-- The sign of a product records the parity of factors larger than a cut. -/
theorem prod_sub_sign
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {m : Multiset K} {x : K} (h : ∀ ξ ∈ m, ξ ≠ x) :
    0 < (-1 : K) ^ (m.filter (fun ξ => x < ξ)).card *
      (m.map (fun ξ => x - ξ)).prod := by
  classical
  induction m using Multiset.induction with
  | empty => simp
  | cons a t ih =>
      have hta : ∀ ξ ∈ t, ξ ≠ x := fun ξ hξ => h ξ (Multiset.mem_cons_of_mem hξ)
      have hane : a ≠ x := h a (Multiset.mem_cons_self a t)
      have hIH := ih hta
      rw [Multiset.map_cons, Multiset.prod_cons, Multiset.filter_cons]
      rcases lt_or_gt_of_ne hane with hlt | hgt
      · have hnot : ¬ x < a := by linarith
        rw [ite_eq_right hnot]
        simp only [zero_add]
        have hfac : (0 : K) < x - a := by linarith
        nlinarith [hIH, hfac]
      · rw [ite_eq_left hgt]
        rw [Multiset.card_add, Multiset.card_singleton]
        have hfac : x - a < 0 := by linarith
        have hpow : (-1 : K) ^ (1 + (t.filter (fun ξ => x < ξ)).card) =
            -((-1 : K) ^ (t.filter (fun ξ => x < ξ)).card) := by
          rw [pow_add, pow_one]
          ring
        rw [hpow]
        nlinarith [hIH, hfac]

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
  unfold Multiset.esymm
  apply Multiset.sum_nonneg
  intro y hy
  rw [Multiset.mem_map] at hy
  obtain ⟨t, ht, rfl⟩ := hy
  rw [Multiset.mem_powersetCard] at ht
  exact Multiset.prod_nonneg (fun x hx => hs x (Multiset.mem_of_le ht.1 hx))

end Multiset
