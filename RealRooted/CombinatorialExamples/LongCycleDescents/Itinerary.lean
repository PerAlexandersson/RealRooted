/-
Copyright (c) 2026 Bowen Zuo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bowen Zuo
-/
module

public import RealRooted.CombinatorialExamples.LongCycleDescents.Basic
public import Mathlib.Order.Prod.Lex.Basic
public import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic

/-! A weakly increasing coloring, strict at ordinary descents, gives primitive cycle words.

Adapted from Bowen Zuo, cycle-minimum-descent-real-roots v1.0.0 (Apache-2.0)
-/

public section

namespace RealRooted.LongCycleDescents

/-- The original adjacent descent constraints force the successor permutation to preserve
the strict order of any pair in a common color fiber. -/
theorem order_of_equal_color {n q : ℕ} (σ : Equiv.Perm (Fin (n + 1)))
    (c : Fin (n + 1) → Fin q) (mono : Monotone c)
    (rise : ∀ i : Fin n, σ i.succ < σ i.castSucc → c i.castSucc < c i.succ)
    {a b : Fin (n + 1)} (ab : a < b) (eqc : c a = c b) : σ a < σ b := by
  have order : StrictMono (fun i ↦ toLex (c i, σ i)) := by
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    apply Prod.Lex.toLex_lt_toLex'.mpr
    refine ⟨mono (show i.castSucc < i.succ from Fin.castSucc_lt_succ).le, ?_⟩
    intro same
    apply lt_of_le_of_ne
    · exact le_of_not_gt fun h ↦ (ne_of_lt (rise i h)) same
    · exact σ.injective.ne (show i.castSucc < i.succ from Fin.castSucc_lt_succ).ne
  exact (Prod.Lex.toLex_lt_toLex'.mp (order ab)).2 eqc

/-- Two rotations of a single orbit with identical infinite itineraries start at the same
point. This is the primitive-necklace step of the Gessel--Reutenauer correspondence. -/
theorem primitive_itinerary {α β : Type*} [Finite α] [LinearOrder α]
    (σ : Equiv.Perm α) (c : α → β)
    (tie : ∀ a b, a < b → c a = c b → σ a < σ b)
    (a : α) (d : ℕ)
    (same : ∀ j : ℕ, c ((σ ^ j) a) = c ((σ ^ j) ((σ ^ d) a))) :
    (σ ^ d) a = a := by
  let := Fintype.ofFinite α
  have propagate {x y : α} (xy : x < y)
      (colors : ∀ j : ℕ, c ((σ ^ j) x) = c ((σ ^ j) y)) (j : ℕ) :
      (σ ^ j) x < (σ ^ j) y := by
    induction j with
    | zero => simpa using xy
    | succ j ih => simpa [pow_succ', Equiv.Perm.mul_apply] using tie _ _ ih (colors j)
  let τ := σ ^ d
  have rule {x y : α} (j : ℕ) (h : (σ ^ (d * j)) x < (σ ^ (d * j)) y) :
      (τ ^ j) x < (τ ^ j) y := by simpa [τ, pow_mul] using h
  by_contra h
  rcases lt_or_gt_of_ne h with down | up
  · have dec : StrictAnti (fun j : ℕ ↦ (τ ^ j) a) := by
      apply strictAnti_nat_of_succ_lt
      intro j
      have r := rule j (propagate down (fun i ↦ (same i).symm) (d * j))
      simpa [pow_succ, Equiv.Perm.mul_apply, τ] using r
    exact (lt_irrefl a) (by simpa [pow_orderOf_eq_one] using dec (orderOf_pos τ))
  · have inc : StrictMono (fun j : ℕ ↦ (τ ^ j) a) := by
      apply strictMono_nat_of_lt_succ
      intro j
      have r := rule j (propagate up same (d * j))
      simpa [pow_succ, Equiv.Perm.mul_apply, τ] using r
    exact (lt_irrefl a) (by simpa [pow_orderOf_eq_one] using inc (orderOf_pos τ))

end RealRooted.LongCycleDescents
