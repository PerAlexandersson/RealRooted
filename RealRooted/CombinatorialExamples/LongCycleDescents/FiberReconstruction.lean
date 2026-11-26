/-
Copyright (c) 2026 Bowen Zuo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bowen Zuo
-/
module

public import RealRooted.CombinatorialExamples.LongCycleDescents.Standardization
public import Mathlib.Order.PiLex
public import Mathlib.Logic.Equiv.Sum
public import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Tactic

/-! Reconstruction of a permutation from the ordered multiplicities of its cyclic itineraries.

Adapted from Bowen Zuo, cycle-minimum-descent-real-roots v1.0.0 (Apache-2.0)
-/

@[expose] public section

noncomputable section
namespace RealRooted.LongCycleDescents.Necklace

variable {n : ℕ} {K : Type*} [DecidableEq K]

/-- The positions carrying one specified itinerary. -/
abbrev Fiber (w : Fin n → K) (s : K) := {i : Fin n // w i = s}

/-- The cardinality of one itinerary fiber. -/
def frequency (w : Fin n → K) (s : K) : ℕ := Nat.card (Fiber w s)

/-- The order on positions distinguishes all the copies of a repeated itinerary. -/
def matchFiber (w : Fin n → K) (T : Equiv.Perm K)
    (invariant : ∀ s, frequency w (T s) = frequency w s) (s : K) :
    Fiber w s ≃o Fiber w (T s) :=
  (Fintype.orderIsoFinOfCardEq (Fiber w s) rfl).symm.trans
    (Fintype.orderIsoFinOfCardEq (Fiber w (T s)) (by
      simpa only [frequency, Nat.card_eq_fintype_card] using invariant s))

/-- Recover the successor permutation by matching ordered fibers along a rotation. -/
def reconstruct (w : Fin n → K) (T : Equiv.Perm K)
    (invariant : ∀ s, frequency w (T s) = frequency w s) : Equiv.Perm (Fin n) :=
  (Equiv.sigmaFiberEquiv w).symm.trans
    ((Equiv.sigmaCongr T fun s ↦ (matchFiber w T invariant s).toEquiv).trans
      (Equiv.sigmaFiberEquiv w))

/-- Reconstruction acts by the increasing equivalence on each fiber. -/
theorem reconstruct_apply (w : Fin n → K) (T : Equiv.Perm K)
    (inv : ∀ s, frequency w (T s) = frequency w s) (i : Fin n) {s : K} (hi : w i = s) :
    reconstruct w T inv i = (matchFiber w T inv s ⟨i,hi⟩).val := by
  subst s
  rfl

/-- The reconstructed successor rotates the itinerary of each position. -/
theorem reconstruct_shift (w : Fin n → K) (T : Equiv.Perm K)
    (inv : ∀ s, frequency w (T s) = frequency w s) (i : Fin n) :
    w (reconstruct w T inv i) = T (w i) :=
  (matchFiber w T inv (w i) ⟨i,rfl⟩).property

/-- Reconstruction preserves the order of positions carrying the same itinerary. -/
theorem reconstruct_tie (w : Fin n → K) (T : Equiv.Perm K)
    (inv : ∀ s, frequency w (T s) = frequency w s) {i j : Fin n}
    (lt : i < j) (eq : w i = w j) : reconstruct w T inv i < reconstruct w T inv j := by
  rw [reconstruct_apply w T inv i eq, reconstruct_apply w T inv j rfl]
  exact (matchFiber w T inv (w j)).strictMono (show (⟨i,eq⟩ : Fiber w (w j)) < ⟨j,rfl⟩ from lt)

/-- A successor permutation transports one itinerary fiber to the next. -/
def transportFiber (w : Fin n → K) (T : Equiv.Perm K) (σ : Equiv.Perm (Fin n))
    (h : ∀ i, w (σ i) = T (w i)) (s : K) : Fiber w s ≃ Fiber w (T s) where
  toFun i := ⟨σ i.val, (h i.val).trans (congrArg T i.property)⟩
  invFun j := ⟨σ.symm j.val, T.injective (by rw [← h, σ.apply_symm_apply, j.property])⟩
  left_inv i := Subtype.ext (σ.symm_apply_apply _)
  right_inv i := Subtype.ext (σ.apply_symm_apply _)

omit [DecidableEq K] in
/-- A successor permutation makes the fiber cardinalities rotation invariant. -/
theorem shift_frequency (w : Fin n → K) (T : Equiv.Perm K) (σ : Equiv.Perm (Fin n))
    (h : ∀ i, w (σ i) = T (w i)) (s : K) : frequency w (T s) = frequency w s :=
  Nat.card_congr (transportFiber w T σ h s).symm

/-- Any permutation respecting a shift and the order of copies agrees at every position
with the order-preserving matching of the two fibers. -/
theorem reconstruct_unique (w : Fin n → K) (T : Equiv.Perm K) (σ : Equiv.Perm (Fin n))
    (h : ∀ i, w (σ i) = T (w i))
    (tie : ∀ i j, i < j → w i = w j → σ i < σ j) :
    σ = reconstruct w T (shift_frequency w T σ h) := by
  apply Equiv.ext
  intro i
  let e := transportFiber w T σ h (w i)
  have he : StrictMono e := fun a b hab ↦ tie a b hab (a.property.trans b.property.symm)
  let o := he.orderIsoOfRightInverse e e.symm e.apply_symm_apply
  have ho : o = matchFiber w T (shift_frequency w T σ h) (w i) := Subsingleton.elim _ _
  exact congrArg (fun f : Fiber w (w i) ≃o Fiber w (T (w i)) ↦ (f ⟨i,rfl⟩).val) ho

end RealRooted.LongCycleDescents.Necklace

end
