/-
Copyright (c) 2026 Bowen Zuo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bowen Zuo
-/
module

public import RealRooted.CombinatorialExamples.LongCycleDescents.FiberReconstruction
public import RealRooted.CombinatorialExamples.LongCycleDescents.Words
public import Mathlib.Data.Fintype.Perm
import Mathlib.Tactic

/-! Sorted factorial-length cyclic itineraries recover the original permutation and color.

Adapted from Bowen Zuo, cycle-minimum-descent-real-roots v1.0.0 (Apache-2.0)
-/

@[expose] public section

open scoped Classical

noncomputable section
namespace RealRooted.LongCycleDescents.Necklace
open RealRooted.LongCycleDescents.Words
variable {n q : ℕ}

/-- Factorial-length itineraries ordered lexicographically. -/
abbrev Key (n q : ℕ) := Lex (Word n.factorial q)

/-- The first letter of a factorial-length itinerary. -/
def first (s : Key n q) : Fin q := ofLex s ⟨0,Nat.factorial_pos _⟩

/-- Cyclic rotation as a permutation of the itinerary keys. -/
def turn (n q : ℕ) : Equiv.Perm (Key n q) where
  toFun s := toLex (shift 1 (ofLex s))
  invFun s := toLex (shift (n.factorial - 1) (ofLex s))
  left_inv s := by simp [shift_add, Nat.sub_add_cancel (Nat.factorial_pos n)]
  right_inv s := by simp [shift_add, Nat.add_sub_of_le (Nat.factorial_pos n)]

/-- Read successive colors along the orbit of a permutation, for one factorial period. -/
def signature (σ : Equiv.Perm (Fin n)) (x : Fin n → Fin q) (i : Fin n) : Key n q :=
  toLex fun j ↦ x ((σ ^ j.val) i)

/-- The first letter of an orbit itinerary is its starting color. -/
@[simp] theorem first_signature (σ : Equiv.Perm (Fin n)) (x : Fin n → Fin q) (i : Fin n) :
    first (signature σ x i) = x i := by simp [first,signature]

/-- Advancing the permutation rotates its orbit itinerary. -/
theorem signature_step (σ : Equiv.Perm (Fin n)) (x : Fin n → Fin q) (i : Fin n) :
    signature σ x (σ i) = turn n q (signature σ x i) := by
  apply ofLex.injective
  funext j
  change x ((σ ^ j.val) (σ i)) = x ((σ ^ ((j.val + 1) % n.factorial)) i)
  have period := pow_mod_card σ (j.val+1)
  rw [Fintype.card_perm, Fintype.card_fin] at period
  rw [period,pow_succ,Equiv.Perm.mul_apply]

/-- Stable colorings give weakly increasing lexicographic orbit itineraries. -/
theorem signature_monotone {σ : Equiv.Perm (Fin n)} {x : Fin n → Fin q}
    (st : Stable σ x) : Monotone (signature σ x) := by
  apply monotone_iff_forall_lt.mpr
  intro a b ab
  apply le_of_not_gt
  rintro ⟨i,prev,lt⟩
  have same (j : ℕ) (hj : j < i.val) : x ((σ ^ j) b) = x ((σ ^ j) a) :=
    prev ⟨j,hj.trans i.isLt⟩ hj
  exact ab.not_gt ((first_difference_iff st b a i.val same (ne_of_lt lt)).mpr lt)

/-- The first letter is weakly increasing in lexicographic order. -/
theorem head_monotone : Monotone (@first n q) := by
  apply monotone_iff_forall_lt.mpr
  rintro a b ⟨i,prev,lt⟩
  by_cases hi : i.val = 0
  · have eq : i = ⟨0,Nat.factorial_pos n⟩ := Fin.ext hi
    subst i
    exact lt.le
  · exact le_of_eq (prev ⟨0,Nat.factorial_pos n⟩ (Nat.pos_of_ne_zero hi))

/-- Rotation preserves the order of unequal itineraries with the same first letter. -/
theorem turn_lt_of_first_eq {a b : Key n q} (hab : a < b) (eq : first a = first b) :
    turn n q a < turn n q b := by
  obtain ⟨i,prev,lt⟩ := hab
  have pos : 0 < i.val := by
    by_contra! hn
    have hi : i = ⟨0,Nat.factorial_pos n⟩ := Fin.ext (by change i.val = 0; lia)
    subst i
    exact lt.ne eq
  let j : Fin n.factorial := ⟨i.val-1,by have := i.isLt; lia⟩
  have ji : j.val + 1 = i.val := by dsimp [j]; lia
  refine ⟨j,?_,?_⟩
  · intro k hkj
    have hk : k.val + 1 < i.val := by change k.val < j.val at hkj; lia
    have hmod := Nat.mod_eq_of_lt (hk.trans i.isLt)
    change ofLex a ⟨(k.val+1)%n.factorial,_⟩ = ofLex b ⟨(k.val+1)%n.factorial,_⟩
    apply prev
    change (k.val+1)%n.factorial < i.val
    rwa [hmod]
  · change ofLex a ⟨(j.val+1)%n.factorial,_⟩ < ofLex b ⟨(j.val+1)%n.factorial,_⟩
    have hj : (⟨(j.val+1)%n.factorial, Nat.mod_lt _ (Nat.factorial_pos n)⟩ : Fin n.factorial) = i :=
      Fin.ext (by change (j.val+1)%n.factorial = i.val; rw [ji,Nat.mod_eq_of_lt i.isLt])
    rw [hj]
    exact lt

/-- Sorted itineraries with rotation-invariant multiplicities. -/
def OrderedInventory (n q : ℕ) :=
  {w : Fin n → Key n q // Monotone w ∧ ∀ s, frequency w (turn n q s) = frequency w s}

/-- Iterating the successor rotates each itinerary by the same number of steps. -/
theorem shift_iterate (w : Fin n → Key n q) (σ : Equiv.Perm (Fin n))
    (step : ∀ i, w (σ i) = turn n q (w i)) (r : ℕ) (i : Fin n) :
    ofLex (w ((σ ^ r) i)) = shift r (ofLex (w i)) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [pow_succ',Equiv.Perm.mul_apply,step]
    change shift 1 (ofLex (w ((σ ^ r) i))) = shift (r+1) (ofLex (w i))
    rw [ih,shift_add,Nat.add_comm]

/-- Reconstruction recovers the original sorted orbit itineraries. -/
theorem recover_signature (w : Fin n → Key n q) (σ : Equiv.Perm (Fin n))
    (step : ∀ i, w (σ i) = turn n q (w i)) : signature σ (first ∘ w) = w := by
  funext i
  apply ofLex.injective
  funext j
  change ofLex (w ((σ ^ j.val) i)) ⟨0,Nat.factorial_pos n⟩ = ofLex (w i) j
  rw [shift_iterate w σ step]
  exact congrArg (ofLex (w i)) (Fin.ext (by
    change (0+j.val)%n.factorial = j.val
    simp [Nat.mod_eq_of_lt j.isLt]))

/-- Recover a compatible permutation and coloring from a sorted itinerary inventory. -/
def recoverPair (w : OrderedInventory n q) : Compatible n q := by
  let h := w.val
  let σ := reconstruct h (turn n q) w.property.2
  refine ⟨(σ,first ∘ h),?_⟩
  intro a b ab
  obtain ⟨hm,inv⟩ := w.property
  have hab : h a ≤ h b := hm ab.le
  refine Prod.Lex.toLex_lt_toLex'.mpr ⟨head_monotone hab,?_⟩
  intro eq
  obtain lt | same := hab.lt_or_eq
  · have turned := turn_lt_of_first_eq lt eq
    have hsa : h (σ a) < h (σ b) := calc
      _ = turn n q (h a) := reconstruct_shift h (turn n q) w.property.2 a
      _ < turn n q (h b) := turned
      _ = _ := (reconstruct_shift h (turn n q) w.property.2 b).symm
    exact lt_of_not_ge (fun le ↦ hsa.not_ge (hm le))
  · exact reconstruct_tie h (turn n q) inv ab same

/-- Compatible permutation-coloring pairs and sorted itinerary inventories are equivalent. -/
def inventoryEquiv (n q : ℕ) : Compatible n q ≃ OrderedInventory n q where
  toFun u := ⟨signature u.val.1 u.val.2,signature_monotone u.property,
    shift_frequency _ _ _ (signature_step u.val.1 u.val.2)⟩
  invFun := recoverPair
  left_inv u := by
    obtain ⟨⟨σ,x⟩,st⟩ := u
    apply Subtype.ext
    apply Prod.ext
    · apply Eq.symm
      apply reconstruct_unique (signature σ x) (turn n q) σ (signature_step σ x)
      intro a b ab same
      have eq := congrArg first same
      exact (Prod.Lex.toLex_lt_toLex'.mp (st ab)).2 (by simpa using eq)
    · funext i
      exact first_signature σ x i
  right_inv w := Subtype.ext (recover_signature w.val _ (reconstruct_shift _ _ _))

/-- Returning to a rooted word is precisely returning to the original permutation position. -/
theorem period_dvd_iff_return {σ : Equiv.Perm (Fin n)} {x : Fin n → Fin q}
    (st : Stable σ x) (i : Fin n) (r : ℕ) :
    period (ofLex (signature σ x i)) ∣ r ↔ (σ ^ r) i = i := by
  rw [period_dvd_iff,← shift_iterate _ _ (signature_step σ x)]
  constructor
  · intro eq
    apply RealRooted.LongCycleDescents.primitive_itinerary σ x
      (fun a b hab h ↦ (Prod.Lex.toLex_lt_toLex'.mp (st hab)).2 h) i r
    intro j
    have h := congrFun eq ⟨j % n.factorial,Nat.mod_lt _ (Nat.factorial_pos n)⟩
    have p := pow_mod_card σ j
    rw [Fintype.card_perm,Fintype.card_fin] at p
    change x ((σ ^ (j % n.factorial)) ((σ ^ r) i)) = x ((σ ^ (j % n.factorial)) i) at h
    simpa only [p] using h.symm
  · intro ret
    rw [ret]

/-- The original cycle cutoff is equivalent to the lower bound on all itinerary periods. -/
theorem allowed_iff_word_period {σ : Equiv.Perm (Fin n)} {x : Fin n → Fin q}
    (st : Stable σ x) (k : ℕ) :
    HasLongCycles k σ ↔ ∀ i, k ≤ period (ofLex (signature σ x i)) := by
  constructor
  · intro allowed i
    apply le_of_not_gt
    intro lt
    exact allowed i _ (period_pos (Nat.factorial_pos n) _) lt
      ((period_dvd_iff_return st i _).mp (dvd_refl _))
  · intro lower i j pos lt ret
    exact (Nat.le_of_dvd pos ((period_dvd_iff_return st i j).mpr ret)).not_gt (lt.trans_le
      (lower i))

/-- The compatible-pair correspondence preserves the prescribed cycle cutoff. -/
def cutoffInventoryEquiv (n q k : ℕ) :
    {u : Compatible n q // HasLongCycles k u.val.1} ≃
      {w : OrderedInventory n q // ∀ i, k ≤ period (ofLex (w.val i))} :=
  (inventoryEquiv n q).subtypeEquiv (fun u ↦ allowed_iff_word_period u.property k)

end RealRooted.LongCycleDescents.Necklace

end
