/-
Copyright (c) 2026 Bowen Zuo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bowen Zuo
-/
module

public import RealRooted.CombinatorialExamples.LongCycleDescents.Inventory
public import Mathlib.Data.Multiset.Sort
public import Mathlib.Data.List.OfFn
import Mathlib.Tactic

/-! Encoding a sorted inventory by its multiplicity at each rooted cyclic word.

Adapted from Bowen Zuo, cycle-minimum-descent-real-roots v1.0.0 (Apache-2.0)
-/

@[expose] public section

open scoped Classical

noncomputable section
namespace RealRooted.LongCycleDescents.Necklace

section General
variable {n : ℕ} {K : Type*} [LinearOrder K] [Fintype K]

omit [Fintype K] in
/-- The size of an itinerary fiber equals its multiplicity in the associated multiset. -/
theorem frequency_count (w : Fin n → K) (s : K) :
    frequency w s = (List.ofFn w : Multiset K).count s := by
  rw [← Fin.univ_val_map,Multiset.count_map,frequency,Nat.card_eq_fintype_card,Fintype.card_subtype]
  simp [Finset.card,Finset.filter_val,eq_comm]

/-- Expand each multiplicity into that many copies of its index. -/
def expand (m : K → ℕ) : Multiset K := ∑ s, Multiset.replicate (m s) s

/-- Expansion has the prescribed multiplicity at every index. -/
@[simp] theorem expand_count (m : K → ℕ) (s : K) : (expand m).count s = m s := by
  simp [expand,Multiset.count_sum',Multiset.count_replicate]

omit [LinearOrder K] in
/-- The cardinality of an expanded multiset is its total multiplicity. -/
@[simp] theorem expand_card (m : K → ℕ) : (expand m).card = ∑ s, m s := by
  simp [expand,Multiset.card_sum]

/-- Expanding the frequencies of a word recovers its multiset of letters. -/
theorem expand_frequency (w : Fin n → K) : expand (frequency w) = List.ofFn w := by
  ext s
  rw [expand_count,frequency_count]

/-- The sum of all fiber sizes is the length of the word. -/
theorem total_frequency (w : Fin n → K) : ∑ s, frequency w s = n := by
  rw [← expand_card,expand_frequency]
  simp

/-- A weakly increasing finite word is determined by its letter multiplicities. -/
theorem sorted_determined {w v : Fin n → K} (hw : Monotone w) (hv : Monotone v)
    (eq : frequency w = frequency v) : w = v := by
  apply List.ofFn_injective
  apply List.Perm.eq_of_sortedLE (List.sortedLE_ofFn_iff.mpr hw) (List.sortedLE_ofFn_iff.mpr hv)
  apply Multiset.coe_eq_coe.mp
  rw [← expand_frequency w,← expand_frequency v,eq]

/-- Read a multiplicity function as its weakly increasing word of the specified length. -/
def enumerateMass (m : K → ℕ) (h : ∑ s, m s = n) : Fin n → K :=
  let l := (expand m).sort (· ≤ ·)
  fun i ↦ l.get (Fin.cast (by simpa [l] using h.symm) i)

/-- Enumeration reads precisely the sorted expansion of the multiplicities. -/
theorem enumerate_list (m : K → ℕ) (h : ∑ s, m s = n) :
    List.ofFn (enumerateMass m h) = (expand m).sort (· ≤ ·) := by
  let l := (expand m).sort (· ≤ ·)
  have len : l.length = n := by simpa [l] using h
  exact (List.ofFn_congr len l.get).symm.trans (List.ofFn_get l)

/-- Enumeration of multiplicities is weakly increasing. -/
theorem enumerate_monotone (m : K → ℕ) (h : ∑ s, m s = n) : Monotone (enumerateMass m h) := by
  rw [← List.sortedLE_ofFn_iff,enumerate_list]
  exact List.sortedLE_iff_pairwise.mpr (Multiset.pairwise_sort _ _)

/-- Enumeration recovers the specified multiplicity function. -/
theorem enumerate_frequency (m : K → ℕ) (h : ∑ s, m s = n) : frequency (enumerateMass m h) = m := by
  funext s
  rw [frequency_count,enumerate_list,Multiset.sort_eq,expand_count]

end General

variable {n q : ℕ}

/-- An itinerary has positive multiplicity exactly when some position carries it. -/
theorem frequency_pos_iff {K : Type*} [DecidableEq K] (w : Fin n → K) (s : K) :
    0 < frequency w s ↔ ∃ i, w i = s := by
  rw [frequency,Nat.card_eq_fintype_card,Fintype.card_pos_iff]
  exact ⟨fun ⟨i,h⟩ ↦ ⟨i,h⟩, fun ⟨i,h⟩ ↦ ⟨⟨i,h⟩⟩⟩

/-- Multiplicities are constant around an orbit and vanish below the prescribed period. -/
def MassInventory (n q k : ℕ) :=
  {m : Key n q → ℕ // (∑ s, m s) = n ∧ (∀ s, m (turn n q s) = m s) ∧
    ∀ s, 0 < m s → k ≤ Words.period (ofLex s)}

/-- Sorted inventories and invariant multiplicity functions are equivalent. -/
def massEquiv (n q k : ℕ) :
    {w : OrderedInventory n q // ∀ i, k ≤ Words.period (ofLex (w.val i))} ≃
      MassInventory n q k where
  toFun w := ⟨frequency w.val.val,total_frequency (K := Key n q) w.val.val,w.val.property.2,
    fun s hs ↦ by obtain ⟨i,rfl⟩ := (frequency_pos_iff w.val.val s).mp hs; exact w.property i⟩
  invFun m := by
    let w := enumerateMass m.val m.property.1
    have freq : frequency w = m.val := enumerate_frequency _ _
    refine ⟨⟨w,enumerate_monotone _ _,?_⟩,?_⟩
    · rw [freq]
      exact m.property.2.1
    · intro i
      apply m.property.2.2
      exact lt_of_lt_of_eq ((frequency_pos_iff w (w i)).mpr ⟨i,rfl⟩) (congrFun freq (w i))
  left_inv w := by
    apply Subtype.ext
    apply Subtype.ext
    exact sorted_determined (enumerate_monotone (frequency w.val.val) (total_frequency w.val.val))
      w.val.property.1 (enumerate_frequency (frequency w.val.val) (total_frequency w.val.val))
  right_inv m := by
    apply Subtype.ext
    exact enumerate_frequency m.val m.property.1

/-- Allowed compatible pairs correspond to invariant multiplicity functions with the cutoff. -/
def cutoffMassEquiv (n q k : ℕ) :
    {u : Compatible n q // HasLongCycles k u.val.1} ≃ MassInventory n q k :=
  (cutoffInventoryEquiv n q k).trans (massEquiv n q k)

end RealRooted.LongCycleDescents.Necklace

end
