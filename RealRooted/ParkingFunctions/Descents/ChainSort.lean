import RealRooted.Mathlib.Data.List.OfFn
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Sort

/-!
# Sorting values along disjoint chains

This low combinatorial module sorts the values read along a specified chain of
positions while preserving the word's full value multiset.  It is the
reordering ingredient in the Diaconis--Hicks parking-word argument.
-/

namespace RealRooted.ParkingFunctions

noncomputable section

/-- Sort the values of a word read along a list of positions, leaving every
other position unchanged. -/
def sortAlong {n : ℕ} (l : List (Fin n))
    (f : Fin n → Fin (n + 1)) : Fin n → Fin (n + 1) := fun i =>
  if i ∈ l then ((l.map f).mergeSort (fun a b => a ≤ b)).getD (l.idxOf i) (f i) else f i

/-- Sorting a chain places its values in weakly increasing chain order. -/
theorem map_sortAlong_chain {n : ℕ} (l : List (Fin n)) (hl : l.Nodup)
    (f : Fin n → Fin (n + 1)) :
    l.map (sortAlong l f) = (l.map f).mergeSort (fun a b => a ≤ b) := by
  apply List.ext_getElem
  · simp
  · intro j h₁ h₂
    have hjl : j < l.length := by simpa using h₁
    rw [List.getElem_map]
    simp only [sortAlong, if_pos (List.getElem_mem hjl), hl.idxOf_getElem j hjl]
    rw [List.getD_eq_getElem _ _ h₂]

/-- The values on a sorted chain are weakly increasing. -/
theorem sorted_map_sortAlong {n : ℕ} (l : List (Fin n)) (hl : l.Nodup)
    (f : Fin n → Fin (n + 1)) :
    (l.map (sortAlong l f)).Pairwise (· ≤ ·) := by
  rw [map_sortAlong_chain l hl f]
  have h := List.pairwise_mergeSort (le := fun a b : Fin (n + 1) => decide (a ≤ b))
    (by intro a b c hab hbc; simp only [decide_eq_true_eq] at *; lia)
    (by intro a b; simp only [Bool.or_eq_true, decide_eq_true_eq]; lia) (l.map f)
  simpa using h

/-- Sorting a chain with pairwise distinct values makes it strictly increasing. -/
theorem sortedLT_map_sortAlong_of_nodup {n : ℕ} (l : List (Fin n)) (hl : l.Nodup)
    (f : Fin n → Fin (n + 1)) (hvalues : (l.map f).Nodup) :
    (l.map (sortAlong l f)).SortedLT := by
  rw [map_sortAlong_chain l hl f]
  have hpair : ((l.map f).mergeSort (fun a b => a ≤ b)).Pairwise (· ≤ ·) := by
    simpa only [decide_eq_true_eq] using
      (List.pairwise_mergeSort (le := fun a b : Fin (n + 1) => decide (a ≤ b))
        (by intro a b c hab hbc; simp only [decide_eq_true_eq] at *; lia)
        (by intro a b; simp only [Bool.or_eq_true, decide_eq_true_eq]; lia) (l.map f))
  have hsorted : ((l.map f).mergeSort (fun a b => a ≤ b)).SortedLE := by
    exact hpair.sortedLE
  exact hsorted.sortedLT_of_nodup ((List.mergeSort_perm _ _).nodup_iff.mpr hvalues)

/-- Sorting a chain preserves the full multiset of word values. -/
theorem map_sortAlong_univ {n : ℕ} (l : List (Fin n)) (hl : l.Nodup)
    (f : Fin n → Fin (n + 1)) :
    Multiset.map (sortAlong l f) Finset.univ.val = Multiset.map f Finset.univ.val := by
  classical
  have hsplit : ∀ g : Fin n → Fin (n + 1),
      Multiset.map g (Finset.univ.val : Multiset (Fin n)) =
        Multiset.map g (Multiset.filter (· ∈ l) Finset.univ.val) +
          Multiset.map g (Multiset.filter (fun i => i ∉ l) Finset.univ.val) := by
    intro g
    rw [← Multiset.map_add, Multiset.filter_add_not]
  have hfil : Multiset.filter (· ∈ l) (Finset.univ.val : Multiset (Fin n)) =
      (l : Multiset (Fin n)) := by
    rw [← Finset.filter_val]
    have huniv : Finset.univ.filter (· ∈ l) = l.toFinset := by
      ext i
      simp
    rw [huniv, List.toFinset_val, hl.dedup]
  rw [hsplit (sortAlong l f), hsplit f, hfil]
  congr 1
  · change (↑(l.map (sortAlong l f)) : Multiset (Fin (n + 1))) = ↑(l.map f)
    rw [map_sortAlong_chain l hl f]
    exact Multiset.coe_eq_coe.2 (List.mergeSort_perm _ _)
  · refine Multiset.map_congr rfl fun i hi => ?_
    simp only [Multiset.mem_filter] at hi
    simp [sortAlong, hi.2]

/-- Sort successively along a list of chains. -/
def sortChains {n : ℕ} (L : List (List (Fin n)))
    (f : Fin n → Fin (n + 1)) : Fin n → Fin (n + 1) :=
  L.foldl (fun g l => sortAlong l g) f

/-- Successive chain sorting preserves the full multiset of word values. -/
theorem map_sortChains_univ {n : ℕ} : ∀ (L : List (List (Fin n)))
    (_ : ∀ l ∈ L, l.Nodup) (f : Fin n → Fin (n + 1)),
    Multiset.map (sortChains L f) Finset.univ.val = Multiset.map f Finset.univ.val := by
  intro L
  induction L with
  | nil => intro _ f; rfl
  | cons l L ih =>
    intro hL f
    change Multiset.map (sortChains L (sortAlong l f)) Finset.univ.val = _
    rw [ih (fun l' hl' => hL l' (List.mem_cons_of_mem _ hl')) (sortAlong l f),
      map_sortAlong_univ l (hL l List.mem_cons_self) f]

end

end RealRooted.ParkingFunctions
