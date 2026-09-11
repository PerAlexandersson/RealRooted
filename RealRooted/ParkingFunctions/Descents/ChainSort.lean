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

/-- Sorting a chain does not change positions outside that chain. -/
@[simp]
theorem sortAlong_apply_of_not_mem {n : ℕ} (l : List (Fin n))
    (f : Fin n → Fin (n + 1)) {i : Fin n} (hi : i ∉ l) :
    sortAlong l f i = f i := by
  simp [sortAlong, hi]

/-- Sorting one chain leaves the value list on a disjoint chain unchanged. -/
theorem map_sortAlong_eq_of_forall_not_mem {n : ℕ} (l l' : List (Fin n))
    (f : Fin n → Fin (n + 1)) (hdisj : ∀ i ∈ l', i ∉ l) :
    l'.map (sortAlong l f) = l'.map f := by
  apply List.map_congr_left
  intro i hi
  exact sortAlong_apply_of_not_mem l f (hdisj i hi)

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

/-- Sorting an already weakly increasing chain leaves the word unchanged. -/
theorem sortAlong_eq_self_of_pairwise {n : ℕ} (l : List (Fin n))
    (f : Fin n → Fin (n + 1)) (hmono : (l.map f).Pairwise (· ≤ ·)) :
    sortAlong l f = f := by
  funext i
  by_cases hi : i ∈ l
  · simp only [sortAlong, if_pos hi]
    rw [List.mergeSort_eq_self (r := (· ≤ ·)) hmono]
    rw [List.getD_eq_getElem]
    · rw [List.getElem_map]
      rw [List.getElem_idxOf (l.idxOf_lt_length_of_mem hi)]
    · simpa using l.idxOf_lt_length_of_mem hi
  · simp [sortAlong, hi]

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

/-- A word is chain-sorted when its values are weakly increasing along every
listed chain. -/
def IsChainSorted {n : ℕ} (L : List (List (Fin n)))
    (f : Fin n → Fin (n + 1)) : Prop :=
  ∀ l ∈ L, (l.map f).Pairwise (· ≤ ·)

/-- Sorting chains disjoint from a fixed chain leaves its value list unchanged. -/
theorem map_sortChains_eq_of_forall_not_mem {n : ℕ} : ∀ (L : List (List (Fin n)))
    (l : List (Fin n))
    (f : Fin n → Fin (n + 1)),
    (∀ l' ∈ L, ∀ i ∈ l, i ∉ l') → l.map (sortChains L f) = l.map f := by
  intro L
  induction L with
  | nil => intro l f _; rfl
  | cons l' L ih =>
    intro l f hdisj
    change l.map (sortChains L (sortAlong l' f)) = l.map f
    rw [ih l (sortAlong l' f) (fun l'' hl'' =>
      hdisj l'' (List.mem_cons_of_mem _ hl''))]
    exact map_sortAlong_eq_of_forall_not_mem l' l f
      (fun i hi => hdisj l' List.mem_cons_self i hi)

/-- Sorting a nodup pairwise-disjoint family preserves the value permutation
on every individual chain. -/
theorem perm_map_sortChains_of_disjoint {n : ℕ} : ∀ (L : List (List (Fin n))),
    L.Nodup →
    (∀ l ∈ L, l.Nodup) →
    (∀ l₁ ∈ L, ∀ l₂ ∈ L, l₁ ≠ l₂ → ∀ i ∈ l₁, i ∉ l₂) →
    ∀ f : Fin n → Fin (n + 1),
      ∀ l ∈ L, List.Perm (l.map (sortChains L f)) (l.map f) := by
  intro L
  induction L with
  | nil =>
    intro _ _ _ f l hl
    simp at hl
  | cons head L ih =>
    intro hLnodup hnodup hdisj f l' hl'
    obtain ⟨hnotmem, hLnodup⟩ := List.nodup_cons.mp hLnodup
    change List.Perm (l'.map (sortChains L (sortAlong head f))) (l'.map f)
    by_cases hEq : l' = head
    · subst l'
      rw [map_sortChains_eq_of_forall_not_mem L head (sortAlong head f) (fun l'' hl'' i hi =>
        hdisj head List.mem_cons_self l'' (List.mem_cons_of_mem _ hl'')
          (fun hEq => hnotmem (hEq ▸ hl'')) i hi)]
      rw [map_sortAlong_chain head (hnodup head List.mem_cons_self) f]
      exact List.mergeSort_perm _ _
    · have h := ih
        hLnodup
        (fun l'' hl'' => hnodup l'' (List.mem_cons_of_mem _ hl''))
        (fun l₁ hl₁ l₂ hl₂ hne' =>
          hdisj l₁ (List.mem_cons_of_mem _ hl₁) l₂ (List.mem_cons_of_mem _ hl₂) hne')
        (sortAlong head f)
        l' ((List.mem_cons.mp hl').resolve_left hEq)
      rw [map_sortAlong_eq_of_forall_not_mem head l' f (fun i hi =>
        hdisj l' (List.mem_cons_of_mem _ ((List.mem_cons.mp hl').resolve_left hEq))
          head List.mem_cons_self (fun hchain => hnotmem (hchain ▸
            ((List.mem_cons.mp hl').resolve_left hEq))) i hi)] at h
      exact h

/-- Sorting a nodup pairwise-disjoint family makes every chain weakly
increasing. -/
theorem sorted_map_sortChains_of_disjoint {n : ℕ} : ∀ (L : List (List (Fin n))),
    L.Nodup →
    (∀ l ∈ L, l.Nodup) →
    (∀ l₁ ∈ L, ∀ l₂ ∈ L, l₁ ≠ l₂ → ∀ i ∈ l₁, i ∉ l₂) →
    ∀ f : Fin n → Fin (n + 1),
      ∀ l ∈ L, (l.map (sortChains L f)).Pairwise (· ≤ ·) := by
  intro L
  induction L with
  | nil =>
    intro _ _ _ f l hl
    simp at hl
  | cons head L ih =>
    intro hLnodup hnodup hdisj f l' hl'
    obtain ⟨hnotmem, hLnodup⟩ := List.nodup_cons.mp hLnodup
    change (l'.map (sortChains L (sortAlong head f))).Pairwise (· ≤ ·)
    by_cases hEq : l' = head
    · subst l'
      rw [map_sortChains_eq_of_forall_not_mem L head (sortAlong head f) (fun l'' hl'' i hi =>
        hdisj head List.mem_cons_self l'' (List.mem_cons_of_mem _ hl'')
          (fun hEq => hnotmem (hEq ▸ hl'')) i hi)]
      exact sorted_map_sortAlong head (hnodup head List.mem_cons_self) f
    · exact ih
        hLnodup
        (fun l'' hl'' => hnodup l'' (List.mem_cons_of_mem _ hl''))
        (fun l₁ hl₁ l₂ hl₂ hne' =>
          hdisj l₁ (List.mem_cons_of_mem _ hl₁) l₂ (List.mem_cons_of_mem _ hl₂) hne')
        (sortAlong head f)
        l' ((List.mem_cons.mp hl').resolve_left hEq)

/-- Sorting a nodup pairwise-disjoint family yields a chain-sorted word. -/
theorem isChainSorted_sortChains_of_disjoint {n : ℕ} (L : List (List (Fin n)))
    (hLnodup : L.Nodup) (hnodup : ∀ l ∈ L, l.Nodup)
    (hdisj : ∀ l₁ ∈ L, ∀ l₂ ∈ L, l₁ ≠ l₂ → ∀ i ∈ l₁, i ∉ l₂)
    (f : Fin n → Fin (n + 1)) :
    IsChainSorted L (sortChains L f) :=
  sorted_map_sortChains_of_disjoint L hLnodup hnodup hdisj f

/-- Sorting a pairwise-disjoint family of chains with distinct chain values
makes every chain strictly increasing. -/
theorem sortedLT_map_sortChains_of_disjoint {n : ℕ} : ∀ (L : List (List (Fin n))),
    L.Nodup →
    (∀ l ∈ L, l.Nodup) →
    (∀ l₁ ∈ L, ∀ l₂ ∈ L, l₁ ≠ l₂ → ∀ i ∈ l₁, i ∉ l₂) →
    ∀ f : Fin n → Fin (n + 1),
      (∀ l ∈ L, (l.map f).Nodup) →
      ∀ l ∈ L, (l.map (sortChains L f)).SortedLT := by
  intro L
  induction L with
  | nil =>
    intro _ _ _ f _ l hl
    simp at hl
  | cons head L ih =>
    intro hLnodup hnodup hdisj f hvalues l' hl'
    obtain ⟨hnotmem, hLnodup⟩ := List.nodup_cons.mp hLnodup
    change (l'.map (sortChains L (sortAlong head f))).SortedLT
    by_cases hEq : l' = head
    · subst l'
      rw [map_sortChains_eq_of_forall_not_mem L head (sortAlong head f) (fun l'' hl'' i hi =>
        hdisj head List.mem_cons_self l'' (List.mem_cons_of_mem _ hl'')
          (fun hEq => hnotmem (hEq ▸ hl'')) i hi)]
      exact sortedLT_map_sortAlong_of_nodup head (hnodup head List.mem_cons_self) f
        (hvalues head List.mem_cons_self)
    · exact ih
        hLnodup
        (fun l'' hl'' => hnodup l'' (List.mem_cons_of_mem _ hl''))
        (fun l₁ hl₁ l₂ hl₂ hne' =>
          hdisj l₁ (List.mem_cons_of_mem _ hl₁) l₂ (List.mem_cons_of_mem _ hl₂) hne')
        (sortAlong head f)
        (fun l'' hl'' => by
          rw [map_sortAlong_eq_of_forall_not_mem head l'' f (fun i hi =>
            hdisj l'' (List.mem_cons_of_mem _ hl'') head List.mem_cons_self
              (fun hEq => hnotmem (hEq ▸ hl'')) i hi)]
          exact hvalues l'' (List.mem_cons_of_mem _ hl''))
        l' ((List.mem_cons.mp hl').resolve_left hEq)

/-- Sorting a list of chains already weakly increasing on each chain is the
identity. -/
theorem sortChains_eq_self_of_pairwise {n : ℕ} : ∀ (L : List (List (Fin n)))
    (f : Fin n → Fin (n + 1)),
    (∀ l ∈ L, (l.map f).Pairwise (· ≤ ·)) → sortChains L f = f := by
  intro L
  induction L with
  | nil => intro f _; rfl
  | cons l L ih =>
    intro f hL
    change sortChains L (sortAlong l f) = f
    rw [sortAlong_eq_self_of_pairwise l f (hL l List.mem_cons_self)]
    exact ih f (fun l' hl' => hL l' (List.mem_cons_of_mem _ hl'))

/-- Sorting fixes an already chain-sorted word. -/
theorem sortChains_eq_self_of_isChainSorted {n : ℕ} (L : List (List (Fin n)))
    (f : Fin n → Fin (n + 1)) (h : IsChainSorted L f) :
    sortChains L f = f :=
  sortChains_eq_self_of_pairwise L f h

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
