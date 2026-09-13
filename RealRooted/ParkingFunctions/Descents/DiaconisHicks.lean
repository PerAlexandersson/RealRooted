import RealRooted.ParkingFunctions.Descents.Pollak
import RealRooted.ParkingFunctions.Descents.ChainSort
import RealRooted.Mathlib.Data.List.OfFn
import RealRooted.Mathlib.Data.Fintype.Card
import Mathlib.Data.List.Sort

/-!
# Diaconis--Hicks chain sorting for parking-function descents

This module combines Pollak's cyclic alphabet action with sorting along
families of chains.  The reusable parking-word predicate, unique cyclic
representative, and ordinary parking-function embedding live in the neutral
`Pollak` module.
-/

namespace RealRooted.ParkingFunctions

noncomputable section

/-- Sort the values of a word along its `Fin n` chain of positions. -/
def chainSortedWord {n m : ℕ} (w : Fin n → Fin m) : Fin n → Fin m :=
  fun i => (List.insertionSort (· ≤ ·) (List.ofFn w)).get ⟨i, by simp⟩

/-- Sorting a word along one chain makes it monotone. -/
theorem chainSortedWord_monotone {n m : ℕ} (w : Fin n → Fin m) :
    Monotone (chainSortedWord w) := by
  intro i j hij
  exact (List.pairwise_insertionSort (r := (· ≤ ·)) (List.ofFn w)).sortedLE.monotone_get hij

/-- Sorting a word along one chain preserves its value multiset. -/
theorem chainSortedWord_perm {n m : ℕ} (w : Fin n → Fin m) :
    List.Perm (List.ofFn (chainSortedWord w)) (List.ofFn w) := by
  rw [show List.ofFn (chainSortedWord w) =
      List.insertionSort (· ≤ ·) (List.ofFn w) by
    apply List.ext_get
    · simp
    · intro i hi₁ hi₂
      simp [chainSortedWord]]
  exact List.perm_insertionSort _ _

/-- A permutation of a word's values preserves every lower-alphabet count. -/
theorem card_lt_eq_of_ofFn_perm {n m : ℕ} {w v : Fin n → Fin m}
    (h : List.Perm (List.ofFn w) (List.ofFn v)) (k : ℕ) :
    (Finset.univ.filter fun i => (w i).val < k).card =
      (Finset.univ.filter fun i => (v i).val < k).card := by
  rw [show (Finset.univ.filter fun i => (w i).val < k).card =
        List.countP (fun x => decide (x.val < k)) (List.ofFn w) by
      simpa using List.card_filter_univ_eq_countP_ofFn w (fun x => decide (x.val < k))]
  rw [h.countP_eq]
  simpa using (List.card_filter_univ_eq_countP_ofFn v (fun x => decide (x.val < k))).symm

/-- The parking-function condition depends only on the word's value multiset. -/
theorem isParkingFunction_iff_of_ofFn_perm {n : ℕ} {w v : Fin n → Fin n}
    (h : List.Perm (List.ofFn w) (List.ofFn v)) :
    IsParkingFunction w ↔ IsParkingFunction v := by
  constructor <;> intro hw k hk
  · rw [← card_lt_eq_of_ofFn_perm h k]
    exact hw k hk
  · rw [card_lt_eq_of_ofFn_perm h k]
    exact hw k hk

/-- The extra-alphabet parking condition also depends only on the value multiset. -/
theorem isParkingWord_iff_of_ofFn_perm {n : ℕ} {w v : Fin n → Fin (n + 1)}
    (h : List.Perm (List.ofFn w) (List.ofFn v)) :
    IsParkingWord w ↔ IsParkingWord v := by
  constructor <;> intro hw k hk
  · rw [← card_lt_eq_of_ofFn_perm h k]
    exact hw k hk
  · rw [card_lt_eq_of_ofFn_perm h k]
    exact hw k hk

/-- Sorting along any list of duplicate-free chains preserves the extra-alphabet
parking condition. -/
theorem isParkingWord_sortChains_iff {n : ℕ} (L : List (List (Fin n)))
    (hL : ∀ l ∈ L, l.Nodup) (w : Fin n → Fin (n + 1)) :
    IsParkingWord (sortChains L w) ↔ IsParkingWord w :=
  isParkingWord_iff_of_multiset_eq (map_sortChains_univ L hL w)

/-- The Diaconis--Hicks value action followed by sorting along a chain family. -/
def cyclicSortChains {n : ℕ} (L : List (List (Fin n))) (c : Fin (n + 1))
    (w : Fin n → Fin (n + 1)) : Fin n → Fin (n + 1) :=
  sortChains L (cyclicValueShift c w)

/-- Chain sorting does not affect whether a cyclic value shift is a parking word. -/
theorem isParkingWord_cyclicSortChains_iff {n : ℕ} (L : List (List (Fin n)))
    (hL : ∀ l ∈ L, l.Nodup) (c : Fin (n + 1))
    (w : Fin n → Fin (n + 1)) :
    IsParkingWord (cyclicSortChains L c w) ↔ IsParkingWord (cyclicValueShift c w) := by
  exact isParkingWord_sortChains_iff L hL _

/-- Every cyclic-shift-and-sort orbit has a unique parking-word representative. -/
theorem existsUnique_isParkingWord_cyclicSortChains {n : ℕ} (L : List (List (Fin n)))
    (hL : ∀ l ∈ L, l.Nodup) (w : Fin n → Fin (n + 1)) :
    ∃! c : Fin (n + 1), IsParkingWord (cyclicSortChains L c w) := by
  obtain ⟨c, hc, hunique⟩ := existsUnique_isParkingWord_cyclicValueShift w
  refine ⟨c, (isParkingWord_cyclicSortChains_iff L hL c w).mpr hc, ?_⟩
  intro c' hc'
  exact hunique c' ((isParkingWord_cyclicSortChains_iff L hL c' w).mp hc')

/-- The shift-and-sort action lands in the weakly chain-sorted normal form. -/
theorem isChainSorted_cyclicSortChains_of_disjoint {n : ℕ}
    (L : List (List (Fin n))) (hLnodup : L.Nodup)
    (hnodup : ∀ l ∈ L, l.Nodup)
    (hdisj : ∀ l₁ ∈ L, ∀ l₂ ∈ L, l₁ ≠ l₂ → ∀ i ∈ l₁, i ∉ l₂)
    (c : Fin (n + 1)) (w : Fin n → Fin (n + 1)) :
    IsChainSorted L (cyclicSortChains L c w) :=
  isChainSorted_sortChains_of_disjoint L hLnodup hnodup hdisj _

/-- On a covering disjoint chain family, unshifting and re-sorting a cyclic
sort recovers every already chain-sorted word. -/
theorem sortChains_unshift_cyclicSortChains {n : ℕ} (L : List (List (Fin n)))
    (hcover : ChainsCover L) (hLnodup : L.Nodup)
    (hnodup : ∀ l ∈ L, l.Nodup)
    (hdisj : ∀ l₁ ∈ L, ∀ l₂ ∈ L, l₁ ≠ l₂ → ∀ i ∈ l₁, i ∉ l₂)
    (c : Fin (n + 1)) (w : Fin n → Fin (n + 1))
    (hw : IsChainSorted L w) :
    sortChains L (cyclicValueUnshift c (cyclicSortChains L c w)) = w := by
  apply eq_of_isChainSorted_of_forall_perm L hcover
  · exact isChainSorted_sortChains_of_disjoint L hLnodup hnodup hdisj _
  · exact hw
  · intro l hl
    have hsorted := perm_map_sortChains_of_disjoint L hLnodup hnodup hdisj
      (cyclicValueShift c w) l hl
    have hunshift : List.Perm
        (l.map (cyclicValueUnshift c (cyclicSortChains L c w))) (l.map w) := by
      change List.Perm
        (l.map ((finCycle c).symm ∘ sortChains L (cyclicValueShift c w))) (l.map w)
      have hundo : (finCycle c).symm ∘ cyclicValueShift c w = w := by
        exact cyclicValueUnshift_cyclicValueShift c w
      simpa only [List.map_map, hundo] using hsorted.map (finCycle c).symm
    exact (perm_map_sortChains_of_disjoint L hLnodup hnodup hdisj
      (cyclicValueUnshift c (cyclicSortChains L c w)) l hl).trans hunshift

/-- For a fixed cyclic shift, sorting is injective on chain-sorted words. -/
theorem cyclicSortChains_injective_of_chainSorted {n : ℕ}
    (L : List (List (Fin n))) (hcover : ChainsCover L) (hLnodup : L.Nodup)
    (hnodup : ∀ l ∈ L, l.Nodup)
    (hdisj : ∀ l₁ ∈ L, ∀ l₂ ∈ L, l₁ ≠ l₂ → ∀ i ∈ l₁, i ∉ l₂)
    (c : Fin (n + 1)) :
    Function.Injective (fun w : {w : Fin n → Fin (n + 1) // IsChainSorted L w} =>
      cyclicSortChains L c w) := by
  intro w v h
  apply Subtype.ext
  have hunshift := congrArg (fun u => sortChains L (cyclicValueUnshift c u)) h
  calc
    w.val = sortChains L (cyclicValueUnshift c (cyclicSortChains L c w.val)) :=
      (sortChains_unshift_cyclicSortChains L hcover hLnodup hnodup hdisj c w.val w.prop).symm
    _ = sortChains L (cyclicValueUnshift c (cyclicSortChains L c v.val)) := hunshift
    _ = v.val :=
      sortChains_unshift_cyclicSortChains L hcover hLnodup hnodup hdisj c v.val v.prop

/-- A fixed cyclic shift-and-sort is a permutation of a finite covering
disjoint-chain normal-form family. -/
noncomputable def cyclicSortChainsEquiv {n : ℕ}
    (L : List (List (Fin n))) (hcover : ChainsCover L) (hLnodup : L.Nodup)
    (hnodup : ∀ l ∈ L, l.Nodup)
    (hdisj : ∀ l₁ ∈ L, ∀ l₂ ∈ L, l₁ ≠ l₂ → ∀ i ∈ l₁, i ∉ l₂)
    (c : Fin (n + 1)) :
    {w : Fin n → Fin (n + 1) // IsChainSorted L w} ≃
      {w : Fin n → Fin (n + 1) // IsChainSorted L w} := by
  let F : {w : Fin n → Fin (n + 1) // IsChainSorted L w} →
      {w : Fin n → Fin (n + 1) // IsChainSorted L w} :=
    fun w => ⟨cyclicSortChains L c w, isChainSorted_cyclicSortChains_of_disjoint
      L hLnodup hnodup hdisj c w⟩
  have hinj : Function.Injective F := by
    intro w v h
    apply cyclicSortChains_injective_of_chainSorted L hcover hLnodup hnodup hdisj c
    have hval := congrArg Subtype.val h
    change cyclicSortChains L c w.val = cyclicSortChains L c v.val at hval
    exact hval
  exact Equiv.ofBijective F ⟨hinj, Finite.surjective_of_injective hinj⟩

/-- Among weakly chain-sorted words, the cyclic shift-and-sort action has one
parking word per orbit. -/
theorem card_chainSortedWords_eq_succ_mul_card_parking {n : ℕ}
    (L : List (List (Fin n))) (hcover : ChainsCover L) (hLnodup : L.Nodup)
    (hnodup : ∀ l ∈ L, l.Nodup)
    (hdisj : ∀ l₁ ∈ L, ∀ l₂ ∈ L, l₁ ≠ l₂ → ∀ i ∈ l₁, i ∉ l₂)
    [DecidablePred (IsChainSorted L)]
    [DecidablePred (fun w : {w : Fin n → Fin (n + 1) // IsChainSorted L w} =>
      IsParkingWord w.val)] :
    Fintype.card {w : Fin n → Fin (n + 1) // IsChainSorted L w} =
      (n + 1) * Fintype.card
        {w : {w : Fin n → Fin (n + 1) // IsChainSorted L w} // IsParkingWord w.val} := by
  classical
  let X := {w : Fin n → Fin (n + 1) // IsChainSorted L w}
  let act : Fin (n + 1) → X ≃ X :=
    cyclicSortChainsEquiv L hcover hLnodup hnodup hdisj
  have hunique : ∀ w : X, ∃! c : Fin (n + 1), IsParkingWord (act c w).val := by
    intro w
    change ∃! c : Fin (n + 1), IsParkingWord (cyclicSortChains L c w.val)
    exact existsUnique_isParkingWord_cyclicSortChains L hnodup w.val
  simpa only [X, act, Fintype.card_fin] using
    Fintype.card_eq_card_mul_card_subtype_of_existsUnique_equiv
      X (Fin (n + 1)) act
      (fun w => IsParkingWord w.val) hunique

/-- A cyclic value shift preserves distinct values read along any chain. -/
theorem nodup_map_cyclicValueShift {n : ℕ} (c : Fin (n + 1))
    (l : List (Fin n)) (w : Fin n → Fin (n + 1)) (h : (l.map w).Nodup) :
    (l.map (cyclicValueShift c w)).Nodup := by
  change (l.map ((finCycle c) ∘ w)).Nodup
  simpa only [List.map_map] using h.map (finCycle c).injective

/-- The shift-and-sort action makes every disjoint chain strictly increasing
when its input values are distinct on that chain. -/
theorem sortedLT_map_cyclicSortChains_of_disjoint {n : ℕ}
    (L : List (List (Fin n))) (hLnodup : L.Nodup)
    (hnodup : ∀ l ∈ L, l.Nodup)
    (hdisj : ∀ l₁ ∈ L, ∀ l₂ ∈ L, l₁ ≠ l₂ → ∀ i ∈ l₁, i ∉ l₂)
    (c : Fin (n + 1)) (w : Fin n → Fin (n + 1))
    (hvalues : ∀ l ∈ L, (l.map w).Nodup) :
    ∀ l ∈ L, (l.map (cyclicSortChains L c w)).SortedLT := by
  exact sortedLT_map_sortChains_of_disjoint L hLnodup hnodup hdisj
    (cyclicValueShift c w) (fun l hl =>
      nodup_map_cyclicValueShift c l w (hvalues l hl))

/-- A fixed cyclic shift-and-sort is a permutation of the strictly
chain-sorted normal-form family. -/
noncomputable def cyclicSortChainsStrictEquiv {n : ℕ}
    (L : List (List (Fin n))) (hcover : ChainsCover L) (hLnodup : L.Nodup)
    (hnodup : ∀ l ∈ L, l.Nodup)
    (hdisj : ∀ l₁ ∈ L, ∀ l₂ ∈ L, l₁ ≠ l₂ → ∀ i ∈ l₁, i ∉ l₂)
    (c : Fin (n + 1)) :
    {w : Fin n → Fin (n + 1) // IsStrictChainSorted L w} ≃
      {w : Fin n → Fin (n + 1) // IsStrictChainSorted L w} := by
  let F : {w : Fin n → Fin (n + 1) // IsStrictChainSorted L w} →
      {w : Fin n → Fin (n + 1) // IsStrictChainSorted L w} :=
    fun w => ⟨cyclicSortChains L c w,
      sortedLT_map_cyclicSortChains_of_disjoint L hLnodup hnodup hdisj c w
        (fun l hl => (w.prop l hl).pairwise.nodup)⟩
  have hinj : Function.Injective F := by
    intro w v h
    have hval := congrArg Subtype.val h
    change cyclicSortChains L c w.val = cyclicSortChains L c v.val at hval
    apply Subtype.ext
    let wWeak : {w : Fin n → Fin (n + 1) // IsChainSorted L w} :=
      ⟨w.val, isChainSorted_of_isStrictChainSorted L w.val w.prop⟩
    let vWeak : {w : Fin n → Fin (n + 1) // IsChainSorted L w} :=
      ⟨v.val, isChainSorted_of_isStrictChainSorted L v.val v.prop⟩
    have hweak : wWeak = vWeak :=
      cyclicSortChains_injective_of_chainSorted L hcover hLnodup hnodup hdisj c hval
    simpa only [wWeak, vWeak] using congrArg Subtype.val hweak
  exact Equiv.ofBijective F ⟨hinj, Finite.surjective_of_injective hinj⟩

/-- Among strictly chain-sorted words, the cyclic shift-and-sort action has
one parking word per orbit. -/
theorem card_strictChainSortedWords_eq_succ_mul_card_parking {n : ℕ}
    (L : List (List (Fin n))) (hcover : ChainsCover L) (hLnodup : L.Nodup)
    (hnodup : ∀ l ∈ L, l.Nodup)
    (hdisj : ∀ l₁ ∈ L, ∀ l₂ ∈ L, l₁ ≠ l₂ → ∀ i ∈ l₁, i ∉ l₂)
    [DecidablePred (IsStrictChainSorted L)]
    [DecidablePred (fun w : {w : Fin n → Fin (n + 1) // IsStrictChainSorted L w} =>
      IsParkingWord w.val)] :
    Fintype.card {w : Fin n → Fin (n + 1) // IsStrictChainSorted L w} =
      (n + 1) * Fintype.card
        {w : {w : Fin n → Fin (n + 1) // IsStrictChainSorted L w} // IsParkingWord w.val} := by
  classical
  let X := {w : Fin n → Fin (n + 1) // IsStrictChainSorted L w}
  let act : Fin (n + 1) → X ≃ X :=
    cyclicSortChainsStrictEquiv L hcover hLnodup hnodup hdisj
  have hunique : ∀ w : X, ∃! c : Fin (n + 1), IsParkingWord (act c w).val := by
    intro w
    change ∃! c : Fin (n + 1), IsParkingWord (cyclicSortChains L c w.val)
    exact existsUnique_isParkingWord_cyclicSortChains L hnodup w.val
  simpa only [X, act, Fintype.card_fin] using
    Fintype.card_eq_card_mul_card_subtype_of_existsUnique_equiv
      X (Fin (n + 1)) act
      (fun w => IsParkingWord w.val) hunique

/-- Sorting along duplicate-free chains preserves the unique cyclic parking
representative in the embedded finite family. -/
theorem existsUnique_cyclicSortChains_mem_embeddedParkingFunctions {n : ℕ}
    (L : List (List (Fin (n + 1)))) (hL : ∀ l ∈ L, l.Nodup)
    (w : Fin (n + 1) → Fin (n + 2)) :
    ∃! c : Fin (n + 2), cyclicSortChains L c w ∈ embeddedParkingFunctions n := by
  simpa only [mem_embeddedParkingFunctions_iff_isParkingWord] using
    (existsUnique_isParkingWord_cyclicSortChains L hL w)

end

end RealRooted.ParkingFunctions
