import RealRooted.ParkingFunctions.Descents.Basic
import RealRooted.ParkingFunctions.Descents.ChainSort
import RealRooted.Mathlib.Data.List.OfFn
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Data.List.Sort

/-!
# Cyclic value action for parking-function descents

This low finite-action layer records the cyclic value shifts used in the
Diaconis--Hicks comparison between parking functions and words on an alphabet
of size one larger.  It proves the orbit and value-reordering facts; selecting
the unique parking representative is later work.
-/

namespace RealRooted.ParkingFunctions

noncomputable section

/-- Cyclically shift every value of a word on `Fin (n + 1)`. -/
def cyclicValueShiftEquiv (n : ℕ) (c : Fin (n + 1)) :
    (Fin n → Fin (n + 1)) ≃ (Fin n → Fin (n + 1)) :=
  Equiv.piCongrRight fun _ => finCycle c

/-- The word obtained by cyclically shifting all values by `c`. -/
def cyclicValueShift {n : ℕ} (c : Fin (n + 1))
    (w : Fin n → Fin (n + 1)) : Fin n → Fin (n + 1) :=
  cyclicValueShiftEquiv n c w

/-- Undo a fixed cyclic value shift on every value of a word. -/
def cyclicValueUnshift {n : ℕ} (c : Fin (n + 1))
    (w : Fin n → Fin (n + 1)) : Fin n → Fin (n + 1) :=
  fun i => (finCycle c).symm (w i)

@[simp]
theorem cyclicValueUnshift_cyclicValueShift {n : ℕ} (c : Fin (n + 1))
    (w : Fin n → Fin (n + 1)) :
    cyclicValueUnshift c (cyclicValueShift c w) = w := by
  funext i
  exact (finCycle c).symm_apply_apply (w i)

/-- The parking condition for a word on an alphabet with one extra letter. -/
def IsParkingWord {n : ℕ} (w : Fin n → Fin (n + 1)) : Prop :=
  ∀ k : ℕ, k ≤ n →
    k ≤ (Finset.univ.filter fun i => (w i).val < k).card

private theorem card_filter_eq_multiset_countP {n : ℕ} (w : Fin n → Fin (n + 1)) (k : ℕ) :
    (Finset.univ.filter fun i => (w i).val < k).card =
      Multiset.countP (fun v : Fin (n + 1) => (v : ℕ) < k)
        (Multiset.map w Finset.univ.val) := by
  rw [Multiset.countP_map]
  rfl

/-- The extra-alphabet parking condition depends only on the value multiset. -/
theorem isParkingWord_iff_of_multiset_eq {n : ℕ} {w v : Fin n → Fin (n + 1)}
    (h : Multiset.map w Finset.univ.val = Multiset.map v Finset.univ.val) :
    IsParkingWord w ↔ IsParkingWord v := by
  unfold IsParkingWord
  simp only [card_filter_eq_multiset_countP, h]

/-- A periodic integer height function with a drop of one has a unique cyclic
minimum. -/
theorem existsUnique_cycle_minimum (N : ℕ) (hN : 0 < N) (S : ℕ → ℤ)
    (hS : ∀ m, S (m + N) = S m - 1) :
    ∃! s : ℕ, s < N ∧ ∀ k < N, S s ≤ S (s + k) := by
  classical
  have hex : ∃ s, s < N ∧ ∀ t < N, S s ≤ S t := by
    obtain ⟨s, hs, hmin⟩ := Finset.exists_min_image (Finset.range N) S ⟨0, by simp [hN]⟩
    exact ⟨s, Finset.mem_range.1 hs, fun t ht => hmin t (Finset.mem_range.2 ht)⟩
  set m0 := Nat.find hex with hm0def
  obtain ⟨hm0N, hm0min⟩ : m0 < N ∧ ∀ t < N, S m0 ≤ S t := Nat.find_spec hex
  have hfirst : ∀ r < m0, S m0 < S r := by
    intro r hr
    have hnot := Nat.find_min hex hr
    push Not at hnot
    obtain ⟨t, htN, ht⟩ := hnot (by lia)
    exact lt_of_le_of_lt (hm0min t htN) ht
  refine ⟨m0, ⟨hm0N, ?_⟩, ?_⟩
  · intro k hk
    rcases lt_or_ge (m0 + k) N with h | h
    · exact hm0min _ h
    · rw [show m0 + k = (m0 + k - N) + N by lia, hS]
      have := hfirst (m0 + k - N) (by lia)
      lia
  · rintro s ⟨hsN, hs⟩
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have h1 := hs (m0 - s) (by lia)
      rw [show s + (m0 - s) = m0 by lia] at h1
      have h2 := hfirst s h
      lia
    · have h1 := hs (m0 + N - s) (by lia)
      rw [show s + (m0 + N - s) = m0 + N by lia, hS] at h1
      have h2 := hm0min s hsN
      lia

variable {n : ℕ} (w : Fin n → Fin (n + 1))

/-- Count the periodic lifts of the values of a word below a natural bound. -/
def parkingPointCount (m : ℕ) : ℕ :=
  ∑ i, (m + n - (w i : ℕ)) / (n + 1)

/-- The height function used in Pollak's cyclic-minimum argument. -/
def parkingHeight (m : ℕ) : ℤ :=
  (parkingPointCount w m : ℤ) - m

theorem parkingPointCount_add_period (m : ℕ) :
    parkingPointCount w (m + (n + 1)) = parkingPointCount w m + n := by
  have h : ∀ i : Fin n, (m + (n + 1) + n - (w i : ℕ)) / (n + 1)
      = (m + n - (w i : ℕ)) / (n + 1) + 1 := by
    intro i
    have hi := (w i).isLt
    rw [show m + (n + 1) + n - (w i : ℕ) =
        (m + n - (w i : ℕ)) + (n + 1) by lia,
      Nat.add_div_right _ (by lia)]
  simp only [parkingPointCount, h, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]

theorem parkingHeight_add_period (m : ℕ) :
    parkingHeight w (m + (n + 1)) = parkingHeight w m - 1 := by
  simp only [parkingHeight, parkingPointCount_add_period, Nat.cast_add]
  push_cast
  ring

private theorem parking_point_div (v s k r : ℕ) (hv : v ≤ n) (hs : s ≤ n)
    (hk : k ≤ n + 1)
    (hr : (s ≤ v ∧ r = v - s) ∨ (v < s ∧ r + s = v + n + 1)) :
    (s + k + n - v) / (n + 1) =
      (s + n - v) / (n + 1) + (if r < k then 1 else 0) := by
  have h1 : (s + n - v) / (n + 1) = if v < s then 1 else 0 := by
    split <;> [exact Nat.div_eq_of_lt_le (by lia) (by lia);
               exact Nat.div_eq_of_lt_le (by lia) (by lia)]
  rw [h1]
  rcases hr with ⟨h, hrv⟩ | ⟨h, hrv⟩ <;> split <;> split <;>
    first
      | lia
      | (refine Nat.div_eq_of_lt_le ?_ ?_ <;> lia)

private theorem parking_shift_residue_cases (v s c : ℕ) (hv : v ≤ n) (hc : c ≤ n)
    (hsc : s + c = 0 ∨ s + c = n + 1) :
    (s ≤ v ∧ (v + c) % (n + 1) = v - s) ∨
      (v < s ∧ (v + c) % (n + 1) + s = v + n + 1) := by
  rcases hsc with h | h
  · exact Or.inl ⟨by lia, by rw [Nat.mod_eq_of_lt (by lia)]; lia⟩
  · rcases Nat.lt_or_ge v s with hsv | hsv
    · exact Or.inr ⟨hsv, by rw [Nat.mod_eq_of_lt (by lia)]; lia⟩
    · refine Or.inl ⟨hsv, ?_⟩
      rw [show v + c = (v - s) + (n + 1) by lia, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by lia)]

private theorem card_filter_cyclicValueShift (c : Fin (n + 1)) (s k : ℕ) (hs : s ≤ n)
    (hk : k ≤ n + 1) (hsc : s + (c : ℕ) = 0 ∨ s + (c : ℕ) = n + 1) :
    (Finset.univ.filter fun i => (cyclicValueShift c w i).val < k).card +
      parkingPointCount w s = parkingPointCount w (s + k) := by
  rw [Finset.card_filter]
  simp only [parkingPointCount, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hv : (w i : ℕ) ≤ n := by have := (w i).isLt; lia
  have hc : (c : ℕ) ≤ n := by have := c.isLt; lia
  change (if (finCycle c (w i)).val < k then 1 else 0) +
    (s + n - (w i : ℕ)) / (n + 1) = _
  rw [finCycle_apply]
  have hval : ((w i + c : Fin (n + 1)) : ℕ) =
      ((w i : ℕ) + (c : ℕ)) % (n + 1) := Fin.val_add _ _
  rw [hval, parking_point_div (w i : ℕ) s k _ hv hs hk
    (parking_shift_residue_cases (w i : ℕ) s (c : ℕ) hv hc hsc)]
  lia

private theorem isParkingWord_cyclicValueShift_iff (c : Fin (n + 1)) (s : ℕ) (hs : s ≤ n)
    (hsc : s + (c : ℕ) = 0 ∨ s + (c : ℕ) = n + 1) :
    IsParkingWord (cyclicValueShift c w) ↔
      ∀ k < n + 1, parkingHeight w s ≤ parkingHeight w (s + k) := by
  unfold IsParkingWord parkingHeight
  constructor
  · intro h k hk
    have hc := card_filter_cyclicValueShift w c s k hs (by lia) hsc
    have h1 := h k (by lia)
    push_cast
    lia
  · intro h k hk
    have hc := card_filter_cyclicValueShift w c s k hs (by lia) hsc
    have h1 := h k (by lia)
    push_cast at h1
    lia

private def parkingShiftStart (n c : ℕ) : ℕ :=
  if c = 0 then 0 else n + 1 - c

private theorem parkingShiftStart_le (c : ℕ) (_hc : c ≤ n) : parkingShiftStart n c ≤ n := by
  unfold parkingShiftStart
  split <;> lia

private theorem parkingShiftStart_add (c : ℕ) (hc : c ≤ n) :
    parkingShiftStart n c + c = 0 ∨ parkingShiftStart n c + c = n + 1 := by
  unfold parkingShiftStart
  split <;> lia

private theorem parkingShiftStart_involutive (c : ℕ) (hc : c ≤ n) :
    parkingShiftStart n (parkingShiftStart n c) = c := by
  unfold parkingShiftStart
  split <;> split <;> lia

/-- **Pollak's cycle lemma for parking words.**  Every word has exactly one
cyclic value shift satisfying the extra-alphabet parking condition. -/
theorem existsUnique_isParkingWord_cyclicValueShift :
    ∃! c : Fin (n + 1), IsParkingWord (cyclicValueShift c w) := by
  obtain ⟨s₀, ⟨hs₀lt, hs₀⟩, huniq⟩ :=
    existsUnique_cycle_minimum (n + 1) (Nat.succ_pos n) (parkingHeight w)
      (parkingHeight_add_period w)
  have hs₀le : s₀ ≤ n := by lia
  refine ⟨⟨parkingShiftStart n s₀, by
    have := parkingShiftStart_le s₀ hs₀le
    lia⟩, ?_, ?_⟩
  · dsimp only
    rw [isParkingWord_cyclicValueShift_iff w _ s₀ hs₀le ?_]
    · exact hs₀
    · simpa [add_comm] using parkingShiftStart_add (n := n) s₀ hs₀le
  · intro c hc
    have hcle : (c : ℕ) ≤ n := by have := c.isLt; lia
    have hstart := parkingShiftStart_add (n := n) (c : ℕ) hcle
    rw [isParkingWord_cyclicValueShift_iff w c (parkingShiftStart n (c : ℕ))
      (parkingShiftStart_le _ hcle) hstart] at hc
    have : parkingShiftStart n (c : ℕ) = s₀ :=
      huniq _ ⟨by
        have := parkingShiftStart_le (n := n) (c : ℕ) hcle
        lia, hc⟩
    apply Fin.ext
    simp only
    rw [← this, parkingShiftStart_involutive _ hcle]

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

@[simp]
theorem cyclicValueShift_apply {n : ℕ} (c : Fin (n + 1))
    (w : Fin n → Fin (n + 1)) (i : Fin n) :
    cyclicValueShift c w i = finCycle c (w i) := rfl

/-- Every fixed cyclic value shift is a bijection on words. -/
theorem cyclicValueShift_bijective {n : ℕ} (c : Fin (n + 1)) :
    Function.Bijective (cyclicValueShift c :
      (Fin n → Fin (n + 1)) → Fin n → Fin (n + 1)) :=
  (cyclicValueShiftEquiv n c).bijective

/-- Cyclic value shifts preserve equality relations between positions. -/
theorem cyclicValueShift_eq_iff {n : ℕ} (c : Fin (n + 1))
    (w : Fin n → Fin (n + 1)) (i j : Fin n) :
    cyclicValueShift c w i = cyclicValueShift c w j ↔ w i = w j := by
  change finCycle c (w i) = finCycle c (w j) ↔ w i = w j
  exact (finCycle c).injective.eq_iff

/-- For a nonempty word, distinct cyclic shifts produce distinct words. -/
theorem cyclicValueShift_injective_in_shift {n : ℕ} (hn : 0 < n)
    (w : Fin n → Fin (n + 1)) :
    Function.Injective (fun c : Fin (n + 1) => cyclicValueShift c w) := by
  intro c d h
  have hzero := congrFun h ⟨0, hn⟩
  change w ⟨0, hn⟩ + c = w ⟨0, hn⟩ + d at hzero
  exact add_left_cancel hzero

/-- The cyclic value orbit of a nonempty word has the full alphabet size. -/
theorem card_cyclicValueShift_orbit {n : ℕ} (hn : 0 < n)
    (w : Fin n → Fin (n + 1)) :
    (Finset.univ.image fun c => cyclicValueShift c w).card = n + 1 := by
  rw [Finset.card_image_of_injective _ (cyclicValueShift_injective_in_shift hn w)]
  simp

/-- Regard a parking word as a word on the alphabet with one additional
letter. -/
def parkingWordEmbed {n : ℕ} (w : Fin n → Fin n) : Fin n → Fin (n + 1) :=
  fun i => (w i).castSucc

@[simp]
theorem parkingWordEmbed_apply {n : ℕ} (w : Fin n → Fin n) (i : Fin n) :
    parkingWordEmbed w i = (w i).castSucc := rfl

/-- The embedded-word and ordinary parking conditions agree. -/
theorem isParkingWord_parkingWordEmbed_iff {n : ℕ} (w : Fin n → Fin n) :
    IsParkingWord (parkingWordEmbed w) ↔ IsParkingFunction w := by
  constructor <;> intro hw k hk
  · simpa [IsParkingWord, parkingWordEmbed] using hw k hk
  · simpa [IsParkingWord, parkingWordEmbed] using hw k hk

/-- The alphabet embedding of parking words is injective. -/
theorem parkingWordEmbed_injective {n : ℕ} :
    Function.Injective (parkingWordEmbed :
      (Fin n → Fin n) → Fin n → Fin (n + 1)) := by
  intro w v h
  funext i
  apply Fin.castSucc_injective
  exact congrFun h i

/-- Embedding the alphabet of a nonempty parking word preserves its descent
set. -/
theorem descentSet_parkingWordEmbed {n : ℕ} (w : Fin (n + 1) → Fin (n + 1)) :
    descentSet (parkingWordEmbed w) = descentSet w := by
  ext i
  simp [mem_descentSet_iff, parkingWordEmbed]

/-- Embedding the alphabet of a nonempty parking word preserves its descent
number. -/
theorem descentNumber_parkingWordEmbed {n : ℕ} (w : Fin (n + 1) → Fin (n + 1)) :
    descentNumber (parkingWordEmbed w) = descentNumber w := by
  rw [descentNumber, descentNumber, descentSet_parkingWordEmbed]

/-- The embedded parking functions form a literal subfamily of words over the
alphabet with one additional letter. -/
def embeddedParkingFunctions (n : ℕ) : Finset (Fin (n + 1) → Fin (n + 2)) :=
  (parkingFunctions (n + 1)).image parkingWordEmbed

/-- The extra-alphabet parking condition characterizes the embedded parking
family. -/
theorem mem_embeddedParkingFunctions_iff_isParkingWord {n : ℕ}
    {w : Fin (n + 1) → Fin (n + 2)} :
    w ∈ embeddedParkingFunctions n ↔ IsParkingWord w := by
  constructor
  · rw [embeddedParkingFunctions, Finset.mem_image]
    rintro ⟨p, hp, rfl⟩
    exact (isParkingWord_parkingWordEmbed_iff p).mpr (mem_parkingFunctions_iff.mp hp)
  · intro hw
    let s := Finset.univ.filter fun i : Fin (n + 1) => (w i).val < n + 1
    have hs_subset : s ⊆ Finset.univ := by
      intro i _
      simp
    have hsle : s.card ≤ n + 1 := by
      simpa using Finset.card_le_card hs_subset
    have hsge : n + 1 ≤ s.card := by
      simpa [s] using hw (n + 1) le_rfl
    have hseq : s = Finset.univ :=
      Finset.eq_of_subset_of_card_le hs_subset (by simpa using hsge)
    have hlt : ∀ i : Fin (n + 1), (w i).val < n + 1 := by
      intro i
      have hi : i ∈ s := by rw [hseq]; simp
      exact (Finset.mem_filter.mp hi).2
    let p : Fin (n + 1) → Fin (n + 1) := fun i =>
      Fin.castPred (w i) (by
        intro hlast
        have hlt' := hlt i
        simp [hlast] at hlt')
    have hpw : parkingWordEmbed p = w := by
      funext i
      apply Fin.ext
      simp [parkingWordEmbed, p, Fin.castPred]
    rw [embeddedParkingFunctions, Finset.mem_image]
    refine ⟨p, mem_parkingFunctions_iff.mpr ?_, hpw⟩
    apply (isParkingWord_parkingWordEmbed_iff p).mp
    simpa [hpw] using hw

/-- Every word has exactly one cyclic shift in the embedded parking family. -/
theorem existsUnique_cyclicValueShift_mem_embeddedParkingFunctions {n : ℕ}
    (w : Fin (n + 1) → Fin (n + 2)) :
    ∃! c : Fin (n + 2), cyclicValueShift c w ∈ embeddedParkingFunctions n := by
  simpa only [mem_embeddedParkingFunctions_iff_isParkingWord] using
    (existsUnique_isParkingWord_cyclicValueShift w)

/-- Sorting along duplicate-free chains preserves the unique cyclic parking
representative in the embedded finite family. -/
theorem existsUnique_cyclicSortChains_mem_embeddedParkingFunctions {n : ℕ}
    (L : List (List (Fin (n + 1)))) (hL : ∀ l ∈ L, l.Nodup)
    (w : Fin (n + 1) → Fin (n + 2)) :
    ∃! c : Fin (n + 2), cyclicSortChains L c w ∈ embeddedParkingFunctions n := by
  simpa only [mem_embeddedParkingFunctions_iff_isParkingWord] using
    (existsUnique_isParkingWord_cyclicSortChains L hL w)

/-- The parking descent polynomial is the descent-generating polynomial of its
embedded finite word family. -/
theorem parkingDescentPolynomial_succ_eq_descentGeneratingPolynomial_embedded
    (n : ℕ) :
    parkingDescentPolynomial (n + 1) =
      descentGeneratingPolynomial (R := ℝ) (embeddedParkingFunctions n) := by
  unfold parkingDescentPolynomial descentGeneratingPolynomial embeddedParkingFunctions
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro w hw
    rw [descentNumber_parkingWordEmbed]
  · intro w hw v hv hwv
    exact parkingWordEmbed_injective hwv

end

end RealRooted.ParkingFunctions
