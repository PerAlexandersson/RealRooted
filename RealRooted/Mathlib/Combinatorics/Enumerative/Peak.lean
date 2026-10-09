import RealRooted.Mathlib.Combinatorics.Enumerative.Descent

/-!
# Peaks and valleys of words

This module uses the zero-based position convention documented in `Descent`.
-/

namespace List

variable {α β : Type*} [LinearOrder α] [LinearOrder β]

private theorem pred_lt_length {i n : ℕ} (hi : 0 < i) (h : i + 1 < n) : i - 1 < n := by
  lia

private theorem index_lt_length {i n : ℕ} (h : i + 1 < n) : i < n := by
  exact Nat.lt_of_succ_lt (by simpa [Nat.succ_eq_add_one] using h)

private def isPeak (l : List α) (i : ℕ) : Bool :=
  if hi : 0 < i then
    if h : i + 1 < l.length then
      decide (l[i - 1]'(pred_lt_length hi h) < l[i]'(index_lt_length h) ∧
        l[i + 1]'h < l[i]'(index_lt_length h))
    else false
  else false

private def isValley (l : List α) (i : ℕ) : Bool :=
  if hi : 0 < i then
    if h : i + 1 < l.length then
      decide (l[i]'(index_lt_length h) < l[i - 1]'(pred_lt_length hi h) ∧
        l[i]'(index_lt_length h) < l[i + 1]'h)
    else false
  else false

private def isLeftPeak (l : List α) : Bool :=
  if h : 1 < l.length then decide (l[1]'h < l[0]'(by lia)) else false

/-- The interior peak positions of a word. -/
def peakSet (l : List α) : Finset ℕ :=
  (Finset.range l.length).filter (fun i => isPeak l i)

/-- The interior valley positions of a word. -/
def valleySet (l : List α) : Finset ℕ :=
  (Finset.range l.length).filter (fun i => isValley l i)

/-- The peaks, allowing position zero when it is larger than its right neighbor. -/
def leftPeakSet (l : List α) : Finset ℕ :=
  l.peakSet ∪ if isLeftPeak l then {0} else ∅

/-- The number of interior peaks of a word. -/
def peakCount (l : List α) : ℕ := l.peakSet.card

/-- The number of interior valleys of a word. -/
def valleyCount (l : List α) : ℕ := l.valleySet.card

/-- The number of left peaks of a word. -/
def leftPeakCount (l : List α) : ℕ := l.leftPeakSet.card

/-- Membership in `peakSet`, in terms of the three neighboring entries. -/
@[simp] theorem mem_peakSet {l : List α} {i : ℕ} :
    i ∈ l.peakSet ↔ ∃ hi : 0 < i, ∃ h : i + 1 < l.length,
      l[i - 1]'(pred_lt_length hi h) < l[i]'(index_lt_length h) ∧
        l[i + 1]'h < l[i]'(index_lt_length h) := by
  change i ∈ (Finset.range l.length).filter (fun j => isPeak l j) ↔ _
  rw [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨_, hi⟩
    by_cases hi0 : 0 < i
    · by_cases h : i + 1 < l.length
      · refine ⟨hi0, h, ?_⟩
        simpa [isPeak, hi0, h] using hi
      · simp [isPeak, hi0, h] at hi
    · simp [isPeak, hi0] at hi
  · rintro ⟨hi, h, hlt⟩
    constructor
    · exact index_lt_length h
    · simpa [isPeak, hi, h] using hlt

/-- Membership in `valleySet`, in terms of the three neighboring entries. -/
@[simp] theorem mem_valleySet {l : List α} {i : ℕ} :
    i ∈ l.valleySet ↔ ∃ hi : 0 < i, ∃ h : i + 1 < l.length,
      l[i]'(index_lt_length h) < l[i - 1]'(pred_lt_length hi h) ∧
        l[i]'(index_lt_length h) < l[i + 1]'h := by
  change i ∈ (Finset.range l.length).filter (fun j => isValley l j) ↔ _
  rw [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨_, hi⟩
    by_cases hi0 : 0 < i
    · by_cases h : i + 1 < l.length
      · refine ⟨hi0, h, ?_⟩
        simpa [isValley, hi0, h] using hi
      · simp [isValley, hi0, h] at hi
    · simp [isValley, hi0] at hi
  · rintro ⟨hi, h, hlt⟩
    constructor
    · exact index_lt_length h
    · simpa [isValley, hi, h] using hlt

/-- Every interior peak is a descent position. -/
theorem peakSet_subset_descentSet (l : List α) : l.peakSet ⊆ l.descentSet := by
  intro i hi
  obtain ⟨hi, h, hlt⟩ := mem_peakSet.mp hi
  exact mem_descentSet.mpr ⟨h, hlt.2⟩

/-- The ascent immediately preceding an interior peak is an ascent. -/
theorem sub_one_mem_ascentSet_of_mem_peakSet {l : List α} {i : ℕ}
    (hi : i ∈ l.peakSet) : i - 1 ∈ l.ascentSet := by
  obtain ⟨hi0, h, hlt⟩ := mem_peakSet.mp hi
  have hprev : i - 1 + 1 < l.length := by lia
  have hindex : i - 1 + 1 = i := by lia
  exact mem_ascentSet.mpr ⟨hprev, by
    simpa [hindex] using hlt.1⟩

/-- Two consecutive positions cannot both be interior peaks. -/
theorem succ_not_mem_peakSet_of_mem_peakSet {l : List α} {i : ℕ}
    (hi : i ∈ l.peakSet) : i + 1 ∉ l.peakSet := by
  intro hj
  obtain ⟨hi0, h, hlt⟩ := mem_peakSet.mp hi
  obtain ⟨_, _, hjlt⟩ := mem_peakSet.mp hj
  exact (not_lt_of_ge (le_of_lt hlt.2)) (by simpa using hjlt.1)

/-- A strictly antitone map exchanges peaks and valleys. -/
theorem peakSet_map_strictAnti (l : List α) (f : α → β) (hf : StrictAnti f) :
    (l.map f).peakSet = l.valleySet := by
  ext i
  constructor
  · intro hi
    obtain ⟨hi0, h, hlt⟩ := mem_peakSet.mp hi
    have h' : i + 1 < l.length := by simpa using h
    refine mem_valleySet.mpr ⟨hi0, h', ?_⟩
    rw [List.getElem_map, List.getElem_map, List.getElem_map] at hlt
    simpa only [hf.lt_iff_gt] using hlt
  · intro hi
    obtain ⟨hi0, h, hlt⟩ := mem_valleySet.mp hi
    have h' : i + 1 < (l.map f).length := by simpa using h
    refine mem_peakSet.mpr ⟨hi0, h', ?_⟩
    rw [List.getElem_map, List.getElem_map, List.getElem_map]
    simpa only [hf.lt_iff_gt] using hlt

/-- A strictly antitone map exchanges valleys and peaks. -/
theorem valleySet_map_strictAnti (l : List α) (f : α → β) (hf : StrictAnti f) :
    (l.map f).valleySet = l.peakSet := by
  ext i
  constructor
  · intro hi
    obtain ⟨hi0, h, hlt⟩ := mem_valleySet.mp hi
    have h' : i + 1 < l.length := by simpa using h
    refine mem_peakSet.mpr ⟨hi0, h', ?_⟩
    rw [List.getElem_map, List.getElem_map, List.getElem_map] at hlt
    simpa only [hf.lt_iff_gt] using hlt
  · intro hi
    obtain ⟨hi0, h, hlt⟩ := mem_peakSet.mp hi
    have h' : i + 1 < (l.map f).length := by simpa using h
    refine mem_valleySet.mpr ⟨hi0, h', ?_⟩
    rw [List.getElem_map, List.getElem_map, List.getElem_map]
    simpa only [hf.lt_iff_gt] using hlt

/-- A strictly monotone map preserves interior peaks. -/
theorem peakSet_map_strictMono (l : List α) (f : α → β) (hf : StrictMono f) :
    (l.map f).peakSet = l.peakSet := by
  ext i
  constructor
  · intro hi
    obtain ⟨hi0, h, hlt⟩ := mem_peakSet.mp hi
    have h' : i + 1 < l.length := by simpa using h
    refine mem_peakSet.mpr ⟨hi0, h', ?_⟩
    rw [List.getElem_map, List.getElem_map, List.getElem_map] at hlt
    simpa only [hf.lt_iff_lt] using hlt
  · intro hi
    obtain ⟨hi0, h, hlt⟩ := mem_peakSet.mp hi
    have h' : i + 1 < (l.map f).length := by simpa using h
    refine mem_peakSet.mpr ⟨hi0, h', ?_⟩
    rw [List.getElem_map, List.getElem_map, List.getElem_map]
    simpa only [hf.lt_iff_lt] using hlt

/-- A strictly monotone map preserves interior valleys. -/
theorem valleySet_map_strictMono (l : List α) (f : α → β) (hf : StrictMono f) :
    (l.map f).valleySet = l.valleySet := by
  ext i
  constructor
  · intro hi
    obtain ⟨hi0, h, hlt⟩ := mem_valleySet.mp hi
    have h' : i + 1 < l.length := by simpa using h
    refine mem_valleySet.mpr ⟨hi0, h', ?_⟩
    rw [List.getElem_map, List.getElem_map, List.getElem_map] at hlt
    simpa only [hf.lt_iff_lt] using hlt
  · intro hi
    obtain ⟨hi0, h, hlt⟩ := mem_valleySet.mp hi
    have h' : i + 1 < (l.map f).length := by simpa using h
    refine mem_valleySet.mpr ⟨hi0, h', ?_⟩
    rw [List.getElem_map, List.getElem_map, List.getElem_map]
    simpa only [hf.lt_iff_lt] using hlt

/-- Interior peaks occupy at most half of the positions before the last entry. -/
theorem peakCount_le (l : List α) : 2 * l.peakCount ≤ l.length - 1 := by
  let s := l.peakSet
  let t := s.image (fun i => i - 1)
  have hinj : Set.InjOn (fun i => i - 1) s := by
    intro i hi j hj hij
    obtain ⟨hi0, _, _⟩ := mem_peakSet.mp hi
    obtain ⟨hj0, _, _⟩ := mem_peakSet.mp hj
    lia
  have hdisj : _root_.Disjoint s t := by
    rw [Finset.disjoint_left]
    intro i hi hti
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hti
    obtain ⟨_, hjlast, _⟩ := mem_peakSet.mp hj
    have hindex : j - 1 + 1 = j := by lia
    exact succ_not_mem_peakSet_of_mem_peakSet hi (by
      simpa [s, hindex] using hj)
  have hsubset : s ∪ t ⊆ Finset.range (l.length - 1) := by
    intro i hi
    rcases Finset.mem_union.mp hi with hi | hi
    · obtain ⟨_, h, _⟩ := mem_peakSet.mp hi
      rw [Finset.mem_range]
      lia
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
      obtain ⟨_, h, _⟩ := mem_peakSet.mp hj
      rw [Finset.mem_range]
      lia
  calc
    2 * l.peakCount = s.card + t.card := by
      dsimp [s, t]
      rw [Finset.card_image_of_injOn hinj]
      simp [s, peakCount, two_mul]
    _ = (s ∪ t).card := (Finset.card_union_of_disjoint hdisj).symm
    _ ≤ (Finset.range (l.length - 1)).card := Finset.card_le_card hsubset
    _ = l.length - 1 := Finset.card_range _

/-- Reversal sends an interior peak at `i` to one at `length - 1 - i`. -/
theorem peakSet_reverse (l : List α) :
    l.reverse.peakSet = l.peakSet.image (fun i => l.length - 1 - i) := by
  ext i
  constructor
  · intro hi
    obtain ⟨hi0, hi1, hlt⟩ := mem_peakSet.mp hi
    have hi1' : i + 1 < l.length := by
      simpa only [List.length_reverse] using hi1
    let a := l.length - 1 - i
    have ha0 : 0 < a := by
      dsimp [a]
      lia
    have ha1 : a + 1 < l.length := by
      dsimp [a]
      lia
    have hleft : a - 1 = l.length - 1 - (i + 1) := by
      dsimp [a]
      lia
    have hright : a + 1 = l.length - 1 - (i - 1) := by
      dsimp [a]
      lia
    have hlt' := hlt
    simp only [List.getElem_reverse] at hlt'
    have ha : a ∈ l.peakSet := mem_peakSet.mpr ⟨ha0, ha1, by
      simpa [a, hleft, hright] using And.intro hlt'.2 hlt'.1⟩
    exact Finset.mem_image.mpr ⟨a, ha, by dsimp [a]; lia⟩
  · intro hi
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨ha0, ha1, hlt⟩ := mem_peakSet.mp ha
    have hi0 : 0 < l.length - 1 - a := by lia
    have hi1 : l.length - 1 - a + 1 < l.length := by lia
    have hleft : l.length - 1 - (l.length - 1 - a - 1) = a + 1 := by
      lia
    have hright : l.length - 1 - (l.length - 1 - a + 1) = a - 1 := by
      lia
    have hcenter : l.length - 1 - (l.length - 1 - a) = a := by
      lia
    have hi1' : l.length - 1 - a + 1 < l.reverse.length := by
      simpa only [List.length_reverse] using hi1
    refine mem_peakSet.mpr ⟨hi0, hi1', ?_⟩
    simp only [List.getElem_reverse]
    simpa [hleft, hright, hcenter] using And.intro hlt.2 hlt.1

/-- The empty word has no peaks. -/
@[simp] theorem peakSet_nil : peakSet ([] : List α) = ∅ := by
  rfl

/-- A one-letter word has no peaks. -/
@[simp] theorem peakSet_singleton (a : α) : peakSet [a] = ∅ := by
  rfl

/-- Position zero belongs to `leftPeakSet` exactly when it is a left peak. -/
theorem mem_leftPeakSet_zero {l : List α} :
    0 ∈ l.leftPeakSet ↔ 0 ∈ l.peakSet ∨ ∃ h : 1 < l.length, l[1]'h < l[0]'(by lia) := by
  by_cases h : ∃ h : 1 < l.length, l[1]'h < l[0]'(by lia)
  · simp [leftPeakSet, h, isLeftPeak]
  · simp [leftPeakSet, h, isLeftPeak]

example : [3, 1, 4, 1, 5, 9, 2, 6].peakSet = {2, 5} := by decide

example : [3, 1, 4, 1, 5, 9, 2, 6].valleySet = {1, 3, 6} := by decide

example : [3, 1, 4, 1, 5, 9, 2, 6].leftPeakSet = {0, 2, 5} := by decide

end List
