import Mathlib.Data.Fin.Rev
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Chain
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Range
import Mathlib.Data.Finset.Union
import Mathlib.Tactic.Linarith
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Basic

/-!
# Descents, ascents, and the major index of a word

Words are lists `l : List α` with `[LinearOrder α]`.  Positions are numbered from
zero: position `i` compares entries `i` and `i + 1`.  Thus the classical
one-based descent set is obtained by adding one to every member of `descentSet`;
we do not introduce a second definition for that convention.

All statistics in this file are computable `Finset ℕ`s (and their cardinalities
or sums), so small examples can be checked by `decide`.
-/

namespace List

variable {α β : Type*} [LinearOrder α] [LinearOrder β]

private theorem lt_length_of_succ_lt {i n : ℕ} (h : i + 1 < n) : i < n := by
  exact Nat.lt_of_succ_lt (by simpa [Nat.succ_eq_add_one] using h)

private def isDescent (l : List α) (i : ℕ) : Bool :=
  if h : i + 1 < l.length then
    decide (l[i + 1]'h < l[i]'(lt_length_of_succ_lt h))
  else false

private def isAscent (l : List α) (i : ℕ) : Bool :=
  if h : i + 1 < l.length then
    decide (l[i]'(lt_length_of_succ_lt h) < l[i + 1]'h)
  else false

/-- The zero-based descent positions of a word. -/
def descentSet (l : List α) : Finset ℕ :=
  (Finset.range l.length).filter (fun i => isDescent l i)

/-- The zero-based ascent positions of a word. -/
def ascentSet (l : List α) : Finset ℕ :=
  (Finset.range l.length).filter (fun i => isAscent l i)

/-- The number of descents of a word. -/
def descentCount (l : List α) : ℕ := l.descentSet.card

/-- The number of ascents of a word. -/
def ascentCount (l : List α) : ℕ := l.ascentSet.card

/-- The major index, with the zero-based convention for descent positions. -/
def majorIndex (l : List α) : ℕ := ∑ i ∈ l.descentSet, (i + 1)

/-- Membership in `descentSet`, in terms of adjacent list entries. -/
@[simp] theorem mem_descentSet {l : List α} {i : ℕ} :
    i ∈ l.descentSet ↔
      ∃ h : i + 1 < l.length, l[i + 1]'h < l[i]'(lt_length_of_succ_lt h) := by
  change i ∈ (Finset.range l.length).filter (fun j => isDescent l j) ↔ _
  rw [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨_, hi⟩
    by_cases h : i + 1 < l.length
    · refine ⟨h, ?_⟩
      simpa [isDescent, h] using hi
    · simp [isDescent, h] at hi
  · rintro ⟨h, hi⟩
    constructor
    · exact lt_length_of_succ_lt h
    · simpa [isDescent, h] using hi

/-- Membership in `ascentSet`, in terms of adjacent list entries. -/
@[simp] theorem mem_ascentSet {l : List α} {i : ℕ} :
    i ∈ l.ascentSet ↔
      ∃ h : i + 1 < l.length, l[i]'(lt_length_of_succ_lt h) < l[i + 1]'h := by
  change i ∈ (Finset.range l.length).filter (fun j => isAscent l j) ↔ _
  rw [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨_, hi⟩
    by_cases h : i + 1 < l.length
    · refine ⟨h, ?_⟩
      simpa [isAscent, h] using hi
    · simp [isAscent, h] at hi
  · rintro ⟨h, hi⟩
    constructor
    · exact lt_length_of_succ_lt h
    · simpa [isAscent, h] using hi

/-- Every descent position is a position before the last entry. -/
theorem descentSet_subset_range (l : List α) : l.descentSet ⊆ Finset.range (l.length - 1) := by
  intro i hi
  rw [Finset.mem_range]
  exact Nat.le_sub_one_of_lt (mem_descentSet.mp hi).1

/-- The empty word has no descents. -/
@[simp] theorem descentSet_nil : descentSet ([] : List α) = ∅ := by
  simp [descentSet, isDescent]

/-- A one-letter word has no descents. -/
@[simp] theorem descentSet_singleton (a : α) : descentSet [a] = ∅ := by
  rfl

/-- The empty word has no ascents. -/
@[simp] theorem descentCount_nil : descentCount ([] : List α) = 0 := by
  simp [descentCount]

@[simp] theorem descentCount_singleton (a : α) : descentCount [a] = 0 := by
  simp [descentCount]

@[simp] theorem ascentSet_nil : ascentSet ([] : List α) = ∅ := by
  simp [ascentSet, isAscent]

/-- A one-letter word has no ascents. -/
@[simp] theorem ascentSet_singleton (a : α) : ascentSet [a] = ∅ := by
  rfl

/-- Descents of two or more entries, split at the first position. -/
theorem descentSet_cons_cons (a b : α) (l : List α) :
    descentSet (a :: b :: l) =
      (if b < a then ({0} : Finset ℕ) else ∅) ∪
        (descentSet (b :: l)).map ⟨Nat.succ, Nat.succ_injective⟩ := by
  ext i
  cases i with
  | zero => by_cases h : b < a <;> simp [mem_descentSet, h]
  | succ i => by_cases h : b < a <;> simp [mem_descentSet, h]

/-- Ascents of two or more entries, split at the first position. -/
theorem ascentSet_cons_cons (a b : α) (l : List α) :
    ascentSet (a :: b :: l) =
      (if a < b then ({0} : Finset ℕ) else ∅) ∪
        (ascentSet (b :: l)).map ⟨Nat.succ, Nat.succ_injective⟩ := by
  ext i
  cases i with
  | zero => by_cases h : a < b <;> simp [mem_ascentSet, h]
  | succ i => by_cases h : a < b <;> simp [mem_ascentSet, h]

/-- A strictly antitone map exchanges descents and ascents. -/
theorem descentSet_map_strictAnti (l : List α) (f : α → β) (hf : StrictAnti f) :
    (l.map f).descentSet = l.ascentSet := by
  ext i
  constructor
  · intro hi
    obtain ⟨h, hlt⟩ := mem_descentSet.mp hi
    have h' : i + 1 < l.length := by simpa using h
    refine mem_ascentSet.mpr ⟨h', ?_⟩
    rw [List.getElem_map, List.getElem_map] at hlt
    exact hf.lt_iff_gt.mp hlt
  · intro hi
    obtain ⟨h, hlt⟩ := mem_ascentSet.mp hi
    have h' : i + 1 < (l.map f).length := by simpa using h
    refine mem_descentSet.mpr ⟨h', ?_⟩
    rw [List.getElem_map, List.getElem_map]
    exact hf hlt

/-- A strictly antitone map exchanges ascents and descents. -/
theorem ascentSet_map_strictAnti (l : List α) (f : α → β) (hf : StrictAnti f) :
    (l.map f).ascentSet = l.descentSet := by
  ext i
  constructor
  · intro hi
    obtain ⟨h, hlt⟩ := mem_ascentSet.mp hi
    have h' : i + 1 < l.length := by simpa using h
    refine mem_descentSet.mpr ⟨h', ?_⟩
    rw [List.getElem_map, List.getElem_map] at hlt
    exact hf.lt_iff_gt.mp hlt
  · intro hi
    obtain ⟨h, hlt⟩ := mem_descentSet.mp hi
    have h' : i + 1 < (l.map f).length := by simpa using h
    refine mem_ascentSet.mpr ⟨h', ?_⟩
    rw [List.getElem_map, List.getElem_map]
    exact hf hlt

/-- A strictly monotone map preserves descents. -/
theorem descentSet_map_strictMono (l : List α) (f : α → β) (hf : StrictMono f) :
    (l.map f).descentSet = l.descentSet := by
  ext i
  constructor
  · intro hi
    obtain ⟨h, hlt⟩ := mem_descentSet.mp hi
    have h' : i + 1 < l.length := by simpa using h
    refine mem_descentSet.mpr ⟨h', ?_⟩
    rw [List.getElem_map, List.getElem_map] at hlt
    exact hf.lt_iff_lt.mp hlt
  · intro hi
    obtain ⟨h, hlt⟩ := mem_descentSet.mp hi
    have h' : i + 1 < (l.map f).length := by simpa using h
    refine mem_descentSet.mpr ⟨h', ?_⟩
    rw [List.getElem_map, List.getElem_map]
    exact hf hlt

/-- A strictly monotone map preserves ascents. -/
theorem ascentSet_map_strictMono (l : List α) (f : α → β) (hf : StrictMono f) :
    (l.map f).ascentSet = l.ascentSet := by
  ext i
  constructor
  · intro hi
    obtain ⟨h, hlt⟩ := mem_ascentSet.mp hi
    have h' : i + 1 < l.length := by simpa using h
    refine mem_ascentSet.mpr ⟨h', ?_⟩
    rw [List.getElem_map, List.getElem_map] at hlt
    exact hf.lt_iff_lt.mp hlt
  · intro hi
    obtain ⟨h, hlt⟩ := mem_ascentSet.mp hi
    have h' : i + 1 < (l.map f).length := by simpa using h
    refine mem_ascentSet.mpr ⟨h', ?_⟩
    rw [List.getElem_map, List.getElem_map]
    exact hf hlt

/-- For a word with unequal adjacent letters, every adjacent position is an ascent or descent. -/
theorem descentCount_add_ascentCount (l : List α) (hchain : l.IsChain (· ≠ ·)) :
    l.descentCount + l.ascentCount = l.length - 1 := by
  have hdisj : _root_.Disjoint l.descentSet l.ascentSet := by
    rw [Finset.disjoint_left]
    intro i hdes hasc
    obtain ⟨_, hdes⟩ := mem_descentSet.mp hdes
    obtain ⟨_, hasc⟩ := mem_ascentSet.mp hasc
    exact (lt_asymm hdes hasc)
  have hunion : l.descentSet ∪ l.ascentSet = Finset.range (l.length - 1) := by
    ext i
    constructor
    · intro hi
      rcases Finset.mem_union.mp hi with hi | hi
      · rw [Finset.mem_range]
        have hle := Nat.le_sub_one_of_lt (mem_descentSet.mp hi).1
        lia
      · rw [Finset.mem_range]
        have hle := Nat.le_sub_one_of_lt (mem_ascentSet.mp hi).1
        lia
    · intro hi
      simp only [Finset.mem_range] at hi
      rw [Finset.mem_union]
      have hlt : i + 1 < l.length := by lia
      have hne := (List.isChain_iff_getElem.mp hchain) i hlt
      rcases lt_or_gt_of_ne hne with hlt' | hgt'
      · exact Or.inr (mem_ascentSet.mpr ⟨hlt, hlt'⟩)
      · exact Or.inl (mem_descentSet.mpr ⟨hlt, hgt'⟩)
  calc
    l.descentCount + l.ascentCount =
        (l.descentSet ∪ l.ascentSet).card := by
      simp only [descentCount, ascentCount, Finset.card_union_of_disjoint hdisj]
    _ = (Finset.range (l.length - 1)).card := by rw [hunion]
    _ = l.length - 1 := Finset.card_range _

/-- A `Nodup` word has unequal adjacent letters, so its ascent and descent counts add up. -/
theorem descentCount_add_ascentCount_of_nodup (l : List α) (hnodup : l.Nodup) :
    l.descentCount + l.ascentCount = l.length - 1 := by
  apply descentCount_add_ascentCount l
  rw [List.isChain_iff_getElem]
  intro i hi heq
  have hidx := hnodup.getElem_inj_iff.mp heq
  lia

/-- Reversal sends a descent at `i` to an ascent at `length - 2 - i`. -/
theorem descentSet_reverse (l : List α) :
    l.reverse.descentSet = l.ascentSet.image (fun i => l.length - 2 - i) := by
  ext i
  constructor
  · intro hi
    obtain ⟨h, hlt⟩ := mem_descentSet.mp hi
    have h' : i + 1 < l.length := by simpa using h
    let j := l.length - 2 - i
    have hj : j + 1 < l.length := by
      dsimp [j]
      rw [Nat.sub_sub]
      have hile : i + 2 ≤ l.length := by lia
      have hsub : l.length - (i + 2) + (i + 2) = l.length :=
        Nat.sub_add_cancel hile
      have hcalc : l.length - (i + 2) + 1 < l.length := by
        calc
          l.length - (i + 2) + 1 < l.length - (i + 2) + (i + 2) := by lia
          _ = l.length := hsub
      simpa [Nat.add_comm] using hcalc
    have hleft : j = l.length - 1 - (i + 1) := by
      dsimp [j]
      rw [Nat.sub_sub]
      lia
    have hright : j + 1 = l.length - 1 - i := by
      dsimp [j]
      rw [Nat.sub_sub]
      lia
    have hright' : l.length - 1 - (i + 1) + 1 = l.length - 1 - i := by
      simpa [hleft] using hright
    have hlt' := hlt
    simp only [List.getElem_reverse] at hlt'
    refine Finset.mem_image.mpr ⟨j, mem_ascentSet.mpr ⟨hj, ?_⟩, ?_⟩
    · simpa [hleft, hright'] using hlt'
    · dsimp [j]
      lia
  · intro hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨hjlen, hjlt⟩ := mem_ascentSet.mp hj
    have hi : l.length - 2 - j + 1 < l.reverse.length := by
      rw [List.length_reverse]
      have hjle : j + 1 ≤ l.length := by lia
      have hsub : l.length - j + j = l.length := Nat.sub_add_cancel (by lia)
      grind
    have hleft : l.length - 1 - (l.length - 2 - j) = j + 1 := by lia
    have hright : l.length - 1 - (l.length - 2 - j + 1) = j := by lia
    refine mem_descentSet.mpr ⟨hi, ?_⟩
    simp only [List.getElem_reverse]
    simpa [hleft, hright] using hjlt

/-! Small executable regression checks for the fixed convention. -/

example : [3, 1, 4, 1, 5, 9, 2, 6].descentSet = {0, 2, 5} := by decide

example : [3, 1, 4, 1, 5, 9, 2, 6].majorIndex = 10 := by decide

/-! ### Words given as functions on `Fin n` -/

/-- Membership in the descent set of `List.ofFn w`, in terms of `w`. -/
theorem mem_descentSet_ofFn {n : ℕ} {w : Fin n → α} {i : ℕ} :
    i ∈ (List.ofFn w).descentSet ↔
      ∃ h : i + 1 < n, w ⟨i + 1, h⟩ < w ⟨i, Nat.lt_of_succ_lt h⟩ := by
  simp [mem_descentSet, List.getElem_ofFn]

/-- The descent set of `List.ofFn w` is the set of `Fin` positions `i` with
`w i.succ < w i.castSucc`, read as natural numbers. -/
theorem descentSet_ofFn {n : ℕ} (w : Fin (n + 1) → α) :
    (List.ofFn w).descentSet =
      (Finset.univ.filter fun i : Fin n => w i.succ < w i.castSucc).map Fin.valEmbedding := by
  ext i
  rw [mem_descentSet_ofFn]
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
    Fin.valEmbedding_apply]
  constructor
  · rintro ⟨h, hi⟩
    exact ⟨⟨i, Nat.lt_of_add_lt_add_right h⟩, hi, rfl⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨Nat.add_lt_add_right j.isLt 1, hj⟩

/-- Appending a letter adds the last position to the descent set exactly when the letter is
smaller than the previous last letter. -/
theorem descentSet_ofFn_snoc {n : ℕ} (w : Fin (n + 1) → α) (x : α) :
    (List.ofFn (Fin.snoc w x : Fin (n + 2) → α)).descentSet =
      (List.ofFn w).descentSet ∪ if x < w (Fin.last n) then {n} else ∅ := by
  ext i
  rw [Finset.mem_union, mem_descentSet_ofFn, mem_descentSet_ofFn]
  rcases lt_trichotomy i n with hi | rfl | hi
  · have h1 : i + 1 < n + 1 := Nat.add_lt_add_right hi 1
    have h2 : i + 1 < n + 2 := by lia
    have hn : i ≠ n := Nat.ne_of_lt hi
    have e1 : (Fin.snoc w x : Fin (n + 2) → α) ⟨i + 1, h2⟩ = w ⟨i + 1, h1⟩ := by
      simp [Fin.snoc, h1]
    have e2 : (Fin.snoc w x : Fin (n + 2) → α) ⟨i, by lia⟩ = w ⟨i, by lia⟩ := by
      simp [Fin.snoc, show i < n + 1 by lia]
    split_ifs <;> simp [h1, h2, e1, e2, hn]
  · have e2 : (Fin.snoc w x : Fin (i + 2) → α) ⟨i, by lia⟩ = w (Fin.last i) := by
      simp [Fin.snoc, Fin.last]
    have e1 : (Fin.snoc w x : Fin (i + 2) → α) ⟨i + 1, by lia⟩ = x := by
      simp [Fin.snoc]
    split_ifs with h <;> simp [e1, e2, h]
  · have h1 : ¬ i + 1 < n + 2 := by lia
    have h2 : ¬ i + 1 < n + 1 := by lia
    have hn : i ≠ n := by lia
    split_ifs <;> simp [h1, h2, hn]

/-- Appending a letter adds one descent exactly when the letter is smaller than the previous
last letter. -/
theorem descentCount_ofFn_snoc {n : ℕ} (w : Fin (n + 1) → α) (x : α) :
    (List.ofFn (Fin.snoc w x : Fin (n + 2) → α)).descentCount =
      (List.ofFn w).descentCount + if x < w (Fin.last n) then 1 else 0 := by
  unfold descentCount
  rw [descentSet_ofFn_snoc]
  split_ifs with h
  · rw [Finset.card_union_of_disjoint, Finset.card_singleton]
    rw [Finset.disjoint_singleton_right, mem_descentSet_ofFn]
    rintro ⟨h', _⟩
    exact Nat.lt_irrefl _ h'
  · simp

/-- A word has fewer descents than letters. -/
theorem descentCount_le_length_sub_one (l : List α) : l.descentCount ≤ l.length - 1 := by
  simpa [descentCount] using Finset.card_le_card l.descentSet_subset_range

/-- A word of length `n + 1` has at most `n` descents. -/
theorem descentCount_ofFn_le {n : ℕ} (w : Fin (n + 1) → α) :
    (List.ofFn w).descentCount ≤ n := by
  simpa using descentCount_le_length_sub_one (List.ofFn w)

end List
