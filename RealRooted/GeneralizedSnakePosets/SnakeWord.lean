import RealRooted.FolkloreLemma

/-!
# Generalized snake words

This module contains the word-level API for Braun--Jal generalized snake
posets: the two letters, final-letter deletion, prefixes, constant words, and
the computable/predicate forms of the last final-letter change.
-/

namespace RealRooted
namespace GeneralizedSnakePosets

/-- The two letters used after the distinguished initial `epsilon` in a
generalized snake word. -/
inductive SnakeLetter where
  | L
  | R
  deriving DecidableEq, Repr

/-- A generalized snake word, represented by the letters following the
distinguished initial `epsilon`. -/
abbrev SnakeWord := List SnakeLetter

namespace SnakeWord

/-- Delete the final letter of a generalized snake word.  On the empty word
this returns the empty word; theorem statements use an explicit positive-length
hypothesis when this operation models final-letter deletion. -/
def deleteFinal (w : SnakeWord) : SnakeWord :=
  w.take (w.length - 1)

/-- The prefix consisting of the first `k` letters after `epsilon`. -/
def takePrefix (w : SnakeWord) (k : ℕ) : SnakeWord :=
  w.take k

/-- A word is constant if all of its letters agree. -/
def IsConstant (w : SnakeWord) : Prop :=
  ∀ a ∈ w, ∀ b ∈ w, a = b

/-- The zero-based positions whose letter differs from the final letter. -/
def changeIndices (w : SnakeWord) : List ℕ :=
  (List.range w.length).filter fun k =>
    decide (w[k]? ≠ w[w.length - 1]?)

/-- The last zero-based position whose letter differs from the final letter,
if such a position exists. -/
def lastChangeIndex? (w : SnakeWord) : Option ℕ :=
  (changeIndices w).getLast?

/-- Predicate form of the last-change index, convenient for recurrence
statements that should not depend on a particular computational encoding. -/
def IsLastChangeIndex (w : SnakeWord) (k : ℕ) : Prop :=
  k ∈ changeIndices w ∧ ∀ j ∈ changeIndices w, j ≤ k

/-- Taking any prefix of the empty snake word gives the empty word. -/
@[simp] theorem takePrefix_nil (k : ℕ) :
    takePrefix ([] : SnakeWord) k = [] := by
  simp [takePrefix]

/-- The zero-length prefix of a snake word is empty. -/
@[simp] theorem takePrefix_zero (w : SnakeWord) :
    w.takePrefix 0 = [] := by
  simp [takePrefix]

/-- The length of the `k`-letter prefix is at most `k`. -/
theorem length_takePrefix_le (w : SnakeWord) (k : ℕ) :
    (w.takePrefix k).length ≤ k := by
  simp [takePrefix]

/-- A prefix of a snake word is no longer than the original word. -/
theorem length_takePrefix_le_length (w : SnakeWord) (k : ℕ) :
    (w.takePrefix k).length ≤ w.length := by
  simp [takePrefix]

/-- A prefix equals the whole word exactly when the requested length is large
enough. -/
theorem takePrefix_eq_self_iff (w : SnakeWord) {k : ℕ} :
    w.takePrefix k = w ↔ w.length ≤ k := by
  simp [takePrefix]

/-- A prefix of length at least the word length is the whole word. -/
theorem takePrefix_eq_self_of_length_le {w : SnakeWord} {k : ℕ}
    (hk : w.length ≤ k) :
    w.takePrefix k = w := by
  exact (takePrefix_eq_self_iff w).mpr hk

/-- Final-letter deletion is the prefix of length `w.length - 1`. -/
theorem deleteFinal_eq_takePrefix (w : SnakeWord) :
    w.deleteFinal = w.takePrefix (w.length - 1) :=
  rfl

/-- Deleting the final letter of the empty word gives the empty word. -/
@[simp] theorem deleteFinal_nil :
    deleteFinal ([] : SnakeWord) = [] := by
  simp [deleteFinal]

/-- Deleting the final letter of a one-letter word gives the empty word. -/
@[simp] theorem deleteFinal_singleton (a : SnakeLetter) :
    deleteFinal [a] = [] := by
  simp [deleteFinal]

/-- The length after final-letter deletion is `w.length - 1`. -/
theorem length_deleteFinal (w : SnakeWord) :
    w.deleteFinal.length = w.length - 1 := by
  rw [deleteFinal, List.length_take]
  exact min_eq_left (Nat.sub_le _ _)

/-- Deleting the final letter does not increase the length. -/
theorem length_deleteFinal_le (w : SnakeWord) :
    w.deleteFinal.length ≤ w.length := by
  rw [length_deleteFinal]
  exact Nat.sub_le _ _

/-- Membership in `changeIndices` is exactly the bounded final-letter-change
condition. -/
theorem mem_changeIndices {w : SnakeWord} {k : ℕ} :
    k ∈ w.changeIndices ↔ k < w.length ∧ w[k]? ≠ w[w.length - 1]? := by
  simp [changeIndices]

/-- The computable change-index list is sorted in increasing order. -/
theorem sortedLE_changeIndices (w : SnakeWord) :
    w.changeIndices.SortedLE := by
  exact (List.Pairwise.filter
    (fun k => decide (w[k]? ≠ w[w.length - 1]?))
    (List.SortedLE.pairwise
      (List.SortedLT.sortedLE (List.sortedLT_range w.length)))).sortedLE

/-- Any actual final-letter change certifies that the word is nonconstant. -/
theorem not_isConstant_of_mem_changeIndices {w : SnakeWord} {k : ℕ}
    (hk : k ∈ w.changeIndices) :
    ¬ w.IsConstant := by
  intro hconst
  rcases SnakeWord.mem_changeIndices.mp hk with ⟨hklt, hne⟩
  have hlen_ne : w.length ≠ 0 :=
    Nat.ne_of_gt (Nat.lt_of_le_of_lt (Nat.zero_le k) hklt)
  have hlast_lt : w.length - 1 < w.length := Nat.sub_one_lt hlen_ne
  have hget : w[k]? = some w[k] := List.getElem?_eq_getElem hklt
  have hlast : w[w.length - 1]? = some w[w.length - 1] :=
    List.getElem?_eq_getElem hlast_lt
  have hmem_k : w[k] ∈ w := List.getElem_mem _
  have hmem_last : w[w.length - 1] ∈ w := List.getElem_mem _
  have heq : w[k] = w[w.length - 1] :=
    hconst w[k] hmem_k w[w.length - 1] hmem_last
  exact hne (by simp [hget, hlast, heq])

/-- Constant words have no final-letter change indices. -/
theorem changeIndices_eq_nil_of_isConstant {w : SnakeWord}
    (h : w.IsConstant) :
    w.changeIndices = [] := by
  rw [List.eq_nil_iff_forall_not_mem]
  intro k hk
  exact not_isConstant_of_mem_changeIndices hk h

/-- If there are no final-letter change indices, the word is constant. -/
theorem isConstant_of_changeIndices_eq_nil {w : SnakeWord}
    (h : w.changeIndices = []) :
    w.IsConstant := by
  intro a ha b hb
  rcases List.mem_iff_getElem?.mp ha with ⟨i, hi⟩
  rcases List.mem_iff_getElem?.mp hb with ⟨j, hj⟩
  rcases List.getElem?_eq_some_iff.mp hi with ⟨hilt, _hia⟩
  rcases List.getElem?_eq_some_iff.mp hj with ⟨hjlt, _hjb⟩
  have hi_final : w[i]? = w[w.length - 1]? := by
    by_contra hne
    have hmem : i ∈ w.changeIndices :=
      SnakeWord.mem_changeIndices.mpr ⟨hilt, hne⟩
    rw [h] at hmem
    simp at hmem
  have hj_final : w[j]? = w[w.length - 1]? := by
    by_contra hne
    have hmem : j ∈ w.changeIndices :=
      SnakeWord.mem_changeIndices.mpr ⟨hjlt, hne⟩
    rw [h] at hmem
    simp at hmem
  apply Option.some.inj
  calc
    some a = w[i]? := hi.symm
    _ = w[w.length - 1]? := hi_final
    _ = w[j]? := hj_final.symm
    _ = some b := hj

/-- A word is constant exactly when it has no final-letter change indices. -/
theorem isConstant_iff_changeIndices_eq_nil (w : SnakeWord) :
    w.IsConstant ↔ w.changeIndices = [] :=
  ⟨changeIndices_eq_nil_of_isConstant, isConstant_of_changeIndices_eq_nil⟩

/-- A word has some final-letter change index exactly when it is nonconstant. -/
theorem changeIndices_ne_nil_iff_not_isConstant (w : SnakeWord) :
    w.changeIndices ≠ [] ↔ ¬ w.IsConstant := by
  rw [isConstant_iff_changeIndices_eq_nil]

/-- A nonconstant word has at least one final-letter change index. -/
theorem exists_mem_changeIndices_of_not_isConstant {w : SnakeWord}
    (h : ¬ w.IsConstant) :
    ∃ k, k ∈ w.changeIndices :=
  List.exists_mem_of_ne_nil w.changeIndices
    ((changeIndices_ne_nil_iff_not_isConstant w).mpr h)

/-- The computable last-change index is absent exactly for constant words. -/
theorem lastChangeIndex?_eq_none_iff_isConstant (w : SnakeWord) :
    w.lastChangeIndex? = none ↔ w.IsConstant := by
  rw [lastChangeIndex?, List.getLast?_eq_none_iff]
  exact (isConstant_iff_changeIndices_eq_nil w).symm

/-- The computable last-change index is present exactly for nonconstant
words. -/
theorem lastChangeIndex?_isSome_iff_not_isConstant (w : SnakeWord) :
    w.lastChangeIndex?.isSome ↔ ¬ w.IsConstant := by
  rw [Option.isSome_iff_ne_none, ne_eq, lastChangeIndex?_eq_none_iff_isConstant]

/-- Existence form of `lastChangeIndex?_isSome_iff_not_isConstant`. -/
theorem exists_lastChangeIndex?_eq_some_iff_not_isConstant (w : SnakeWord) :
    (∃ k, w.lastChangeIndex? = some k) ↔ ¬ w.IsConstant := by
  rw [← Option.isSome_iff_exists, lastChangeIndex?_isSome_iff_not_isConstant]

/-- A nonconstant word has a computable last-change index. -/
theorem exists_lastChangeIndex?_eq_some_of_not_isConstant {w : SnakeWord}
    (h : ¬ w.IsConstant) :
    ∃ k, w.lastChangeIndex? = some k :=
  (exists_lastChangeIndex?_eq_some_iff_not_isConstant w).mpr h

/-- A computed last-change index is a member of `changeIndices`. -/
theorem mem_changeIndices_of_lastChangeIndex?_eq_some {w : SnakeWord} {k : ℕ}
    (h : w.lastChangeIndex? = some k) :
    k ∈ w.changeIndices := by
  rw [lastChangeIndex?, List.getLast?_eq_some_iff] at h
  rcases h with ⟨ys, hys⟩
  rw [hys]
  simp

/-- A word with a computed last-change index is nonconstant. -/
theorem not_isConstant_of_lastChangeIndex?_eq_some {w : SnakeWord} {k : ℕ}
    (h : w.lastChangeIndex? = some k) :
    ¬ w.IsConstant :=
  not_isConstant_of_mem_changeIndices
    (mem_changeIndices_of_lastChangeIndex?_eq_some h)

/-- A computed last-change index satisfies the predicate-form interface. -/
theorem isLastChangeIndex_of_lastChangeIndex?_eq_some {w : SnakeWord} {k : ℕ}
    (h : w.lastChangeIndex? = some k) :
    w.IsLastChangeIndex k := by
  let l := w.changeIndices
  have hlast : l.getLast? = some k := by
    simpa [l, lastChangeIndex?] using h
  have hne : l ≠ [] := by
    intro hnil
    rw [hnil] at hlast
    simp at hlast
  have hlast_eq : l.getLast hne = k := by
    have hget := List.getLast?_eq_getLast_of_ne_nil (l := l) hne
    rw [hlast] at hget
    exact Option.some.inj hget.symm
  refine ⟨mem_changeIndices_of_lastChangeIndex?_eq_some h, ?_⟩
  intro j hj
  have hpair : l.Pairwise (fun a b => a ≤ b) :=
    List.SortedLE.pairwise (by simpa [l] using sortedLE_changeIndices w)
  have hjle : j ≤ l.getLast hne := hpair.rel_getLast (by simpa [l] using hj)
  simpa [hlast_eq] using hjle

/-- A predicate-form last-change index agrees with the computable one. -/
theorem lastChangeIndex?_eq_some_of_isLastChangeIndex {w : SnakeWord} {k : ℕ}
    (h : w.IsLastChangeIndex k) :
    w.lastChangeIndex? = some k := by
  let l := w.changeIndices
  have hne : l ≠ [] := by
    intro hnil
    have hk : k ∈ ([] : List ℕ) := by
      simpa [l, hnil] using h.1
    cases hk
  have hpair : l.Pairwise (fun a b => a ≤ b) :=
    List.SortedLE.pairwise (by simpa [l] using sortedLE_changeIndices w)
  have hk_le_last : k ≤ l.getLast hne :=
    hpair.rel_getLast (by simpa [l] using h.1)
  have hlast_mem : l.getLast hne ∈ w.changeIndices := by
    simp [l, List.getLast_mem hne]
  have hlast_le_k : l.getLast hne ≤ k :=
    h.2 (l.getLast hne) hlast_mem
  have hlast_eq : l.getLast hne = k := le_antisymm hlast_le_k hk_le_last
  have hget := List.getLast?_eq_getLast_of_ne_nil (l := l) hne
  rw [lastChangeIndex?]
  simpa [l, hlast_eq] using hget

/-- The computable and predicate forms of last-change index agree. -/
theorem lastChangeIndex?_eq_some_iff_isLastChangeIndex (w : SnakeWord) (k : ℕ) :
    w.lastChangeIndex? = some k ↔ w.IsLastChangeIndex k :=
  ⟨isLastChangeIndex_of_lastChangeIndex?_eq_some,
    lastChangeIndex?_eq_some_of_isLastChangeIndex⟩

/-- A nonconstant word has a predicate-form last-change index. -/
theorem exists_isLastChangeIndex_of_not_isConstant {w : SnakeWord}
    (h : ¬ w.IsConstant) :
    ∃ k, w.IsLastChangeIndex k := by
  rcases exists_lastChangeIndex?_eq_some_of_not_isConstant h with ⟨k, hk⟩
  exact ⟨k, isLastChangeIndex_of_lastChangeIndex?_eq_some hk⟩

/-- The last-change index is one of the change indices. -/
theorem IsLastChangeIndex.mem_changeIndices {w : SnakeWord} {k : ℕ}
    (h : w.IsLastChangeIndex k) :
    k ∈ w.changeIndices :=
  h.1

/-- A word with a last-change index is nonconstant. -/
theorem IsLastChangeIndex.not_isConstant {w : SnakeWord} {k : ℕ}
    (h : w.IsLastChangeIndex k) :
    ¬ w.IsConstant :=
  not_isConstant_of_mem_changeIndices h.1

/-- A last-change index is a valid index of the word. -/
theorem IsLastChangeIndex.index_lt_length {w : SnakeWord} {k : ℕ}
    (h : w.IsLastChangeIndex k) :
    k < w.length :=
  (SnakeWord.mem_changeIndices.mp h.1).1

/-- At a last-change index, the letter differs from the final letter. -/
theorem IsLastChangeIndex.letter_ne_final {w : SnakeWord} {k : ℕ}
    (h : w.IsLastChangeIndex k) :
    w[k]? ≠ w[w.length - 1]? :=
  (SnakeWord.mem_changeIndices.mp h.1).2

/-- Every change index lies before or at the last-change index. -/
theorem IsLastChangeIndex.all_changes_le {w : SnakeWord} {k : ℕ}
    (h : w.IsLastChangeIndex k) :
    ∀ j ∈ w.changeIndices, j ≤ k :=
  h.2

/-- Every index after the last-change index has the final letter. -/
theorem IsLastChangeIndex.getElem?_eq_final_of_lt
    {w : SnakeWord} {k j : ℕ} (h : w.IsLastChangeIndex k)
    (hkj : k < j) (hj : j < w.length) :
    w[j]? = w[w.length - 1]? := by
  by_contra hne
  have hjchange : j ∈ w.changeIndices :=
    SnakeWord.mem_changeIndices.mpr ⟨hj, hne⟩
  have hjle : j ≤ k := h.all_changes_le j hjchange
  exact (not_lt_of_ge hjle) hkj

/-- `getD` form of `IsLastChangeIndex.getElem?_eq_final_of_lt`. -/
theorem IsLastChangeIndex.getD_eq_final_of_lt
    {w : SnakeWord} {k j : ℕ} (h : w.IsLastChangeIndex k)
    (hkj : k < j) (hj : j < w.length) (default : SnakeLetter) :
    w.getD j default = w.getD (w.length - 1) default := by
  simpa [List.getD_eq_getElem?_getD] using
    congrArg (fun letter? => letter?.getD default)
      (h.getElem?_eq_final_of_lt hkj hj)

/-- The prefix ending at the last-change index has length `k + 1`. -/
theorem IsLastChangeIndex.takePrefix_succ_length {w : SnakeWord} {k : ℕ}
    (h : w.IsLastChangeIndex k) :
    (w.takePrefix (k + 1)).length = k + 1 := by
  have hk : k + 1 ≤ w.length :=
    Nat.succ_le_iff.mpr (SnakeWord.IsLastChangeIndex.index_lt_length h)
  simp [takePrefix, List.length_take, min_eq_left hk]

/-- The prefix before the last-change index has length `k`. -/
theorem IsLastChangeIndex.takePrefix_length {w : SnakeWord} {k : ℕ}
    (h : w.IsLastChangeIndex k) :
    (w.takePrefix k).length = k := by
  have hk : k ≤ w.length :=
    Nat.le_of_lt (SnakeWord.IsLastChangeIndex.index_lt_length h)
  simp [takePrefix, List.length_take, min_eq_left hk]

end SnakeWord

end GeneralizedSnakePosets
end RealRooted
