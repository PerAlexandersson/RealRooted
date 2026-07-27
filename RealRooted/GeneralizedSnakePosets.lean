import RealRooted.Basic

/-!
# Generalized snake poset statement interfaces

This file records the first Lean-facing interface for Braun--Jal,
*Order polytopes of generalized snake posets are h^*-real-rooted*,
arXiv:2607.00922v1.

The immediate target is Theorem 4.1 of the paper: if `w` is a generalized
snake word of length at least one and `w'` is obtained by deleting the final
letter, then the non-nesting rook polynomial `M_{epsilon w}` is real-rooted
and `M_{epsilon w'}` interlaces `M_{epsilon w}`.

The board, poset, and order-polytope encodings are intentionally left as
interfaces in this first module.  The recurrence/Narayana proof route should
later refine these statement interfaces rather than replacing them with a
one-off coefficient argument.
-/

open Polynomial

noncomputable section

namespace RealRooted
namespace GeneralizedSnakePosets

universe u

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

/-! ## Board and rook-polynomial interfaces -/

/-- A finite skew board, represented only by its finite set of cells.

This intentionally avoids committing to a Ferrers or squarecase coordinate
system.  Concrete squarecase encodings can later prove that their cell sets
agree with this finite model. -/
structure FiniteSkewBoard where
  cells : Finset (ℕ × ℕ)
  deriving DecidableEq

namespace FiniteSkewBoard

/-- The empty finite skew board. -/
def empty : FiniteSkewBoard :=
  ⟨∅⟩

/-- A rook placement is non-nesting if all cells lie in the board, no two
rooks share a row, and columns strictly decrease as rows increase. -/
def IsNonNestingPlacement (B : FiniteSkewBoard) (P : Finset (ℕ × ℕ)) : Prop :=
  P ⊆ B.cells ∧
    (∀ a ∈ P, ∀ b ∈ P, a ≠ b → a.1 ≠ b.1) ∧
    (∀ a ∈ P, ∀ b ∈ P, a.1 < b.1 → b.2 < a.2)

/-- The non-nesting rook polynomial of a finite skew board. -/
def rookPolynomial (B : FiniteSkewBoard) : ℝ[X] := by
  classical
  exact (B.cells.powerset.filter (fun P => B.IsNonNestingPlacement P)).sum
    (fun P => X ^ P.card)

/-- The empty placement is non-nesting on every finite skew board. -/
@[simp] theorem isNonNestingPlacement_empty (B : FiniteSkewBoard) :
    B.IsNonNestingPlacement ∅ := by
  simp [IsNonNestingPlacement]

/-- A singleton cell is a non-nesting placement when it lies in the board. -/
private lemma isNonNestingPlacement_singleton {B : FiniteSkewBoard} {a : ℕ × ℕ}
    (ha : a ∈ B.cells) :
    B.IsNonNestingPlacement ({a} : Finset (ℕ × ℕ)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    rw [Finset.mem_singleton] at hx
    rw [hx]
    exact ha
  · intro x hx y hy hne
    rw [Finset.mem_singleton] at hx hy
    rw [hx, hy] at hne
    exact (hne rfl).elim
  · intro x hx y hy hlt
    rw [Finset.mem_singleton] at hx hy
    rw [hx, hy] at hlt
    exact (Nat.lt_irrefl _ hlt).elim

/-- A two-cell set is a non-nesting placement when the two cells lie in the
board, are in different rows, and satisfy the decreasing-column condition. -/
private lemma isNonNestingPlacement_pair {B : FiniteSkewBoard} (a b : ℕ × ℕ)
    (ha : a ∈ B.cells) (hb : b ∈ B.cells) (hrow : a.1 ≠ b.1)
    (hcol_ab : a.1 < b.1 → b.2 < a.2)
    (hcol_ba : b.1 < a.1 → a.2 < b.2) :
    B.IsNonNestingPlacement ({a, b} : Finset (ℕ × ℕ)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact ha
    · exact hb
  · intro x hx y hy hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl
    · rcases hy with rfl | rfl
      · exact (hne rfl).elim
      · exact hrow
    · rcases hy with rfl | rfl
      · exact hrow.symm
      · exact (hne rfl).elim
  · intro x hx y hy hlt
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl
    · rcases hy with rfl | rfl
      · exact (Nat.lt_irrefl _ hlt).elim
      · exact hcol_ab hlt
    · rcases hy with rfl | rfl
      · exact hcol_ba hlt
      · exact (Nat.lt_irrefl _ hlt).elim

private def finsetAllBool {α : Type*} (s : Finset α) (p : α → Bool) : Bool :=
  s.fold (fun a b => a && b) true p

private lemma finsetAllBool_iff {α : Type*} (s : Finset α) (p : α → Bool) :
    finsetAllBool s p ↔ ∀ a ∈ s, p a := by
  classical
  induction s using Finset.induction with
  | empty => simp [finsetAllBool]
  | insert a s ha ih =>
      rw [finsetAllBool, Finset.fold_insert ha, Bool.and_eq_true_iff]
      constructor
      · rintro ⟨hpa, hall⟩ b hb
        rw [Finset.mem_insert] at hb
        rcases hb with rfl | hb
        · exact hpa
        · exact ih.mp hall b hb
      · intro hall
        exact ⟨hall a (Finset.mem_insert_self a s), ih.mpr fun b hb =>
          hall b (Finset.mem_insert_of_mem hb)⟩

private def isNonNestingPlacementBool (B : FiniteSkewBoard)
    (P : Finset (ℕ × ℕ)) : Bool :=
  finsetAllBool P (fun a => decide (a ∈ B.cells)) &&
    finsetAllBool P (fun a =>
      finsetAllBool P (fun b =>
        decide ((a.1 = b.1 → a.2 ≠ b.2) → a.1 ≠ b.1))) &&
    finsetAllBool P (fun a =>
      finsetAllBool P (fun b => decide (a.1 < b.1 → b.2 < a.2)))

private lemma isNonNestingPlacementBool_iff (B : FiniteSkewBoard)
    (P : Finset (ℕ × ℕ)) :
    isNonNestingPlacementBool B P ↔ B.IsNonNestingPlacement P := by
  simp only [isNonNestingPlacementBool, ne_eq, decide_implies, decide_not,
    dite_eq_ite, Bool.if_true_right, Bool.not_or, Bool.not_not,
    Bool.and_eq_true, finsetAllBool_iff, decide_eq_true_eq, Prod.forall,
    Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
    decide_eq_false_iff_not, not_lt, IsNonNestingPlacement,
    Finset.subset_iff, Prod.mk.injEq, not_and]
  constructor
  · rintro ⟨⟨hsub, hrow⟩, hnest⟩
    refine ⟨hsub, ?_, ?_⟩
    · intro a b hab c d hcd hne
      rcases hrow a b hab c d hcd with hEq | hrow_ne
      · exact (hne hEq.1 hEq.2).elim
      · exact hrow_ne
    · intro a b hab c d hcd hlt
      rcases hnest a b hab c d hcd with hle | hcol
      · exact (False.elim ((not_lt_of_ge hle) hlt))
      · exact hcol
  · rintro ⟨hsub, hrow, hnest⟩
    refine ⟨⟨hsub, ?_⟩, ?_⟩
    · intro a b hab c d hcd
      by_cases ha : a = c
      · by_cases hb : b = d
        · exact Or.inl ⟨ha, hb⟩
        · exact Or.inr (hrow a b hab c d hcd (by intro _; exact hb))
      · exact Or.inr ha
    · intro a b hab c d hcd
      by_cases hlt : a < c
      · exact Or.inr (hnest a b hab c d hcd hlt)
      · exact Or.inl (le_of_not_gt hlt)

/-- Powers of `X` have nonnegative coefficients. -/
private lemma xPow_hasNonnegCoeffs (n : ℕ) :
    HasNonnegCoeffs ((X : ℝ[X]) ^ n) := by
  intro k
  by_cases hk : k = n
  · subst k
    simp
  · simp [coeff_X_pow, hk]

/-- The empty board has rook polynomial `1`. -/
@[simp] theorem rookPolynomial_empty :
    empty.rookPolynomial = 1 := by
  classical
  have hpowerset :
      empty.cells.powerset = ({∅} : Finset (Finset (ℕ × ℕ))) := by
    simp [empty]
  have hfilter :
      empty.cells.powerset.filter (fun P => empty.IsNonNestingPlacement P) =
        ({∅} : Finset (Finset (ℕ × ℕ))) := by
    rw [hpowerset]
    apply Finset.filter_true_of_mem
    intro P hP
    have hPempty : P = ∅ := by
      simpa using hP
    subst P
    simp [IsNonNestingPlacement, empty]
  simp [rookPolynomial, hfilter]

/-- Finite skew board rook polynomials have nonnegative coefficients. -/
theorem rookPolynomial_hasNonnegCoeffs (B : FiniteSkewBoard) :
    HasNonnegCoeffs B.rookPolynomial := by
  classical
  unfold rookPolynomial
  intro k
  rw [Polynomial.finsetSum_coeff]
  exact Finset.sum_nonneg fun (P : Finset (ℕ × ℕ)) _ =>
    xPow_hasNonnegCoeffs P.card k

/-- The empty placement gives the constant coefficient of a finite skew board
rook polynomial. -/
@[simp] theorem rookPolynomial_coeff_zero (B : FiniteSkewBoard) :
    B.rookPolynomial.coeff 0 = 1 := by
  classical
  rw [rookPolynomial, Polynomial.finsetSum_coeff, Finset.sum_eq_single ∅]
  · simp
  · intro P _hP hne
    have hP_nonzero : P.card ≠ 0 := by
      rwa [Finset.card_ne_zero, Finset.nonempty_iff_ne_empty]
    have hzero : ¬ 0 = P.card := fun h => hP_nonzero h.symm
    simp [Polynomial.coeff_X_pow, hzero]
  · intro hnot
    simp at hnot

/-- Finite skew board rook polynomials are nonzero. -/
theorem rookPolynomial_ne_zero (B : FiniteSkewBoard) :
    B.rookPolynomial ≠ 0 := by
  intro hzero
  have hcoeff := congrArg (fun p : ℝ[X] => p.coeff 0) hzero
  rw [rookPolynomial_coeff_zero] at hcoeff
  norm_num at hcoeff

/-! ### Skew Ferrers boards -/

/-- The skew Ferrers board `lam / mu` in zero-based row coordinates.

The paper uses cells `(i,j)` with `1 ≤ i` and `mu_i < j ≤ lam_i`; this encoding
uses rows indexed by `0, ..., lam.length - 1`, keeps the same column inequality,
and reads missing `mu` entries as zero. -/
def skewFerrers (lam mu : List ℕ) : FiniteSkewBoard where
  cells :=
    (Finset.range lam.length).biUnion fun row =>
      (Finset.Ioc (mu.getD row 0) (lam.getD row 0)).image fun col => (row, col)

/-- The straight Ferrers board attached to a finite row-length list. -/
def ferrers (lam : List ℕ) : FiniteSkewBoard :=
  skewFerrers lam []

/-- The non-nesting rook polynomial of a zero-based skew Ferrers board. -/
def skewFerrersRookPolynomial (lam mu : List ℕ) : ℝ[X] :=
  (skewFerrers lam mu).rookPolynomial

/-- The non-nesting rook polynomial of a straight Ferrers board. -/
def ferrersRookPolynomial (lam : List ℕ) : ℝ[X] :=
  (ferrers lam).rookPolynomial

/-- Remove one column from every row-length entry. -/
def partitionSubOne (lam : List ℕ) : List ℕ :=
  lam.map fun n => n - 1

/-- Keep the first `i` row-length entries. -/
def partitionPrefix (lam : List ℕ) (i : ℕ) : List ℕ :=
  lam.take i

/-- Skew Ferrers rook polynomials have nonnegative coefficients. -/
theorem skewFerrersRookPolynomial_hasNonnegCoeffs (lam mu : List ℕ) :
    HasNonnegCoeffs (skewFerrersRookPolynomial lam mu) :=
  rookPolynomial_hasNonnegCoeffs _

/-- Ferrers rook polynomials have nonnegative coefficients. -/
theorem ferrersRookPolynomial_hasNonnegCoeffs (lam : List ℕ) :
    HasNonnegCoeffs (ferrersRookPolynomial lam) :=
  rookPolynomial_hasNonnegCoeffs _

/-- Skew Ferrers rook polynomials have constant coefficient one. -/
@[simp] theorem skewFerrersRookPolynomial_coeff_zero (lam mu : List ℕ) :
    (skewFerrersRookPolynomial lam mu).coeff 0 = 1 :=
  rookPolynomial_coeff_zero _

/-- Ferrers rook polynomials have constant coefficient one. -/
@[simp] theorem ferrersRookPolynomial_coeff_zero (lam : List ℕ) :
    (ferrersRookPolynomial lam).coeff 0 = 1 :=
  rookPolynomial_coeff_zero _

/-- Skew Ferrers rook polynomials are nonzero. -/
theorem skewFerrersRookPolynomial_ne_zero (lam mu : List ℕ) :
    skewFerrersRookPolynomial lam mu ≠ 0 :=
  rookPolynomial_ne_zero _

/-- Ferrers rook polynomials are nonzero. -/
theorem ferrersRookPolynomial_ne_zero (lam : List ℕ) :
    ferrersRookPolynomial lam ≠ 0 :=
  rookPolynomial_ne_zero _

/-- Braun--Jal Proposition 3.2, stated for any straight Ferrers rook-polynomial
family indexed by row lengths. -/
def FerrersFirstColumnDeletionStatement (M : List ℕ → ℝ[X]) : Prop :=
  ∀ lam : List ℕ,
    M lam =
      M (partitionSubOne lam) +
        X * ((List.range lam.length).map fun i =>
          M (partitionPrefix (partitionSubOne lam) i)).sum

/-- Braun--Jal Proposition 3.2 as the target statement for the concrete finite
Ferrers-board rook-polynomial model. -/
def ferrersFirstColumnDeletionStatement : Prop :=
  FerrersFirstColumnDeletionStatement ferrersRookPolynomial

/-- A finite list sum of nonnegative-coefficient polynomials has nonnegative
coefficients. -/
private lemma listSum_hasNonnegCoeffs {ps : List ℝ[X]}
    (hps : ∀ p ∈ ps, HasNonnegCoeffs p) :
    HasNonnegCoeffs ps.sum := by
  induction ps with
  | nil =>
      simp [HasNonnegCoeffs]
  | cons p ps ih =>
      intro k
      have hp : HasNonnegCoeffs p := hps p (by simp)
      have htail : ∀ q ∈ ps, HasNonnegCoeffs q := by
        intro q hq
        exact hps q (by simp [hq])
      simpa using add_nonneg (hp k) (ih htail k)

/-- The truncated staircase shape `mu_{n,i}` used in Braun--Jal Section 3,
modeled as the first `i` rows of the staircase with row lengths
`n, n - 1, ...`. -/
def truncatedStaircase (n i : ℕ) : FiniteSkewBoard where
  cells :=
    (Finset.range i).biUnion fun row =>
      (Finset.range (n - row)).image fun col => (row, col)

/-- The non-nesting rook polynomial of the truncated staircase `mu_{n,i}`. -/
def truncatedStaircaseRookPolynomial (n i : ℕ) : ℝ[X] :=
  (truncatedStaircase n i).rookPolynomial

/-- The truncated staircase with zero rows is the empty board. -/
@[simp] theorem truncatedStaircase_zero_rows (n : ℕ) :
    truncatedStaircase n 0 = empty := by
  simp [truncatedStaircase, empty]

/-- Truncated-staircase rook polynomials have constant coefficient one. -/
@[simp] theorem truncatedStaircaseRookPolynomial_coeff_zero (n i : ℕ) :
    (truncatedStaircaseRookPolynomial n i).coeff 0 = 1 :=
  rookPolynomial_coeff_zero _

/-- The zero-row truncated-staircase rook polynomial is one. -/
@[simp] theorem truncatedStaircaseRookPolynomial_zero_rows (n : ℕ) :
    truncatedStaircaseRookPolynomial n 0 = 1 := by
  simp [truncatedStaircaseRookPolynomial]

/-- The one-row truncated staircase with two cells has rook polynomial
`1 + 2X`. -/
@[simp] theorem truncatedStaircaseRookPolynomial_two_one :
    truncatedStaircaseRookPolynomial 2 1 = 1 + C (2 : ℝ) * X := by
  classical
  have hcells :
      (truncatedStaircase 2 1).cells =
        ({(0, 0), (0, 1)} : Finset (ℕ × ℕ)) := by
    ext x
    constructor
    · intro hx
      simp only [truncatedStaircase, Finset.mem_biUnion, Finset.mem_range,
        Finset.mem_image] at hx
      rcases hx with ⟨row, hrow, col, hcol, hx⟩
      interval_cases row
      interval_cases col <;> simp_all
    · intro hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · simp only [truncatedStaircase, Finset.mem_biUnion, Finset.mem_range,
          Finset.mem_image]
        exact ⟨0, by norm_num, 0, by norm_num, rfl⟩
      · simp only [truncatedStaircase, Finset.mem_biUnion, Finset.mem_range,
          Finset.mem_image]
        exact ⟨0, by norm_num, 1, by norm_num, rfl⟩
  have hplacements :
      (truncatedStaircase 2 1).cells.powerset.filter
        (fun P => (truncatedStaircase 2 1).IsNonNestingPlacement P) =
        ({∅, {(0, 0)}, {(0, 1)}} : Finset (Finset (ℕ × ℕ))) := by
    rw [hcells]
    ext P
    simp only [IsNonNestingPlacement, hcells, Finset.mem_filter, Finset.mem_powerset,
      Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro h
      by_cases h00 : (0, 0) ∈ P
      · by_cases h01 : (0, 1) ∈ P
        · exfalso
          have hne : (0, 0) ≠ (0, 1) := by
            norm_num
          have hrow := h.2.2.1 (0, 0) h00 (0, 1) h01 hne
          exact hrow rfl
        · right
          left
          ext x
          constructor
          · intro hx
            have hxsub := h.1 hx
            simp only [Finset.mem_insert, Finset.mem_singleton] at hxsub
            rcases hxsub with rfl | rfl
            · simp
            · exact (h01 hx).elim
          · intro hx
            rw [Finset.mem_singleton] at hx
            rw [hx]
            exact h00
      · by_cases h01 : (0, 1) ∈ P
        · right
          right
          ext x
          constructor
          · intro hx
            have hxsub := h.1 hx
            simp only [Finset.mem_insert, Finset.mem_singleton] at hxsub
            rcases hxsub with rfl | rfl
            · exact (h00 hx).elim
            · simp
          · intro hx
            rw [Finset.mem_singleton] at hx
            rw [hx]
            exact h01
        · left
          ext x
          constructor
          · intro hx
            have hxsub := h.1 hx
            simp only [Finset.mem_insert, Finset.mem_singleton] at hxsub
            rcases hxsub with rfl | rfl
            · exact (h00 hx).elim
            · exact (h01 hx).elim
          · intro hx
            simp at hx
    · rintro (rfl | rfl | rfl) <;> simp
  rw [truncatedStaircaseRookPolynomial, rookPolynomial, hplacements]
  norm_num
  have hC2 : (C (2 : ℝ) : ℝ[X]) = 2 := Polynomial.C_eq_natCast (R := ℝ) 2
  rw [hC2]
  ring_nf

/-- The one-row truncated staircase with three cells has rook polynomial
`1 + 3X`. -/
@[simp] theorem truncatedStaircaseRookPolynomial_three_one :
    truncatedStaircaseRookPolynomial 3 1 = 1 + C (3 : ℝ) * X := by
  classical
  have hcells :
      (truncatedStaircase 3 1).cells =
        ({(0, 0), (0, 1), (0, 2)} : Finset (ℕ × ℕ)) := by
    decide
  have hplacements :
      (truncatedStaircase 3 1).cells.powerset.filter
        (fun P => (truncatedStaircase 3 1).IsNonNestingPlacement P) =
        ({∅, {(0, 0)}, {(0, 1)}, {(0, 2)}} :
          Finset (Finset (ℕ × ℕ))) := by
    rw [hcells]
    ext P
    constructor
    · intro hmem
      rw [Finset.mem_filter] at hmem
      have hsub := hmem.1
      fin_cases hsub <;>
        simp [IsNonNestingPlacement] at hmem <;>
        try decide
    · intro hmem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with rfl | rfl | rfl | rfl <;>
        simp [IsNonNestingPlacement, hcells]
  rw [truncatedStaircaseRookPolynomial, rookPolynomial, hplacements]
  norm_num
  have hC3 : (C (3 : ℝ) : ℝ[X]) = 3 := Polynomial.C_eq_natCast (R := ℝ) 3
  rw [hC3]
  ring_nf

/-- The one-row truncated staircase with four cells has rook polynomial
`1 + 4X`. -/
@[simp] theorem truncatedStaircaseRookPolynomial_four_one :
    truncatedStaircaseRookPolynomial 4 1 = 1 + C (4 : ℝ) * X := by
  classical
  let placements : List (Finset (ℕ × ℕ)) :=
    [∅, {(0, 0)}, {(0, 1)}, {(0, 2)}, {(0, 3)}]
  have hplacements_nodup : placements.Nodup := by
    decide
  have hplacements_toFinset :
      ({∅, {(0, 0)}, {(0, 1)}, {(0, 2)}, {(0, 3)}} :
        Finset (Finset (ℕ × ℕ))) = placements.toFinset := by
    decide
  have hcells :
      (truncatedStaircase 4 1).cells =
        ({(0, 0), (0, 1), (0, 2), (0, 3)} : Finset (ℕ × ℕ)) := by
    decide
  have hplacements :
      (truncatedStaircase 4 1).cells.powerset.filter
        (fun P => (truncatedStaircase 4 1).IsNonNestingPlacement P) =
        ({∅, {(0, 0)}, {(0, 1)}, {(0, 2)}, {(0, 3)}} :
          Finset (Finset (ℕ × ℕ))) := by
    rw [hcells]
    ext P
    constructor
    · intro hmem
      rw [Finset.mem_filter] at hmem
      have hsub := hmem.1
      fin_cases hsub <;>
        simp [IsNonNestingPlacement] at hmem <;>
        try decide
    · intro hmem
      fin_cases hmem <;> simp [IsNonNestingPlacement, hcells]
  rw [truncatedStaircaseRookPolynomial, rookPolynomial, hplacements,
    hplacements_toFinset]
  rw [List.sum_toFinset _ hplacements_nodup]
  norm_num [placements]
  have hC4 : (C (4 : ℝ) : ℝ[X]) = 4 := Polynomial.C_eq_natCast (R := ℝ) 4
  rw [hC4]
  ring_nf

/-- The two-row truncated staircase with row lengths three and two has rook
polynomial `1 + 5X + 3X^2`. -/
@[simp] theorem truncatedStaircaseRookPolynomial_three_two :
    truncatedStaircaseRookPolynomial 3 2 =
      1 + C (5 : ℝ) * X + C (3 : ℝ) * X ^ 2 := by
  classical
  let placements : List (Finset (ℕ × ℕ)) :=
    [∅, {(0, 0)}, {(0, 1)}, {(0, 2)}, {(1, 0)}, {(1, 1)},
      {(0, 1), (1, 0)}, {(0, 2), (1, 0)}, {(0, 2), (1, 1)}]
  have hplacements_nodup : placements.Nodup := by
    decide
  have hplacements_toFinset :
      ({∅, {(0, 0)}, {(0, 1)}, {(0, 2)}, {(1, 0)}, {(1, 1)},
        {(0, 1), (1, 0)}, {(0, 2), (1, 0)}, {(0, 2), (1, 1)}} :
        Finset (Finset (ℕ × ℕ))) = placements.toFinset := by
    decide
  have hcells :
      (truncatedStaircase 3 2).cells =
        ({(0, 0), (0, 1), (0, 2), (1, 0), (1, 1)} : Finset (ℕ × ℕ)) := by
    decide
  have hvalid00 :
      (truncatedStaircase 3 2).IsNonNestingPlacement
        ({(0, 0)} : Finset (ℕ × ℕ)) := by
    exact isNonNestingPlacement_singleton (by rw [hcells]; simp)
  have hvalid01 :
      (truncatedStaircase 3 2).IsNonNestingPlacement
        ({(0, 1)} : Finset (ℕ × ℕ)) := by
    exact isNonNestingPlacement_singleton (by rw [hcells]; simp)
  have hvalid02 :
      (truncatedStaircase 3 2).IsNonNestingPlacement
        ({(0, 2)} : Finset (ℕ × ℕ)) := by
    exact isNonNestingPlacement_singleton (by rw [hcells]; simp)
  have hvalid10 :
      (truncatedStaircase 3 2).IsNonNestingPlacement
        ({(1, 0)} : Finset (ℕ × ℕ)) := by
    exact isNonNestingPlacement_singleton (by rw [hcells]; simp)
  have hvalid11 :
      (truncatedStaircase 3 2).IsNonNestingPlacement
        ({(1, 1)} : Finset (ℕ × ℕ)) := by
    exact isNonNestingPlacement_singleton (by rw [hcells]; simp)
  have hvalid01_10 :
      (truncatedStaircase 3 2).IsNonNestingPlacement
        ({(0, 1), (1, 0)} : Finset (ℕ × ℕ)) := by
    refine isNonNestingPlacement_pair (0, 1) (1, 0) (by rw [hcells]; simp)
      (by rw [hcells]; simp) ?_ ?_ ?_
    · norm_num
    · intro _
      norm_num
    · intro h
      norm_num at h
  have hvalid02_10 :
      (truncatedStaircase 3 2).IsNonNestingPlacement
        ({(0, 2), (1, 0)} : Finset (ℕ × ℕ)) := by
    refine isNonNestingPlacement_pair (0, 2) (1, 0) (by rw [hcells]; simp)
      (by rw [hcells]; simp) ?_ ?_ ?_
    · norm_num
    · intro _
      norm_num
    · intro h
      norm_num at h
  have hvalid02_11 :
      (truncatedStaircase 3 2).IsNonNestingPlacement
        ({(0, 2), (1, 1)} : Finset (ℕ × ℕ)) := by
    refine isNonNestingPlacement_pair (0, 2) (1, 1) (by rw [hcells]; simp)
      (by rw [hcells]; simp) ?_ ?_ ?_
    · norm_num
    · intro _
      norm_num
    · intro h
      norm_num at h
  have hplacements :
      (truncatedStaircase 3 2).cells.powerset.filter
        (fun P => (truncatedStaircase 3 2).IsNonNestingPlacement P) =
        ({∅, {(0, 0)}, {(0, 1)}, {(0, 2)}, {(1, 0)}, {(1, 1)},
          {(0, 1), (1, 0)}, {(0, 2), (1, 0)}, {(0, 2), (1, 1)}} :
          Finset (Finset (ℕ × ℕ))) := by
    rw [hcells]
    ext P
    constructor
    · intro hmem
      rw [Finset.mem_filter] at hmem
      have hsub := hmem.1
      fin_cases hsub <;>
        simp [IsNonNestingPlacement] at hmem <;>
        try decide
    · intro hmem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact Finset.mem_filter.mpr ⟨by simp, isNonNestingPlacement_empty _⟩
      · exact Finset.mem_filter.mpr ⟨by simp, hvalid00⟩
      · exact Finset.mem_filter.mpr ⟨by simp, hvalid01⟩
      · exact Finset.mem_filter.mpr ⟨by simp, hvalid02⟩
      · exact Finset.mem_filter.mpr ⟨by simp, hvalid10⟩
      · exact Finset.mem_filter.mpr ⟨by simp, hvalid11⟩
      · exact Finset.mem_filter.mpr ⟨by decide, hvalid01_10⟩
      · exact Finset.mem_filter.mpr ⟨by decide, hvalid02_10⟩
      · exact Finset.mem_filter.mpr ⟨by decide, hvalid02_11⟩
  rw [truncatedStaircaseRookPolynomial, rookPolynomial, hplacements,
    hplacements_toFinset]
  rw [List.sum_toFinset _ hplacements_nodup]
  norm_num [placements]
  have hC3 : (C (3 : ℝ) : ℝ[X]) = 3 := Polynomial.C_eq_natCast (R := ℝ) 3
  have hC5 : (C (5 : ℝ) : ℝ[X]) = 5 := Polynomial.C_eq_natCast (R := ℝ) 5
  rw [hC3, hC5]
  ring_nf

/-- The two-row truncated staircase with row lengths four and three has rook
polynomial `1 + 7X + 6X^2`. -/
@[simp] theorem truncatedStaircaseRookPolynomial_four_two :
    truncatedStaircaseRookPolynomial 4 2 =
      1 + C (7 : ℝ) * X + C (6 : ℝ) * X ^ 2 := by
  classical
  let placements : List (Finset (ℕ × ℕ)) :=
    [∅, {(0, 0)}, {(0, 1)}, {(0, 2)}, {(0, 3)}, {(1, 0)}, {(1, 1)}, {(1, 2)},
      {(0, 1), (1, 0)}, {(0, 2), (1, 0)}, {(0, 2), (1, 1)},
      {(0, 3), (1, 0)}, {(0, 3), (1, 1)}, {(0, 3), (1, 2)}]
  have hplacements_nodup : placements.Nodup := by
    decide
  have hplacements_toFinset :
      ({∅, {(0, 0)}, {(0, 1)}, {(0, 2)}, {(0, 3)}, {(1, 0)}, {(1, 1)}, {(1, 2)},
        {(0, 1), (1, 0)}, {(0, 2), (1, 0)}, {(0, 2), (1, 1)},
        {(0, 3), (1, 0)}, {(0, 3), (1, 1)}, {(0, 3), (1, 2)}} :
        Finset (Finset (ℕ × ℕ))) = placements.toFinset := by
    decide
  have hcells :
      (truncatedStaircase 4 2).cells =
        ({(0, 0), (0, 1), (0, 2), (0, 3), (1, 0), (1, 1), (1, 2)} :
          Finset (ℕ × ℕ)) := by
    decide
  have hplacements_bool :
      ({(0, 0), (0, 1), (0, 2), (0, 3), (1, 0), (1, 1), (1, 2)} :
          Finset (ℕ × ℕ)).powerset.filter
        (fun P => isNonNestingPlacementBool (truncatedStaircase 4 2) P) =
        ({∅, {(0, 0)}, {(0, 1)}, {(0, 2)}, {(0, 3)}, {(1, 0)}, {(1, 1)}, {(1, 2)},
          {(0, 1), (1, 0)}, {(0, 2), (1, 0)}, {(0, 2), (1, 1)},
          {(0, 3), (1, 0)}, {(0, 3), (1, 1)}, {(0, 3), (1, 2)}} :
          Finset (Finset (ℕ × ℕ))) := by
    decide
  have hplacements :
      (truncatedStaircase 4 2).cells.powerset.filter
        (fun P => (truncatedStaircase 4 2).IsNonNestingPlacement P) =
        ({∅, {(0, 0)}, {(0, 1)}, {(0, 2)}, {(0, 3)}, {(1, 0)}, {(1, 1)}, {(1, 2)},
          {(0, 1), (1, 0)}, {(0, 2), (1, 0)}, {(0, 2), (1, 1)},
          {(0, 3), (1, 0)}, {(0, 3), (1, 1)}, {(0, 3), (1, 2)}} :
          Finset (Finset (ℕ × ℕ))) := by
    rw [hcells]
    rw [← hplacements_bool]
    ext P
    simp only [Finset.mem_filter]
    constructor
    · intro h
      exact ⟨h.1, (isNonNestingPlacementBool_iff (truncatedStaircase 4 2) P).mpr h.2⟩
    · intro h
      exact ⟨h.1, (isNonNestingPlacementBool_iff (truncatedStaircase 4 2) P).mp h.2⟩
  rw [truncatedStaircaseRookPolynomial, rookPolynomial, hplacements,
    hplacements_toFinset]
  rw [List.sum_toFinset _ hplacements_nodup]
  norm_num [placements]
  have hC6 : (C (6 : ℝ) : ℝ[X]) = 6 := Polynomial.C_eq_natCast (R := ℝ) 6
  have hC7 : (C (7 : ℝ) : ℝ[X]) = 7 := Polynomial.C_eq_natCast (R := ℝ) 7
  rw [hC6, hC7]
  ring_nf

/-- The three-row truncated staircase with row lengths four, three, and two
has rook polynomial `1 + 9X + 14X^2 + 4X^3`. -/
@[simp] theorem truncatedStaircaseRookPolynomial_four_three :
    truncatedStaircaseRookPolynomial 4 3 =
      1 + C (9 : ℝ) * X + C (14 : ℝ) * X ^ 2 + C (4 : ℝ) * X ^ 3 := by
  classical
  let placements : List (Finset (ℕ × ℕ)) :=
    [∅,
      {(0, 0)}, {(0, 1)}, {(0, 2)}, {(0, 3)},
      {(1, 0)}, {(1, 1)}, {(1, 2)}, {(2, 0)}, {(2, 1)},
      {(0, 1), (1, 0)}, {(0, 2), (1, 0)}, {(0, 2), (1, 1)},
      {(0, 3), (1, 0)}, {(0, 3), (1, 1)}, {(0, 3), (1, 2)},
      {(0, 1), (2, 0)}, {(0, 2), (2, 0)}, {(0, 2), (2, 1)},
      {(0, 3), (2, 0)}, {(0, 3), (2, 1)},
      {(1, 1), (2, 0)}, {(1, 2), (2, 0)}, {(1, 2), (2, 1)},
      {(0, 2), (1, 1), (2, 0)}, {(0, 3), (1, 1), (2, 0)},
      {(0, 3), (1, 2), (2, 0)}, {(0, 3), (1, 2), (2, 1)}]
  have hplacements_nodup : placements.Nodup := by
    decide
  have hplacements_toFinset :
      ({∅,
        {(0, 0)}, {(0, 1)}, {(0, 2)}, {(0, 3)},
        {(1, 0)}, {(1, 1)}, {(1, 2)}, {(2, 0)}, {(2, 1)},
        {(0, 1), (1, 0)}, {(0, 2), (1, 0)}, {(0, 2), (1, 1)},
        {(0, 3), (1, 0)}, {(0, 3), (1, 1)}, {(0, 3), (1, 2)},
        {(0, 1), (2, 0)}, {(0, 2), (2, 0)}, {(0, 2), (2, 1)},
        {(0, 3), (2, 0)}, {(0, 3), (2, 1)},
        {(1, 1), (2, 0)}, {(1, 2), (2, 0)}, {(1, 2), (2, 1)},
        {(0, 2), (1, 1), (2, 0)}, {(0, 3), (1, 1), (2, 0)},
        {(0, 3), (1, 2), (2, 0)}, {(0, 3), (1, 2), (2, 1)}} :
        Finset (Finset (ℕ × ℕ))) = placements.toFinset := by
    decide
  have hcells :
      (truncatedStaircase 4 3).cells =
        ({(0, 0), (0, 1), (0, 2), (0, 3), (1, 0), (1, 1), (1, 2),
          (2, 0), (2, 1)} : Finset (ℕ × ℕ)) := by
    decide
  have hplacements_bool :
      ({(0, 0), (0, 1), (0, 2), (0, 3), (1, 0), (1, 1), (1, 2),
          (2, 0), (2, 1)} : Finset (ℕ × ℕ)).powerset.filter
        (fun P => isNonNestingPlacementBool (truncatedStaircase 4 3) P) =
        ({∅,
          {(0, 0)}, {(0, 1)}, {(0, 2)}, {(0, 3)},
          {(1, 0)}, {(1, 1)}, {(1, 2)}, {(2, 0)}, {(2, 1)},
          {(0, 1), (1, 0)}, {(0, 2), (1, 0)}, {(0, 2), (1, 1)},
          {(0, 3), (1, 0)}, {(0, 3), (1, 1)}, {(0, 3), (1, 2)},
          {(0, 1), (2, 0)}, {(0, 2), (2, 0)}, {(0, 2), (2, 1)},
          {(0, 3), (2, 0)}, {(0, 3), (2, 1)},
          {(1, 1), (2, 0)}, {(1, 2), (2, 0)}, {(1, 2), (2, 1)},
          {(0, 2), (1, 1), (2, 0)}, {(0, 3), (1, 1), (2, 0)},
          {(0, 3), (1, 2), (2, 0)}, {(0, 3), (1, 2), (2, 1)}} :
          Finset (Finset (ℕ × ℕ))) := by
    decide
  have hplacements :
      (truncatedStaircase 4 3).cells.powerset.filter
        (fun P => (truncatedStaircase 4 3).IsNonNestingPlacement P) =
        ({∅,
          {(0, 0)}, {(0, 1)}, {(0, 2)}, {(0, 3)},
          {(1, 0)}, {(1, 1)}, {(1, 2)}, {(2, 0)}, {(2, 1)},
          {(0, 1), (1, 0)}, {(0, 2), (1, 0)}, {(0, 2), (1, 1)},
          {(0, 3), (1, 0)}, {(0, 3), (1, 1)}, {(0, 3), (1, 2)},
          {(0, 1), (2, 0)}, {(0, 2), (2, 0)}, {(0, 2), (2, 1)},
          {(0, 3), (2, 0)}, {(0, 3), (2, 1)},
          {(1, 1), (2, 0)}, {(1, 2), (2, 0)}, {(1, 2), (2, 1)},
          {(0, 2), (1, 1), (2, 0)}, {(0, 3), (1, 1), (2, 0)},
          {(0, 3), (1, 2), (2, 0)}, {(0, 3), (1, 2), (2, 1)}} :
          Finset (Finset (ℕ × ℕ))) := by
    rw [hcells]
    rw [← hplacements_bool]
    ext P
    simp only [Finset.mem_filter]
    constructor
    · intro h
      exact ⟨h.1, (isNonNestingPlacementBool_iff (truncatedStaircase 4 3) P).mpr h.2⟩
    · intro h
      exact ⟨h.1, (isNonNestingPlacementBool_iff (truncatedStaircase 4 3) P).mp h.2⟩
  rw [truncatedStaircaseRookPolynomial, rookPolynomial, hplacements,
    hplacements_toFinset]
  rw [List.sum_toFinset _ hplacements_nodup]
  norm_num [placements]
  have hC4 : (C (4 : ℝ) : ℝ[X]) = 4 := Polynomial.C_eq_natCast (R := ℝ) 4
  have hC9 : (C (9 : ℝ) : ℝ[X]) = 9 := Polynomial.C_eq_natCast (R := ℝ) 9
  have hC14 : (C (14 : ℝ) : ℝ[X]) = 14 := Polynomial.C_eq_natCast (R := ℝ) 14
  rw [hC4, hC9, hC14]
  ring_nf

/-- Truncated-staircase rook polynomials are nonzero. -/
theorem truncatedStaircaseRookPolynomial_ne_zero (n i : ℕ) :
    truncatedStaircaseRookPolynomial n i ≠ 0 :=
  rookPolynomial_ne_zero _

/-- The auxiliary polynomial `G_n` as a finite sum over truncated staircase
rook polynomials. -/
def auxiliaryG : ℕ → ℝ[X] :=
  fun n => ((List.range n).map fun i => truncatedStaircaseRookPolynomial n i).sum

/-- The finite-board auxiliary polynomial `G_0` is zero. -/
@[simp] theorem auxiliaryG_zero :
    auxiliaryG 0 = 0 := by
  simp [auxiliaryG]

/-- The finite-board auxiliary polynomial `G_1` is one. -/
@[simp] theorem auxiliaryG_one :
    auxiliaryG 1 = 1 := by
  simp [auxiliaryG]

/-- The finite-board auxiliary polynomial `G_2` is `2 + 2X`. -/
@[simp] theorem auxiliaryG_two :
    auxiliaryG 2 = 2 + C (2 : ℝ) * X := by
  rw [auxiliaryG, show List.range 2 = [0, 1] by rfl]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  rw [truncatedStaircaseRookPolynomial_zero_rows,
    truncatedStaircaseRookPolynomial_two_one]
  ring_nf

/-- The finite-board auxiliary polynomial `G_3` is `3 + 8X + 3X^2`. -/
@[simp] theorem auxiliaryG_three :
    auxiliaryG 3 = 3 + C (8 : ℝ) * X + C (3 : ℝ) * X ^ 2 := by
  rw [auxiliaryG, show List.range 3 = [0, 1, 2] by rfl]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  rw [truncatedStaircaseRookPolynomial_zero_rows,
    truncatedStaircaseRookPolynomial_three_one,
    truncatedStaircaseRookPolynomial_three_two]
  have hC3 : (C (3 : ℝ) : ℝ[X]) = 3 := Polynomial.C_eq_natCast (R := ℝ) 3
  have hC5 : (C (5 : ℝ) : ℝ[X]) = 5 := Polynomial.C_eq_natCast (R := ℝ) 5
  have hC8 : (C (8 : ℝ) : ℝ[X]) = 8 := Polynomial.C_eq_natCast (R := ℝ) 8
  rw [hC3, hC5, hC8]
  ring_nf

/-- The expected `G_4` finite-board value follows from the remaining two-row
and three-row truncated-staircase computations. -/
theorem auxiliaryG_four_of_truncatedStaircaseRookPolynomial_four_two_three
    (h42 : truncatedStaircaseRookPolynomial 4 2 =
      1 + C (7 : ℝ) * X + C (6 : ℝ) * X ^ 2)
    (h43 : truncatedStaircaseRookPolynomial 4 3 =
      1 + C (9 : ℝ) * X + C (14 : ℝ) * X ^ 2 + C (4 : ℝ) * X ^ 3) :
    auxiliaryG 4 = 4 + C (20 : ℝ) * X + C (20 : ℝ) * X ^ 2 +
      C (4 : ℝ) * X ^ 3 := by
  rw [auxiliaryG, show List.range 4 = [0, 1, 2, 3] by rfl]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  rw [truncatedStaircaseRookPolynomial_zero_rows,
    truncatedStaircaseRookPolynomial_four_one, h42, h43]
  have hC4 : (C (4 : ℝ) : ℝ[X]) = 4 := Polynomial.C_eq_natCast (R := ℝ) 4
  have hC6 : (C (6 : ℝ) : ℝ[X]) = 6 := Polynomial.C_eq_natCast (R := ℝ) 6
  have hC7 : (C (7 : ℝ) : ℝ[X]) = 7 := Polynomial.C_eq_natCast (R := ℝ) 7
  have hC9 : (C (9 : ℝ) : ℝ[X]) = 9 := Polynomial.C_eq_natCast (R := ℝ) 9
  have hC14 : (C (14 : ℝ) : ℝ[X]) = 14 := Polynomial.C_eq_natCast (R := ℝ) 14
  have hC20 : (C (20 : ℝ) : ℝ[X]) = 20 := Polynomial.C_eq_natCast (R := ℝ) 20
  rw [hC4, hC6, hC7, hC9, hC14, hC20]
  ring_nf

/-- The expected `G_4` finite-board value now follows from the remaining
three-row truncated-staircase computation. -/
theorem auxiliaryG_four_of_truncatedStaircaseRookPolynomial_four_three
    (h43 : truncatedStaircaseRookPolynomial 4 3 =
      1 + C (9 : ℝ) * X + C (14 : ℝ) * X ^ 2 + C (4 : ℝ) * X ^ 3) :
    auxiliaryG 4 = 4 + C (20 : ℝ) * X + C (20 : ℝ) * X ^ 2 +
      C (4 : ℝ) * X ^ 3 :=
  auxiliaryG_four_of_truncatedStaircaseRookPolynomial_four_two_three
    truncatedStaircaseRookPolynomial_four_two h43

/-- The finite-board auxiliary polynomial `G_4` is `4 + 20X + 20X^2 + 4X^3`. -/
@[simp] theorem auxiliaryG_four :
    auxiliaryG 4 = 4 + C (20 : ℝ) * X + C (20 : ℝ) * X ^ 2 +
      C (4 : ℝ) * X ^ 3 :=
  auxiliaryG_four_of_truncatedStaircaseRookPolynomial_four_three
    truncatedStaircaseRookPolynomial_four_three

/-- The finite-board version of `G_n` has nonnegative coefficients. -/
theorem auxiliaryG_hasNonnegCoeffs (n : ℕ) :
    HasNonnegCoeffs (auxiliaryG n) := by
  refine listSum_hasNonnegCoeffs ?_
  intro p hp
  rcases List.mem_map.mp hp with ⟨i, _hi, rfl⟩
  exact rookPolynomial_hasNonnegCoeffs _

end FiniteSkewBoard

/-- Abstract squarecase/non-nesting rook model for generalized snake words.

The concrete squarecase encoding is deliberately not fixed here.  Later files
can instantiate `Board`, `boardOfSnake`, and `nonNestingRookPolynomial` with a
Ferrers/skew-shape model while reusing the theorem-shaped interfaces below. -/
structure SquarecaseRookModel where
  Board : Type u
  boardOfSnake : SnakeWord → Board
  nonNestingRookPolynomial : Board → ℝ[X]

namespace SquarecaseRookModel

/-- The non-nesting rook polynomial attached to a generalized snake word in a
chosen squarecase model. -/
def snakePolynomial (model : SquarecaseRookModel) (w : SnakeWord) : ℝ[X] :=
  model.nonNestingRookPolynomial (model.boardOfSnake w)

end SquarecaseRookModel

/-- A finite-skew-board assignment for snake words gives an abstract squarecase
rook model. -/
def squarecaseRookModelOfFiniteSkewBoard
    (boardOfSnake : SnakeWord → FiniteSkewBoard) : SquarecaseRookModel where
  Board := FiniteSkewBoard
  boardOfSnake := boardOfSnake
  nonNestingRookPolynomial := FiniteSkewBoard.rookPolynomial

@[simp] theorem squarecaseRookModelOfFiniteSkewBoard_snakePolynomial
    (boardOfSnake : SnakeWord → FiniteSkewBoard) (w : SnakeWord) :
    (squarecaseRookModelOfFiniteSkewBoard boardOfSnake).snakePolynomial w =
      (boardOfSnake w).rookPolynomial :=
  rfl

/-- Finite-skew-board squarecase models have constant coefficient one for every
snake-word polynomial. -/
@[simp] theorem squarecaseRookModelOfFiniteSkewBoard_snakePolynomial_coeff_zero
    (boardOfSnake : SnakeWord → FiniteSkewBoard) (w : SnakeWord) :
    ((squarecaseRookModelOfFiniteSkewBoard boardOfSnake).snakePolynomial w).coeff 0 = 1 :=
  FiniteSkewBoard.rookPolynomial_coeff_zero _

/-- Finite-skew-board squarecase models have nonzero snake-word polynomials. -/
theorem squarecaseRookModelOfFiniteSkewBoard_snakePolynomial_ne_zero
    (boardOfSnake : SnakeWord → FiniteSkewBoard) (w : SnakeWord) :
    (squarecaseRookModelOfFiniteSkewBoard boardOfSnake).snakePolynomial w ≠ 0 :=
  FiniteSkewBoard.rookPolynomial_ne_zero _

/-- Statement interface for Braun--Jal Theorem 4.1, with the non-nesting rook
polynomial supplied as a parameter. -/
def Theorem41NonNestingRookStatement (M : SnakeWord → ℝ[X]) : Prop :=
  ∀ {w : SnakeWord}, 1 ≤ w.length →
    (M w ≠ 0 ∧ (M w).Splits) ∧
      Interlaces (M w.deleteFinal) (M w)

/-- Compatibility alias with a name that is easy to find from the paper title. -/
abbrev BraunJalGeneralizedSnakeRealRootedStatement
    (M : SnakeWord → ℝ[X]) : Prop :=
  Theorem41NonNestingRookStatement M

/-- Compatibility alias matching the first milestone note. -/
abbrev GeneralizedSnakeNonNestingRookInterlacesStatement
    (M : SnakeWord → ℝ[X]) : Prop :=
  Theorem41NonNestingRookStatement M

/-- Theorem 4.1 expressed for an abstract squarecase/non-nesting rook model. -/
abbrev SquarecaseRookModelTheorem41Statement
    (model : SquarecaseRookModel) : Prop :=
  Theorem41NonNestingRookStatement model.snakePolynomial

/-- The real-rootedness part of Braun--Jal Theorem 4.1. -/
theorem nonNestingRook_ne_zero_and_splits_of_theorem41
    {M : SnakeWord → ℝ[X]}
    (hBJ : Theorem41NonNestingRookStatement M)
    {w : SnakeWord} (hw : 1 ≤ w.length) :
    M w ≠ 0 ∧ (M w).Splits :=
  (hBJ (w := w) hw).1

/-- The final-letter-deletion interlacing part of Braun--Jal Theorem 4.1. -/
theorem nonNestingRook_deleteFinal_interlaces_of_theorem41
    {M : SnakeWord → ℝ[X]}
    (hBJ : Theorem41NonNestingRookStatement M)
    {w : SnakeWord} (hw : 1 ≤ w.length) :
    Interlaces (M w.deleteFinal) (M w) :=
  (hBJ (w := w) hw).2

/-! ## Narayana and recurrence interfaces from Section 3 -/

/-- A family `P` is the modified Narayana family attached to Narayana
polynomials `N` when `N_{n+1} = X * P_n`, i.e. `P_n(t) = t^{-1} N_{n+1}(t)`.
-/
def ModifiedNarayanaFamilyStatement
    (N P : ℕ → ℝ[X]) : Prop :=
  P 0 = 1 ∧ ∀ n : ℕ, N (n + 1) = X * P n

/-- The auxiliary polynomial `G_n` as the sum of non-nesting rook polynomials
of truncated staircases `mu_{n,i}` for `i = 0, ..., n - 1`. -/
def AuxiliaryGMatchesTruncatedStaircasesStatement
    (Mtrunc : ℕ → ℕ → ℝ[X]) (G : ℕ → ℝ[X]) : Prop :=
  ∀ n : ℕ, G n = ((List.range n).map fun i => Mtrunc n i).sum

/-- The finite-board definition of `G_n` satisfies the truncated-staircase
interface. -/
theorem FiniteSkewBoard.auxiliaryG_matchesTruncatedStaircases :
    AuxiliaryGMatchesTruncatedStaircasesStatement
      FiniteSkewBoard.truncatedStaircaseRookPolynomial
      FiniteSkewBoard.auxiliaryG := by
  intro n
  rfl

/-- Equation (2) of Braun--Jal: `X * G_{n-1} = P_n - (1 + X) * P_{n-1}`. -/
def NarayanaAuxiliaryGRecurrenceStatement
    (P G : ℕ → ℝ[X]) : Prop :=
  ∀ {n : ℕ}, 1 ≤ n → X * G (n - 1) = P n - (1 + X) * P (n - 1)

/-- Lemma 3.3 statement: the auxiliary `G_n` interlaces the modified Narayana
polynomial `P_n`. -/
def Lemma33AuxiliaryGInterlacesStatement
    (P G : ℕ → ℝ[X]) : Prop :=
  ∀ {n : ℕ}, 1 ≤ n → Prec (G n) (P n)

/-- Lemma 3.4 statement for the modified Narayana family. -/
def Lemma34ModifiedNarayanaInterlacingStatement
    (P : ℕ → ℝ[X]) : Prop :=
  ∀ {m : ℕ} {lam nu : ℝ}, 2 ≤ m → 0 ≤ lam → -1 ≤ nu →
    Prec ((C lam * X + C nu) * P (m - 1) + P m)
      ((C lam * X + C nu) * P m + P (m + 1))

/-- Difference `Q_n = P_n - P_{n-1}` used in the Theorem 4.1 matrix step. -/
def narayanaDifference (P : ℕ → ℝ[X]) (n : ℕ) : ℝ[X] :=
  P n - P (n - 1)

/-- Difference `H_n = G_n - G_{n-1}` used in the Theorem 4.1 matrix step. -/
def auxiliaryDifference (G : ℕ → ℝ[X]) (n : ℕ) : ℝ[X] :=
  G n - G (n - 1)

/-- The claim labeled `(6)` in Braun--Jal's proof of Theorem 4.1. -/
def Theorem41MatrixClaimStatement
    (P G : ℕ → ℝ[X]) : Prop :=
  ∀ {m : ℕ} {lam mu : ℝ}, 2 ≤ m → 0 ≤ lam → 0 ≤ mu →
    Prec ((C lam * X + C mu) * G (m - 1) + auxiliaryDifference G m)
      ((C lam * X + C mu) * P (m - 1) + narayanaDifference P m)

/-- The reindexed claim labeled `(7)` in Braun--Jal's proof of Theorem 4.1. -/
def Theorem41Claim7Statement
    (P G : ℕ → ℝ[X]) : Prop :=
  ∀ {m : ℕ} {lam nu : ℝ}, 2 ≤ m → 0 ≤ lam → -1 ≤ nu →
    Prec ((C lam * X + C nu) * G (m - 1) + G m)
      ((C lam * X + C nu) * P (m - 1) + P m)

/-- The generalized snake recurrence, Theorem 3.5, in zero-based list
coordinates.  If `k` is the last position where `w` differs from its final
letter, then paper notation `w[:k+1]` and `w[:k]` become `takePrefix (k+1)`
and `takePrefix k` for the list of letters following `epsilon`. -/
def Theorem35GeneralizedSnakeRecurrenceStatement
    (M : SnakeWord → ℝ[X]) (P G : ℕ → ℝ[X]) : Prop :=
  ∀ {w : SnakeWord} {k : ℕ}, ¬ w.IsConstant → w.IsLastChangeIndex k →
    M w = M (w.takePrefix (k + 1)) * P (w.length - (k + 1)) +
      X * M (w.takePrefix k) * G (w.length - (k + 1))

/-- Computable form of Theorem 3.5, using `lastChangeIndex?` instead of a
separate predicate-form witness. -/
def Theorem35GeneralizedSnakeRecurrenceComputableStatement
    (M : SnakeWord → ℝ[X]) (P G : ℕ → ℝ[X]) : Prop :=
  ∀ {w : SnakeWord} {k : ℕ}, w.lastChangeIndex? = some k →
    M w = M (w.takePrefix (k + 1)) * P (w.length - (k + 1)) +
      X * M (w.takePrefix k) * G (w.length - (k + 1))

/-- The predicate-form recurrence implies the computable `lastChangeIndex?`
form. -/
theorem theorem35Computable_of_theorem35
    {M : SnakeWord → ℝ[X]} {P G : ℕ → ℝ[X]}
    (hrec : Theorem35GeneralizedSnakeRecurrenceStatement M P G) :
    Theorem35GeneralizedSnakeRecurrenceComputableStatement M P G := by
  intro w k hlast
  exact hrec (SnakeWord.not_isConstant_of_lastChangeIndex?_eq_some hlast)
    (SnakeWord.isLastChangeIndex_of_lastChangeIndex?_eq_some hlast)

/-- The computable `lastChangeIndex?` recurrence implies the predicate-form
recurrence. -/
theorem theorem35_of_theorem35Computable
    {M : SnakeWord → ℝ[X]} {P G : ℕ → ℝ[X]}
    (hrec : Theorem35GeneralizedSnakeRecurrenceComputableStatement M P G) :
    Theorem35GeneralizedSnakeRecurrenceStatement M P G := by
  intro w k _hconst hlast
  exact hrec (SnakeWord.lastChangeIndex?_eq_some_of_isLastChangeIndex hlast)

/-- The predicate-form and computable forms of the generalized snake
recurrence are equivalent. -/
theorem theorem35Computable_iff_theorem35
    (M : SnakeWord → ℝ[X]) (P G : ℕ → ℝ[X]) :
    Theorem35GeneralizedSnakeRecurrenceComputableStatement M P G ↔
      Theorem35GeneralizedSnakeRecurrenceStatement M P G :=
  ⟨theorem35_of_theorem35Computable, theorem35Computable_of_theorem35⟩

/-- Statement-level package for the induction route from the Section 3
Narayana and recurrence ingredients to Theorem 4.1. -/
def Theorem41InductionRouteStatement
    (M : SnakeWord → ℝ[X]) (P G : ℕ → ℝ[X]) : Prop :=
  Lemma33AuxiliaryGInterlacesStatement P G →
    Lemma34ModifiedNarayanaInterlacingStatement P →
    Theorem35GeneralizedSnakeRecurrenceStatement M P G →
      Theorem41NonNestingRookStatement M

/-- Computable-recursion variant of the current Theorem 4.1 induction route. -/
def Theorem41InductionRouteComputableStatement
    (M : SnakeWord → ℝ[X]) (P G : ℕ → ℝ[X]) : Prop :=
  Lemma33AuxiliaryGInterlacesStatement P G →
    Lemma34ModifiedNarayanaInterlacingStatement P →
    Theorem35GeneralizedSnakeRecurrenceComputableStatement M P G →
      Theorem41NonNestingRookStatement M

/-- The predicate-form induction route also accepts a computable recurrence
input. -/
theorem theorem41InductionRouteComputable_of_theorem41InductionRoute
    {M : SnakeWord → ℝ[X]} {P G : ℕ → ℝ[X]}
    (hroute : Theorem41InductionRouteStatement M P G) :
    Theorem41InductionRouteComputableStatement M P G := by
  intro h33 h34 hrec
  exact hroute h33 h34 (theorem35_of_theorem35Computable hrec)

/-- The computable-recursion induction route implies the predicate-form route. -/
theorem theorem41InductionRoute_of_theorem41InductionRouteComputable
    {M : SnakeWord → ℝ[X]} {P G : ℕ → ℝ[X]}
    (hroute : Theorem41InductionRouteComputableStatement M P G) :
    Theorem41InductionRouteStatement M P G := by
  intro h33 h34 hrec
  exact hroute h33 h34 (theorem35Computable_of_theorem35 hrec)

/-- Predicate and computable forms of the Theorem 4.1 induction route are
equivalent. -/
theorem theorem41InductionRouteComputable_iff_theorem41InductionRoute
    (M : SnakeWord → ℝ[X]) (P G : ℕ → ℝ[X]) :
    Theorem41InductionRouteComputableStatement M P G ↔
      Theorem41InductionRouteStatement M P G :=
  ⟨theorem41InductionRoute_of_theorem41InductionRouteComputable,
    theorem41InductionRouteComputable_of_theorem41InductionRoute⟩

/-- Bundled Section 3 ingredients needed by the current Theorem 4.1 induction
interface. -/
structure Theorem41Section3Inputs
    (M : SnakeWord → ℝ[X]) (P G : ℕ → ℝ[X]) : Prop where
  lemma33 : Lemma33AuxiliaryGInterlacesStatement P G
  lemma34 : Lemma34ModifiedNarayanaInterlacingStatement P
  recurrence : Theorem35GeneralizedSnakeRecurrenceStatement M P G

/-- Bundled Section 3 ingredients using the computable recurrence form. -/
structure Theorem41Section3ComputableInputs
    (M : SnakeWord → ℝ[X]) (P G : ℕ → ℝ[X]) : Prop where
  lemma33 : Lemma33AuxiliaryGInterlacesStatement P G
  lemma34 : Lemma34ModifiedNarayanaInterlacingStatement P
  recurrence : Theorem35GeneralizedSnakeRecurrenceComputableStatement M P G

/-- Convert computable Section 3 inputs into the predicate-form bundle. -/
theorem theorem41Section3Inputs_of_computable
    {M : SnakeWord → ℝ[X]} {P G : ℕ → ℝ[X]}
    (hinputs : Theorem41Section3ComputableInputs M P G) :
    Theorem41Section3Inputs M P G where
  lemma33 := hinputs.lemma33
  lemma34 := hinputs.lemma34
  recurrence := theorem35_of_theorem35Computable hinputs.recurrence

/-- Feed the bundled Section 3 ingredients into the abstract Theorem 4.1
induction route. -/
theorem theorem41_of_section3Inputs
    {M : SnakeWord → ℝ[X]} {P G : ℕ → ℝ[X]}
    (hroute : Theorem41InductionRouteStatement M P G)
    (hinputs : Theorem41Section3Inputs M P G) :
    Theorem41NonNestingRookStatement M :=
  hroute hinputs.lemma33 hinputs.lemma34 hinputs.recurrence

/-- Feed computable Section 3 ingredients into the abstract Theorem 4.1
induction route. -/
theorem theorem41_of_section3ComputableInputs
    {M : SnakeWord → ℝ[X]} {P G : ℕ → ℝ[X]}
    (hroute : Theorem41InductionRouteStatement M P G)
    (hinputs : Theorem41Section3ComputableInputs M P G) :
    Theorem41NonNestingRookStatement M :=
  theorem41_of_section3Inputs hroute
    (theorem41Section3Inputs_of_computable hinputs)

/-! ## Squarecase recurrence packages -/

/-- Existence statement for a squarecase model satisfying the computable
Braun--Jal Theorem 3.5 recurrence for some Section 3 families `P` and `G`. -/
def SquarecaseRookRecurrenceStatement (model : SquarecaseRookModel) : Prop :=
  ∃ P G : ℕ → ℝ[X],
    Theorem35GeneralizedSnakeRecurrenceComputableStatement
      model.snakePolynomial P G

/-- Data package for a concrete squarecase/non-nesting rook recurrence.

Later board files should construct this from the actual squarecase board model
and Braun--Jal's positive recurrence. -/
structure SquarecaseRookRecurrencePackage (model : SquarecaseRookModel) where
  P : ℕ → ℝ[X]
  G : ℕ → ℝ[X]
  recurrence :
    Theorem35GeneralizedSnakeRecurrenceComputableStatement
      model.snakePolynomial P G

namespace SquarecaseRookRecurrencePackage

/-- Forget a recurrence data package to the corresponding existence
statement. -/
theorem statement {model : SquarecaseRookModel}
    (h : SquarecaseRookRecurrencePackage model) :
    SquarecaseRookRecurrenceStatement model :=
  ⟨h.P, h.G, h.recurrence⟩

/-- A squarecase recurrence package provides the computable Theorem 3.5
interface for its attached polynomial families. -/
theorem theorem35Computable {model : SquarecaseRookModel}
    (h : SquarecaseRookRecurrencePackage model) :
    Theorem35GeneralizedSnakeRecurrenceComputableStatement
      model.snakePolynomial h.P h.G :=
  h.recurrence

/-- A squarecase recurrence package also provides the predicate-form Theorem
3.5 interface. -/
theorem theorem35 {model : SquarecaseRookModel}
    (h : SquarecaseRookRecurrencePackage model) :
    Theorem35GeneralizedSnakeRecurrenceStatement model.snakePolynomial h.P h.G :=
  theorem35_of_theorem35Computable h.recurrence

end SquarecaseRookRecurrencePackage

/-- Existence statement for a squarecase model equipped with the Section 3
inputs needed by the current Theorem 4.1 induction route. -/
def SquarecaseRookSection3Statement (model : SquarecaseRookModel) : Prop :=
  ∃ P G : ℕ → ℝ[X],
    Theorem41Section3ComputableInputs model.snakePolynomial P G

/-- Data package for the squarecase/non-nesting rook model together with the
Narayana and recurrence inputs from Braun--Jal Section 3. -/
structure SquarecaseRookSection3Package (model : SquarecaseRookModel) where
  P : ℕ → ℝ[X]
  G : ℕ → ℝ[X]
  lemma33 : Lemma33AuxiliaryGInterlacesStatement P G
  lemma34 : Lemma34ModifiedNarayanaInterlacingStatement P
  recurrence :
    Theorem35GeneralizedSnakeRecurrenceComputableStatement
      model.snakePolynomial P G

namespace SquarecaseRookSection3Package

/-- The recurrence component of a Section 3 package as a standalone squarecase
recurrence package. -/
def recurrencePackage {model : SquarecaseRookModel}
    (h : SquarecaseRookSection3Package model) :
    SquarecaseRookRecurrencePackage model where
  P := h.P
  G := h.G
  recurrence := h.recurrence

/-- Forget a Section 3 data package to the corresponding existence statement.
-/
theorem statement {model : SquarecaseRookModel}
    (h : SquarecaseRookSection3Package model) :
    SquarecaseRookSection3Statement model :=
  ⟨h.P, h.G, ⟨h.lemma33, h.lemma34, h.recurrence⟩⟩

/-- A squarecase Section 3 package provides the existing computable input
bundle for the attached polynomial families. -/
theorem computableInputs {model : SquarecaseRookModel}
    (h : SquarecaseRookSection3Package model) :
    Theorem41Section3ComputableInputs model.snakePolynomial h.P h.G where
  lemma33 := h.lemma33
  lemma34 := h.lemma34
  recurrence := h.recurrence

/-- A squarecase Section 3 package provides the predicate-form input bundle for
the attached polynomial families. -/
theorem inputs {model : SquarecaseRookModel}
    (h : SquarecaseRookSection3Package model) :
    Theorem41Section3Inputs model.snakePolynomial h.P h.G :=
  theorem41Section3Inputs_of_computable h.computableInputs

/-- Feed a squarecase Section 3 package into the abstract Theorem 4.1 induction
route. -/
theorem theorem41 {model : SquarecaseRookModel}
    (h : SquarecaseRookSection3Package model)
    (hroute : Theorem41InductionRouteStatement model.snakePolynomial h.P h.G) :
    SquarecaseRookModelTheorem41Statement model :=
  theorem41_of_section3Inputs hroute h.inputs

/-- Feed a squarecase Section 3 package into the computable form of the
abstract Theorem 4.1 induction route. -/
theorem theorem41Computable {model : SquarecaseRookModel}
    (h : SquarecaseRookSection3Package model)
    (hroute :
      Theorem41InductionRouteComputableStatement model.snakePolynomial h.P h.G) :
    SquarecaseRookModelTheorem41Statement model :=
  hroute h.lemma33 h.lemma34 h.recurrence

/-- A squarecase Section 3 package also gives the standalone recurrence
existence statement. -/
theorem recurrenceStatement {model : SquarecaseRookModel}
    (h : SquarecaseRookSection3Package model) :
    SquarecaseRookRecurrenceStatement model :=
  h.recurrencePackage.statement

end SquarecaseRookSection3Package

/-- Section 3 inputs for a squarecase model include the Theorem 3.5 recurrence
input needed by the Braun--Jal induction. -/
theorem squarecaseRookRecurrenceStatement_of_section3Statement
    {model : SquarecaseRookModel}
    (hsection : SquarecaseRookSection3Statement model) :
    SquarecaseRookRecurrenceStatement model := by
  rcases hsection with ⟨P, G, hinputs⟩
  exact ⟨P, G, hinputs.recurrence⟩

/-- A statement-level squarecase Section 3 witness plus the abstract induction
route proves the non-nesting-rook form of Braun--Jal Theorem 4.1. -/
theorem theorem41_of_squarecaseSection3Statement
    {model : SquarecaseRookModel}
    (hroute :
      ∀ P G : ℕ → ℝ[X],
        Theorem41InductionRouteStatement model.snakePolynomial P G)
    (hsection : SquarecaseRookSection3Statement model) :
    SquarecaseRookModelTheorem41Statement model := by
  rcases hsection with ⟨P, G, hinputs⟩
  exact theorem41_of_section3ComputableInputs (hroute P G) hinputs

/-- A statement-level squarecase Section 3 witness plus a computable abstract
induction route proves the non-nesting-rook form of Braun--Jal Theorem 4.1. -/
theorem theorem41_of_squarecaseSection3ComputableStatement
    {model : SquarecaseRookModel}
    (hroute :
      ∀ P G : ℕ → ℝ[X],
        Theorem41InductionRouteComputableStatement model.snakePolynomial P G)
    (hsection : SquarecaseRookSection3Statement model) :
    SquarecaseRookModelTheorem41Statement model := by
  rcases hsection with ⟨P, G, hinputs⟩
  exact hroute P G hinputs.lemma33 hinputs.lemma34 hinputs.recurrence

/-- Statement that a chosen order-polytope `h^*` model agrees with the
non-nesting rook polynomial model for generalized snake words. -/
def OrderPolytopeHStarMatchesNonNestingRook
    (hStar M : SnakeWord → ℝ[X]) : Prop :=
  ∀ w : SnakeWord, hStar w = M w

/-- Final order-polytope `h^*` real-rootedness statement, isolated from the
rook-polynomial model. -/
def OrderPolytopeHStarRealRootedStatement
    (hStar : SnakeWord → ℝ[X]) : Prop :=
  ∀ {w : SnakeWord}, 1 ≤ w.length → hStar w ≠ 0 ∧ (hStar w).Splits

/-- Final order-polytope `h^*` interlacing statement, isolated from the
rook-polynomial model. -/
def OrderPolytopeHStarInterlacesStatement
    (hStar : SnakeWord → ℝ[X]) : Prop :=
  ∀ {w : SnakeWord}, 1 ≤ w.length →
    Interlaces (hStar w.deleteFinal) (hStar w)

/-- Full order-polytope `h^*` form of Braun--Jal Theorem 4.1 after the
Stanley/Alexandersson--Jal matching interface has identified the `h^*`
polynomials with non-nesting rook polynomials. -/
def OrderPolytopeHStarTheorem41Statement
    (hStar : SnakeWord → ℝ[X]) : Prop :=
  ∀ {w : SnakeWord}, 1 ≤ w.length →
    (hStar w ≠ 0 ∧ (hStar w).Splits) ∧
      Interlaces (hStar w.deleteFinal) (hStar w)

/-- The full order-polytope `h^*` Theorem 4.1 wrapper implies its
real-rootedness projection. -/
theorem orderPolytopeHStarRealRooted_of_hStarTheorem41
    {hStar : SnakeWord → ℝ[X]}
    (h : OrderPolytopeHStarTheorem41Statement hStar) :
    OrderPolytopeHStarRealRootedStatement hStar := by
  intro w hw
  exact (h hw).1

/-- The full order-polytope `h^*` Theorem 4.1 wrapper implies its interlacing
projection. -/
theorem orderPolytopeHStarInterlaces_of_hStarTheorem41
    {hStar : SnakeWord → ℝ[X]}
    (h : OrderPolytopeHStarTheorem41Statement hStar) :
    OrderPolytopeHStarInterlacesStatement hStar := by
  intro w hw
  exact (h hw).2

/-- Theorem 4.1 plus the Stanley/Alexandersson--Jal matching interface implies
the order-polytope `h^*` real-rootedness wrapper. -/
theorem orderPolytopeHStarRealRooted_of_theorem41
    {hStar M : SnakeWord → ℝ[X]}
    (hBJ : Theorem41NonNestingRookStatement M)
    (hmatch : OrderPolytopeHStarMatchesNonNestingRook hStar M) :
    OrderPolytopeHStarRealRootedStatement hStar := by
  intro w hw
  simpa [hmatch w] using
    nonNestingRook_ne_zero_and_splits_of_theorem41 hBJ (w := w) hw

/-- Theorem 4.1 plus the Stanley/Alexandersson--Jal matching interface implies
the order-polytope `h^*` interlacing wrapper. -/
theorem orderPolytopeHStarInterlaces_of_theorem41
    {hStar M : SnakeWord → ℝ[X]}
    (hBJ : Theorem41NonNestingRookStatement M)
    (hmatch : OrderPolytopeHStarMatchesNonNestingRook hStar M) :
    OrderPolytopeHStarInterlacesStatement hStar := by
  intro w hw
  simpa [hmatch w, hmatch w.deleteFinal] using
    nonNestingRook_deleteFinal_interlaces_of_theorem41 hBJ (w := w) hw

/-- Theorem 4.1 plus the Stanley/Alexandersson--Jal matching interface gives
the full order-polytope `h^*` version of Braun--Jal Theorem 4.1. -/
theorem orderPolytopeHStarTheorem41_of_theorem41
    {hStar M : SnakeWord → ℝ[X]}
    (hBJ : Theorem41NonNestingRookStatement M)
    (hmatch : OrderPolytopeHStarMatchesNonNestingRook hStar M) :
    OrderPolytopeHStarTheorem41Statement hStar := by
  intro w hw
  exact ⟨orderPolytopeHStarRealRooted_of_theorem41 hBJ hmatch hw,
    orderPolytopeHStarInterlaces_of_theorem41 hBJ hmatch hw⟩

/-- A statement-level squarecase Section 3 witness plus the abstract induction
route and order-polytope matching proves the final `h^*` real-rootedness
wrapper. -/
theorem orderPolytopeHStarRealRooted_of_squarecaseSection3Statement
    {hStar : SnakeWord → ℝ[X]} {model : SquarecaseRookModel}
    (hroute :
      ∀ P G : ℕ → ℝ[X],
        Theorem41InductionRouteStatement model.snakePolynomial P G)
    (hsection : SquarecaseRookSection3Statement model)
    (hmatch :
      OrderPolytopeHStarMatchesNonNestingRook hStar model.snakePolynomial) :
    OrderPolytopeHStarRealRootedStatement hStar :=
  orderPolytopeHStarRealRooted_of_theorem41
    (theorem41_of_squarecaseSection3Statement hroute hsection) hmatch

/-- A statement-level squarecase Section 3 witness plus the abstract induction
route and order-polytope matching proves the final `h^*` interlacing wrapper.
-/
theorem orderPolytopeHStarInterlaces_of_squarecaseSection3Statement
    {hStar : SnakeWord → ℝ[X]} {model : SquarecaseRookModel}
    (hroute :
      ∀ P G : ℕ → ℝ[X],
        Theorem41InductionRouteStatement model.snakePolynomial P G)
    (hsection : SquarecaseRookSection3Statement model)
    (hmatch :
      OrderPolytopeHStarMatchesNonNestingRook hStar model.snakePolynomial) :
    OrderPolytopeHStarInterlacesStatement hStar :=
  orderPolytopeHStarInterlaces_of_theorem41
    (theorem41_of_squarecaseSection3Statement hroute hsection) hmatch

/-- A statement-level squarecase Section 3 witness plus the abstract induction
route and order-polytope matching proves the full final `h^*` Theorem 4.1
wrapper. -/
theorem orderPolytopeHStarTheorem41_of_squarecaseSection3Statement
    {hStar : SnakeWord → ℝ[X]} {model : SquarecaseRookModel}
    (hroute :
      ∀ P G : ℕ → ℝ[X],
        Theorem41InductionRouteStatement model.snakePolynomial P G)
    (hsection : SquarecaseRookSection3Statement model)
    (hmatch :
      OrderPolytopeHStarMatchesNonNestingRook hStar model.snakePolynomial) :
    OrderPolytopeHStarTheorem41Statement hStar :=
  orderPolytopeHStarTheorem41_of_theorem41
    (theorem41_of_squarecaseSection3Statement hroute hsection) hmatch

/-- A squarecase Section 3 package, a matching computable induction route, and
the order-polytope matching interface prove the final `h^*` real-rootedness
wrapper. -/
theorem orderPolytopeHStarRealRooted_of_squarecaseSection3Package
    {hStar : SnakeWord → ℝ[X]} {model : SquarecaseRookModel}
    (hsection : SquarecaseRookSection3Package model)
    (hroute :
      Theorem41InductionRouteComputableStatement
        model.snakePolynomial hsection.P hsection.G)
    (hmatch :
      OrderPolytopeHStarMatchesNonNestingRook hStar model.snakePolynomial) :
    OrderPolytopeHStarRealRootedStatement hStar :=
  orderPolytopeHStarRealRooted_of_theorem41
    (hsection.theorem41Computable hroute) hmatch

/-- A squarecase Section 3 package, a matching computable induction route, and
the order-polytope matching interface prove the final `h^*` interlacing
wrapper. -/
theorem orderPolytopeHStarInterlaces_of_squarecaseSection3Package
    {hStar : SnakeWord → ℝ[X]} {model : SquarecaseRookModel}
    (hsection : SquarecaseRookSection3Package model)
    (hroute :
      Theorem41InductionRouteComputableStatement
        model.snakePolynomial hsection.P hsection.G)
    (hmatch :
      OrderPolytopeHStarMatchesNonNestingRook hStar model.snakePolynomial) :
    OrderPolytopeHStarInterlacesStatement hStar :=
  orderPolytopeHStarInterlaces_of_theorem41
    (hsection.theorem41Computable hroute) hmatch

/-- A squarecase Section 3 package, a matching computable induction route, and
the order-polytope matching interface prove the full final `h^*` Theorem 4.1
wrapper. -/
theorem orderPolytopeHStarTheorem41_of_squarecaseSection3Package
    {hStar : SnakeWord → ℝ[X]} {model : SquarecaseRookModel}
    (hsection : SquarecaseRookSection3Package model)
    (hroute :
      Theorem41InductionRouteComputableStatement
        model.snakePolynomial hsection.P hsection.G)
    (hmatch :
      OrderPolytopeHStarMatchesNonNestingRook hStar model.snakePolynomial) :
    OrderPolytopeHStarTheorem41Statement hStar :=
  orderPolytopeHStarTheorem41_of_theorem41
    (hsection.theorem41Computable hroute) hmatch

/-- A statement-level squarecase Section 3 witness plus a computable abstract
induction route and order-polytope matching proves the final `h^*`
real-rootedness wrapper. -/
theorem orderPolytopeHStarRealRooted_of_squarecaseSection3ComputableStatement
    {hStar : SnakeWord → ℝ[X]} {model : SquarecaseRookModel}
    (hroute :
      ∀ P G : ℕ → ℝ[X],
        Theorem41InductionRouteComputableStatement model.snakePolynomial P G)
    (hsection : SquarecaseRookSection3Statement model)
    (hmatch :
      OrderPolytopeHStarMatchesNonNestingRook hStar model.snakePolynomial) :
    OrderPolytopeHStarRealRootedStatement hStar :=
  orderPolytopeHStarRealRooted_of_theorem41
    (theorem41_of_squarecaseSection3ComputableStatement hroute hsection)
    hmatch

/-- A statement-level squarecase Section 3 witness plus a computable abstract
induction route and order-polytope matching proves the final `h^*`
interlacing wrapper. -/
theorem orderPolytopeHStarInterlaces_of_squarecaseSection3ComputableStatement
    {hStar : SnakeWord → ℝ[X]} {model : SquarecaseRookModel}
    (hroute :
      ∀ P G : ℕ → ℝ[X],
        Theorem41InductionRouteComputableStatement model.snakePolynomial P G)
    (hsection : SquarecaseRookSection3Statement model)
    (hmatch :
      OrderPolytopeHStarMatchesNonNestingRook hStar model.snakePolynomial) :
    OrderPolytopeHStarInterlacesStatement hStar :=
  orderPolytopeHStarInterlaces_of_theorem41
    (theorem41_of_squarecaseSection3ComputableStatement hroute hsection)
    hmatch

/-- A statement-level squarecase Section 3 witness plus a computable abstract
induction route and order-polytope matching proves the full final `h^*`
Theorem 4.1 wrapper. -/
theorem orderPolytopeHStarTheorem41_of_squarecaseSection3ComputableStatement
    {hStar : SnakeWord → ℝ[X]} {model : SquarecaseRookModel}
    (hroute :
      ∀ P G : ℕ → ℝ[X],
        Theorem41InductionRouteComputableStatement model.snakePolynomial P G)
    (hsection : SquarecaseRookSection3Statement model)
    (hmatch :
      OrderPolytopeHStarMatchesNonNestingRook hStar model.snakePolynomial) :
    OrderPolytopeHStarTheorem41Statement hStar :=
  orderPolytopeHStarTheorem41_of_theorem41
    (theorem41_of_squarecaseSection3ComputableStatement hroute hsection)
    hmatch

end GeneralizedSnakePosets
end RealRooted
