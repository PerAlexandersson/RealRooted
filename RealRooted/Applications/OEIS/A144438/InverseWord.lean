import RealRooted.Applications.OEIS.A144438.NormalizedCode
import RealRooted.Combinatorics.MinimumInsertionWord
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.TakeDrop

/-!
# Inverse words of chronological deco codes

The chronological code is exactly the sequence of new-minimum insertion
positions for the inverse permutation.  This file specializes the generic
decoder and records its decomposition around any two successive rows.
-/

namespace RealRooted.Applications.OEIS.DecoCode

/-- The chronological entries as a list. -/
def entryList {h : Nat} (c : DecoCode h) : List Nat := List.ofFn c

@[simp] theorem length_entryList {h : Nat} (c : DecoCode h) :
    c.entryList.length = h := by
  simp [entryList]

@[simp] theorem get_entryList {h : Nat} (c : DecoCode h)
    (i : Fin c.entryList.length) :
    c.entryList.get i = c ⟨i.1, by simpa using i.2⟩ := by
  simp [entryList]

/-- Every chronological deco code satisfies the insertion decoder's bounds. -/
theorem validFrom_entryList {h : Nat} (c : DecoCode h) :
    MinimumInsertionWord.ValidFrom 0 c.entryList := by
  rw [MinimumInsertionWord.validFrom_iff_get]
  intro i
  rw [get_entryList]
  have hlt := c.entry_lt ⟨i.1, by simpa using i.2⟩
  lia

/-- The inverse word obtained by chronological new-minimum insertion. -/
def inverseWord {h : Nat} (c : DecoCode h) : List Nat :=
  MinimumInsertionWord.decode c.entryList

/-- The inverse word after only the first `j` chronological entries. -/
def inverseWordPrefix {h : Nat} (c : DecoCode h) (j : Nat) : List Nat :=
  MinimumInsertionWord.decode (c.entryList.take j)

@[simp] theorem length_inverseWord {h : Nat} (c : DecoCode h) :
    c.inverseWord.length = h := by
  rw [inverseWord, MinimumInsertionWord.length_decode c.validFrom_entryList,
    length_entryList]

/-- Every label in a deco inverse word is positive. -/
theorem inverseWord_isPositive {h : Nat} (c : DecoCode h) :
    MinimumInsertionWord.IsPositive c.inverseWord := by
  exact MinimumInsertionWord.IsPositive.decode c.entryList

@[simp] theorem length_inverseWordPrefix {h : Nat} (c : DecoCode h)
    {j : Nat} (hj : j ≤ h) :
    (c.inverseWordPrefix j).length = j := by
  rw [inverseWordPrefix, MinimumInsertionWord.length_decode
    (c.validFrom_entryList.take j)]
  simp [hj]

/-- Every label already constructed in a chronological prefix is positive. -/
theorem inverseWordPrefix_isPositive {h : Nat} (c : DecoCode h) (j : Nat) :
    MinimumInsertionWord.IsPositive (c.inverseWordPrefix j) := by
  exact MinimumInsertionWord.IsPositive.decode (c.entryList.take j)

/-- Split the chronological entries around two successive positions. -/
theorem entryList_eq_take_pair_drop {h : Nat} (c : DecoCode h)
    (j : Nat) (hj : j + 1 < h) :
    c.entryList =
      c.entryList.take j ++
        [c ⟨j, by lia⟩, c ⟨j + 1, hj⟩] ++
          c.entryList.drop (j + 2) := by
  have hj0 : j < c.entryList.length := by simp; lia
  have hj1 : j + 1 < c.entryList.length := by simpa using hj
  have hjEntry : c.entryList[j] = c ⟨j, by lia⟩ := by
    simp [entryList]
  have hj1Entry : c.entryList[j + 1] = c ⟨j + 1, hj⟩ := by
    simp [entryList]
  calc
    c.entryList = c.entryList.take (j + 2) ++
        c.entryList.drop (j + 2) := (List.take_append_drop _ _).symm
    _ = (c.entryList.take (j + 1) ++ [c.entryList[j + 1]]) ++
        c.entryList.drop (j + 2) := by
          rw [List.take_concat_get' c.entryList (j + 1) hj1]
    _ = ((c.entryList.take j ++ [c.entryList[j]]) ++
          [c.entryList[j + 1]]) ++ c.entryList.drop (j + 2) := by
          rw [List.take_concat_get' c.entryList j hj0]
    _ = c.entryList.take j ++ [c ⟨j, by lia⟩, c ⟨j + 1, hj⟩] ++
        c.entryList.drop (j + 2) := by
          rw [hjEntry, hj1Entry]
          simp only [List.append_assoc, List.singleton_append]

/-- Decode a chronological code as its prefix word, the two selected
insertions, and the remaining suffix. -/
theorem inverseWord_eq_decodeFrom_take_pair_drop {h : Nat} (c : DecoCode h)
    (j : Nat) (hj : j + 1 < h) :
    c.inverseWord =
      MinimumInsertionWord.decodeFrom
        (MinimumInsertionWord.step (c ⟨j + 1, hj⟩)
          (MinimumInsertionWord.step (c ⟨j, by lia⟩)
            (c.inverseWordPrefix j)))
        (c.entryList.drop (j + 2)) := by
  unfold inverseWord
  conv_lhs => rw [entryList_eq_take_pair_drop c j hj]
  simp only [List.append_assoc, inverseWordPrefix,
    MinimumInsertionWord.decode,
    MinimumInsertionWord.decodeFrom_append,
    MinimumInsertionWord.decodeFrom_cons,
    MinimumInsertionWord.decodeFrom_nil]

end RealRooted.Applications.OEIS.DecoCode
