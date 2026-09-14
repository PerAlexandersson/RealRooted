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

/-- Replacing one `(0,2)` pair by `(1,0)`, while keeping the prefix and suffix
fixed, swaps the corresponding final adjacent labels. -/
theorem inverseWord_eq_map_swap_of_pair {h j : Nat}
    {c d : DecoCode h} (hjLower : 2 ≤ j) (hjBound : j + 1 < h)
    (hprefix : d.entryList.take j = c.entryList.take j)
    (hsuffix : d.entryList.drop (j + 2) = c.entryList.drop (j + 2))
    (hdj : d ⟨j, by lia⟩ = 1) (hdSucc : d ⟨j + 1, hjBound⟩ = 0)
    (hcj : c ⟨j, by lia⟩ = 0) (hcSucc : c ⟨j + 1, hjBound⟩ = 2) :
    d.inverseWord =
      c.inverseWord.map (Equiv.swap (h - (j + 1)) (h - j)) := by
  have hprefixLength : j ≤ h := by lia
  have hprefixNonempty : c.inverseWordPrefix j ≠ [] := by
    intro hnil
    have hlength := c.length_inverseWordPrefix hprefixLength
    rw [hnil] at hlength
    simp only [List.length_nil] at hlength
    lia
  obtain ⟨a, w, hpref⟩ := List.exists_cons_of_ne_nil hprefixNonempty
  have ha : 0 < a := by
    have hpos := c.inverseWordPrefix_isPositive j
    rw [hpref] at hpos
    exact hpos a (by simp)
  have hw : ∀ x ∈ w, 0 < x := by
    have hpos := c.inverseWordPrefix_isPositive j
    rw [hpref] at hpos
    intro x hx
    exact hpos x (by simp [hx])
  rw [d.inverseWord_eq_decodeFrom_take_pair_drop j hjBound,
    c.inverseWord_eq_decodeFrom_take_pair_drop j hjBound]
  rw [hdj, hdSucc, hcj, hcSucc]
  have hprefixWord : d.inverseWordPrefix j = c.inverseWordPrefix j := by
    simp only [inverseWordPrefix]
    rw [hprefix]
  rw [hprefixWord, hpref, hsuffix]
  rw [MinimumInsertionWord.decodeFrom_exceptional_pair_eq_map_swap
    (c.entryList.drop (j + 2)) a w ha hw]
  have hsuffixLength : (c.entryList.drop (j + 2)).length = h - (j + 2) := by
    simp [length_entryList]
  have hleft : 1 + (c.entryList.drop (j + 2)).length = h - (j + 1) := by
    rw [hsuffixLength]
    lia
  have hright : 2 + (c.entryList.drop (j + 2)).length = h - j := by
    rw [hsuffixLength]
    lia
  rw [hleft, hright]

/-- The same local `(0,2)` to `(1,0)` replacement preserves every adjacent
comparison in the decoded inverse word. -/
theorem inverseWord_comparisonWord_eq_of_pair {h j : Nat}
    {c d : DecoCode h} (hjLower : 2 ≤ j) (hjBound : j + 1 < h)
    (hprefix : d.entryList.take j = c.entryList.take j)
    (hsuffix : d.entryList.drop (j + 2) = c.entryList.drop (j + 2))
    (hdj : d ⟨j, by lia⟩ = 1) (hdSucc : d ⟨j + 1, hjBound⟩ = 0)
    (hcj : c ⟨j, by lia⟩ = 0) (hcSucc : c ⟨j + 1, hjBound⟩ = 2) :
    MinimumInsertionWord.comparisonWord d.inverseWord =
      MinimumInsertionWord.comparisonWord c.inverseWord := by
  have hprefixLength : j ≤ h := by lia
  have hprefixNonempty : c.inverseWordPrefix j ≠ [] := by
    intro hnil
    have hlength := c.length_inverseWordPrefix hprefixLength
    rw [hnil] at hlength
    simp only [List.length_nil] at hlength
    lia
  obtain ⟨a, w, hpref⟩ := List.exists_cons_of_ne_nil hprefixNonempty
  have ha : 0 < a := by
    have hpos := c.inverseWordPrefix_isPositive j
    rw [hpref] at hpos
    exact hpos a (by simp)
  have hw : ∀ x ∈ w, 0 < x := by
    have hpos := c.inverseWordPrefix_isPositive j
    rw [hpref] at hpos
    intro x hx
    exact hpos x (by simp [hx])
  have hprefLength : (a :: w).length = j := by
    rw [← hpref]
    exact c.length_inverseWordPrefix hprefixLength
  rw [d.inverseWord_eq_decodeFrom_take_pair_drop j hjBound,
    c.inverseWord_eq_decodeFrom_take_pair_drop j hjBound]
  rw [hdj, hdSucc, hcj, hcSucc]
  have hprefixWord : d.inverseWordPrefix j = c.inverseWordPrefix j := by
    simp only [inverseWordPrefix]
    rw [hprefix]
  rw [hprefixWord, hpref, hsuffix]
  apply MinimumInsertionWord.comparisonWord_decodeFrom_congr
  · exact MinimumInsertionWord.isPositive_step 0
      (MinimumInsertionWord.step 1 (a :: w))
  · exact MinimumInsertionWord.isPositive_step 2
      (MinimumInsertionWord.step 0 (a :: w))
  · rw [MinimumInsertionWord.step_exceptional_pair,
      MinimumInsertionWord.step_normal_pair]
    simp
  · exact MinimumInsertionWord.comparisonWord_step_pair a w ha hw
  · have hsuffixValid := c.validFrom_entryList.drop
        (k := j + 2) (by simp [length_entryList]; lia)
    rw [MinimumInsertionWord.step_exceptional_pair]
    simp only [List.length_cons, List.length_map]
    have hwLength : w.length + 1 = j := by simpa using hprefLength
    rw [show w.length + 1 + 1 + 1 = 0 + (j + 2) by lia]
    exact hsuffixValid

end RealRooted.Applications.OEIS.DecoCode

namespace RealRooted.Applications.OEIS.DecoNormalizedCode.Decoration

/-- The decoration selecting one eligible normal pair. -/
noncomputable def singleton {h : Nat} {c : DecoNormalizedCode h}
    (j : Fin h) (hj : c.Eligible j) : Decoration c where
  starts := {j}
  starts_subset := by
    intro i hi
    simp only [Finset.mem_singleton] at hi
    subst i
    exact DecoNormalizedCode.mem_eligibleStarts.mpr hj

@[simp] theorem singleton_starts {h : Nat} {c : DecoNormalizedCode h}
    (j : Fin h) (hj : c.Eligible j) :
    (singleton j hj).starts = {j} := rfl

@[simp] theorem singleton_exceptionalize_apply {h : Nat}
    {c : DecoNormalizedCode h} (j : Fin h) (hj : c.Eligible j)
    (k : Fin h) :
    (singleton j hj).exceptionalize k =
      if k = j then 1 else if j.1 + 1 = k.1 then 0 else c k := by
  simp [singleton, exceptionalize]

end RealRooted.Applications.OEIS.DecoNormalizedCode.Decoration

namespace RealRooted.Applications.OEIS

open DecoNormalizedCode

/-- A singleton decoration does not change entries before its selected pair. -/
theorem singleton_entryList_take_eq {h : Nat} {c : DecoNormalizedCode h}
    (j : Fin h) (hj : c.Eligible j) :
    (Decoration.singleton j hj).exceptionalize.entryList.take j.1 =
      c.toDecoCode.entryList.take j.1 := by
  apply List.ext_get
  · simp [DecoCode.length_entryList]
  · intro k hkLeft hkRight
    simp only [List.get_eq_getElem, List.getElem_take]
    simp only [DecoCode.entryList, List.getElem_ofFn]
    have hk : k < j.1 := by simpa using hkLeft
    let kFin : Fin h := ⟨k, hk.trans j.2⟩
    change (Decoration.singleton j hj).exceptionalize kFin = c kFin
    rw [Decoration.singleton_exceptionalize_apply]
    have hkj : kFin ≠ j := by
      intro heq
      exact (Nat.ne_of_lt hk) (congrArg Fin.val heq)
    have hpred : j.1 + 1 ≠ kFin.1 := by simp [kFin]; lia
    simp [hkj, hpred]

/-- A singleton decoration does not change entries after its selected pair. -/
theorem singleton_entryList_drop_eq {h : Nat} {c : DecoNormalizedCode h}
    (j : Fin h) (hj : c.Eligible j) :
    (Decoration.singleton j hj).exceptionalize.entryList.drop (j.1 + 2) =
      c.toDecoCode.entryList.drop (j.1 + 2) := by
  apply List.ext_get
  · simp [DecoCode.length_entryList]
  · intro k hkLeft hkRight
    simp only [List.get_eq_getElem, List.getElem_drop]
    simp only [DecoCode.entryList, List.getElem_ofFn]
    have hjBound : j.1 + 1 < h := hj.2.choose
    have hk : k < h - (j.1 + 2) := by
      simpa [DecoCode.length_entryList] using hkLeft
    let kFin : Fin h := ⟨j.1 + 2 + k, by lia⟩
    change (Decoration.singleton j hj).exceptionalize kFin = c kFin
    rw [Decoration.singleton_exceptionalize_apply]
    have hkj : kFin ≠ j := by
      intro heq
      have := congrArg Fin.val heq
      simp only [kFin] at this
      lia
    have hpred : j.1 + 1 ≠ kFin.1 := by
      change j.1 + 1 ≠ j.1 + 2 + k
      lia
    simp [hkj, hpred]

/-- Replacing one eligible `(0,2)` pair by `(1,0)` swaps the corresponding
final adjacent labels. The one-based start is `j.1 + 1`. -/
theorem singleton_inverseWord_eq_map_swap {h : Nat}
    {c : DecoNormalizedCode h} (j : Fin h) (hj : c.Eligible j) :
    (Decoration.singleton j hj).exceptionalize.inverseWord =
      c.toDecoCode.inverseWord.map
        (Equiv.swap (h - (j.1 + 1)) (h - j.1)) := by
  rcases hj with ⟨hjLower, hjBound, hjZero, hjTwo⟩
  apply DecoCode.inverseWord_eq_map_swap_of_pair hjLower hjBound
  · exact singleton_entryList_take_eq j
      ⟨hjLower, hjBound, hjZero, hjTwo⟩
  · exact singleton_entryList_drop_eq j
      ⟨hjLower, hjBound, hjZero, hjTwo⟩
  · rw [Decoration.singleton_exceptionalize_apply]
    simp
  · rw [Decoration.singleton_exceptionalize_apply]
    have hne : (⟨j.1 + 1, hjBound⟩ : Fin h) ≠ j := by
      intro heq
      have heqVal := congrArg Fin.val heq
      simp only at heqVal
      lia
    simp [hne]
  · exact hjZero
  · exact hjTwo

/-- Exceptionalizing one eligible pair preserves the ascent/descent word of
the decoded inverse word. -/
theorem singleton_inverseWord_comparisonWord_eq {h : Nat}
    {c : DecoNormalizedCode h} (j : Fin h) (hj : c.Eligible j) :
    MinimumInsertionWord.comparisonWord
        ((Decoration.singleton j hj).exceptionalize.inverseWord) =
      MinimumInsertionWord.comparisonWord c.toDecoCode.inverseWord := by
  rcases hj with ⟨hjLower, hjBound, hjZero, hjTwo⟩
  apply DecoCode.inverseWord_comparisonWord_eq_of_pair hjLower hjBound
  · exact singleton_entryList_take_eq j
      ⟨hjLower, hjBound, hjZero, hjTwo⟩
  · exact singleton_entryList_drop_eq j
      ⟨hjLower, hjBound, hjZero, hjTwo⟩
  · rw [Decoration.singleton_exceptionalize_apply]
    simp
  · rw [Decoration.singleton_exceptionalize_apply]
    have hne : (⟨j.1 + 1, hjBound⟩ : Fin h) ≠ j := by
      intro heq
      have heqVal := congrArg Fin.val heq
      simp only at heqVal
      lia
    simp [hne]
  · exact hjZero
  · exact hjTwo

end RealRooted.Applications.OEIS
