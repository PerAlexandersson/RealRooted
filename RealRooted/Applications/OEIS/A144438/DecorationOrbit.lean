import RealRooted.Applications.OEIS.A144438.InverseWord
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Fintype.Powerset

/-!
# Finite decoration swap orbits

Eligible chronological `(0,2)` pairs have disjoint final adjacent-label
supports. Consequently their swaps commute, and exceptionalizing an arbitrary
finite decoration applies exactly the corresponding swap orbit while
preserving the inverse word's ascent/descent comparisons.
-/

namespace RealRooted.MinimumInsertionWord

theorem swap_comm_of_disjoint (a b c d : Nat)
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    Function.Commute (Equiv.swap a b) (Equiv.swap c d) := by
  intro n
  by_cases hnc : n = c
  · subst n
    simp [Equiv.swap_apply_def, hac, had, hbc, hbd, Ne.symm]
  · by_cases hnd : n = d
    · subst n
      simp [Equiv.swap_apply_def, hac, had, hbc, hbd, Ne.symm]
    · by_cases hna : n = a
      · subst n
        simp [Equiv.swap_apply_def, hac, had, hbc, hbd]
      · by_cases hnb : n = b
        · subst n
          simp [Equiv.swap_apply_def, hac, had, hbc, hbd]
        · simp [Equiv.swap_apply_def, hnc, hnd, hna, hnb]

end RealRooted.MinimumInsertionWord

namespace RealRooted.Applications.OEIS.DecoNormalizedCode

/-- An eligible start bundled with its eligibility proof. -/
abbrev EligibleStart {h : Nat} (c : DecoNormalizedCode h) :=
  {j : Fin h // c.Eligible j}

noncomputable instance instFintypeEligibleStart {h : Nat}
    (c : DecoNormalizedCode h) : Fintype (EligibleStart c) := by
  classical
  exact Fintype.ofFinite (EligibleStart c)

/-- The final adjacent-label swap associated with a chronological start. -/
def finalSwap (h : Nat) (j : Fin h) : Equiv.Perm Nat :=
  Equiv.swap (h - (j.1 + 1)) (h - j.1)

/-- Apply one final adjacent-label swap to a word. -/
def swapWord (h : Nat) (j : Fin h) (w : List Nat) : List Nat :=
  w.map (finalSwap h j)

/-- Distinct eligible chronological pairs have disjoint final-label supports. -/
theorem finalSwap_support_disjoint {h : Nat} {c : DecoNormalizedCode h}
    {i j : Fin h} (hi : c.Eligible i) (hj : c.Eligible j) (hij : i ≠ j) :
    h - (i.1 + 1) ≠ h - (j.1 + 1) ∧
      h - (i.1 + 1) ≠ h - j.1 ∧
      h - i.1 ≠ h - (j.1 + 1) ∧
      h - i.1 ≠ h - j.1 := by
  have hiSuccNe : i.1 + 1 ≠ j.1 := eligible_succ_ne hi hj
  have hjSuccNe : j.1 + 1 ≠ i.1 := eligible_succ_ne hj hi
  rcases hi with ⟨_, hiBound, _, _⟩
  rcases hj with ⟨_, hjBound, _, _⟩
  have hijVal : i.1 ≠ j.1 := fun heq => hij (Fin.ext heq)
  constructor
  · lia
  constructor
  · lia
  constructor <;> lia

/-- Final-label swaps belonging to eligible starts commute. -/
theorem finalSwap_comm {h : Nat} {c : DecoNormalizedCode h}
    (i j : EligibleStart c) :
    Function.Commute (finalSwap h i.1) (finalSwap h j.1) := by
  by_cases hij : i.1 = j.1
  · have hSubtype : i = j := Subtype.ext hij
    subst j
    intro n
    rfl
  · rcases finalSwap_support_disjoint i.2 j.2 hij with
      ⟨hac, had, hbc, hbd⟩
    exact MinimumInsertionWord.swap_comm_of_disjoint _ _ _ _
      hac had hbc hbd

/-- Eligible final-label swaps commute on whole words. -/
theorem swapWord_comm {h : Nat} {c : DecoNormalizedCode h}
    (i j : EligibleStart c) :
    Function.Commute (swapWord h i.1) (swapWord h j.1) := by
  intro w
  simp only [swapWord, List.map_map]
  apply List.map_congr_left
  intro x hx
  exact finalSwap_comm i j x

instance eligibleSwapWord_leftCommutative {h : Nat}
    {c : DecoNormalizedCode h} :
    LeftCommutative
      (fun (j : EligibleStart c) (w : List Nat) => swapWord h j.1 w) where
  left_comm i j w := swapWord_comm i j w

/-- Apply the commuting swaps indexed by a finite eligible-start set. -/
noncomputable def applySwaps {h : Nat} {c : DecoNormalizedCode h}
    (s : Finset (EligibleStart c)) (w : List Nat) : List Nat :=
  s.toList.foldr (fun j word => swapWord h j.1 word) w

@[simp] theorem applySwaps_empty {h : Nat} {c : DecoNormalizedCode h}
    (w : List Nat) : applySwaps (∅ : Finset (EligibleStart c)) w = w := by
  simp [applySwaps]

theorem applySwaps_insert {h : Nat} {c : DecoNormalizedCode h}
    {s : Finset (EligibleStart c)} {j : EligibleStart c} (hj : j ∉ s)
    (w : List Nat) :
    applySwaps (insert j s) w = swapWord h j.1 (applySwaps s w) := by
  unfold applySwaps
  rw [(Finset.toList_insert hj).foldr_eq]
  rfl

namespace Decoration

def eligibleStartValEmbedding {h : Nat} {c : DecoNormalizedCode h} :
    EligibleStart c ↪ Fin h where
  toFun := Subtype.val
  inj' := Subtype.val_injective

/-- A decoration represented by a finite set of bundled eligible starts. -/
noncomputable def ofEligibleFinset {h : Nat} {c : DecoNormalizedCode h}
    (s : Finset (EligibleStart c)) : Decoration c where
  starts := s.map eligibleStartValEmbedding
  starts_subset := by
    intro j hj
    simp only [Finset.mem_map] at hj
    obtain ⟨i, hi, rfl⟩ := hj
    exact mem_eligibleStarts.mpr i.2

@[simp] theorem ofEligibleFinset_starts {h : Nat}
    {c : DecoNormalizedCode h} (s : Finset (EligibleStart c)) :
    (ofEligibleFinset s).starts = s.map eligibleStartValEmbedding := rfl

@[simp] theorem mem_ofEligibleFinset_starts {h : Nat}
    {c : DecoNormalizedCode h} {s : Finset (EligibleStart c)}
    (j : EligibleStart c) :
    j.1 ∈ (ofEligibleFinset s).starts ↔ j ∈ s := by
  rw [ofEligibleFinset_starts, Finset.mem_map]
  constructor
  · rintro ⟨i, hi, hij⟩
    have hSubtype : i = j := Subtype.ext hij
    simpa [hSubtype] using hi
  · intro hj
    exact ⟨j, hj, rfl⟩

theorem insert_exceptionalize_apply_of_ne {h : Nat}
    {c : DecoNormalizedCode h} {s : Finset (EligibleStart c)}
    {j : EligibleStart c} {k : Fin h} (hkj : k ≠ j.1)
    (hksucc : j.1.1 + 1 ≠ k.1) :
    (ofEligibleFinset (insert j s)).exceptionalize k =
      (ofEligibleFinset s).exceptionalize k := by
  let D := ofEligibleFinset s
  let E := ofEligibleFinset (insert j s)
  have hstarts : E.starts = insert j.1 D.starts := by
    change (insert j s).map eligibleStartValEmbedding =
      insert j.1 (s.map eligibleStartValEmbedding)
    rw [Finset.map_insert]
    rfl
  have hmem : k ∈ E.starts ↔ k ∈ D.starts := by
    rw [hstarts]
    simp [hkj]
  have hprevious :
      (∃ i ∈ E.starts, i.1 + 1 = k.1) ↔
        ∃ i ∈ D.starts, i.1 + 1 = k.1 := by
    rw [hstarts]
    simp [hksucc]
  by_cases hk : k ∈ D.starts
  · rw [exceptionalize_apply_of_mem D hk,
      exceptionalize_apply_of_mem E (hmem.mpr hk)]
  · by_cases hp : ∃ i ∈ D.starts, i.1 + 1 = k.1
    · rw [exceptionalize_apply_of_predecessor D hk hp,
        exceptionalize_apply_of_predecessor E
          (fun hkE => hk (hmem.mp hkE)) (hprevious.mpr hp)]
    · rw [exceptionalize_apply_of_not_mem_of_no_predecessor D hk hp,
        exceptionalize_apply_of_not_mem_of_no_predecessor E
          (fun hkE => hk (hmem.mp hkE)) (fun hpE => hp (hprevious.mp hpE))]

theorem insert_exceptionalize_pair {h : Nat}
    {c : DecoNormalizedCode h} {s : Finset (EligibleStart c)}
    {j : EligibleStart c} (hj : j ∉ s) :
    let hjBound := j.2.2.choose
    (ofEligibleFinset (insert j s)).exceptionalize
          ⟨j.1.1, by exact j.1.2⟩ = 1 ∧
      (ofEligibleFinset (insert j s)).exceptionalize
          ⟨j.1.1 + 1, hjBound⟩ = 0 ∧
      (ofEligibleFinset s).exceptionalize
          ⟨j.1.1, by exact j.1.2⟩ = 0 ∧
      (ofEligibleFinset s).exceptionalize
          ⟨j.1.1 + 1, hjBound⟩ = 2 := by
  let D := ofEligibleFinset s
  let E := ofEligibleFinset (insert j s)
  have hjMemE : j.1 ∈ E.starts := by
    change j.1 ∈ (ofEligibleFinset (insert j s)).starts
    rw [mem_ofEligibleFinset_starts]
    simp
  have hjNotMemD : j.1 ∉ D.starts := by
    change j.1 ∉ (ofEligibleFinset s).starts
    rw [mem_ofEligibleFinset_starts]
    exact hj
  have hjNoPreviousD : ¬∃ i ∈ D.starts, i.1 + 1 = j.1.1 := by
    rintro ⟨i, hi, hij⟩
    have hiEligible := mem_eligibleStarts.mp (D.starts_subset hi)
    exact eligible_succ_ne hiEligible j.2 hij
  have hsuccNotMemE :
      (⟨j.1.1 + 1, j.2.2.choose⟩ : Fin h) ∉ E.starts := by
    intro hmem
    have hsuccEligible := mem_eligibleStarts.mp (E.starts_subset hmem)
    exact eligible_succ_ne j.2 hsuccEligible rfl
  have hsuccNotMemD :
      (⟨j.1.1 + 1, j.2.2.choose⟩ : Fin h) ∉ D.starts := by
    exact fun hmem => hsuccNotMemE (by
      change (⟨j.1.1 + 1, j.2.2.choose⟩ : Fin h) ∈
        (ofEligibleFinset (insert j s)).starts
      change (⟨j.1.1 + 1, j.2.2.choose⟩ : Fin h) ∈
        (insert j s).map eligibleStartValEmbedding
      rw [Finset.map_insert]
      exact Finset.mem_insert_of_mem hmem)
  have hsuccPreviousE :
      ∃ i ∈ E.starts, i.1 + 1 = j.1.1 + 1 := ⟨j.1, hjMemE, rfl⟩
  have hsuccNoPreviousD :
      ¬∃ i ∈ D.starts, i.1 + 1 = j.1.1 + 1 := by
    rintro ⟨i, hi, hij⟩
    have hiMap : i ∈ s.map eligibleStartValEmbedding := by
      exact hi
    rw [Finset.mem_map] at hiMap
    obtain ⟨a, ha, hai⟩ := hiMap
    have haiVal : a.1.1 = i.1 := by
      exact congrArg Fin.val hai
    have haVal : a.1.1 = j.1.1 := by
      change i.1 + 1 = j.1.1 + 1 at hij
      lia
    have hajFin : a.1 = j.1 := Fin.ext haVal
    have haj : a = j := Subtype.ext hajFin
    exact hj (haj ▸ ha)
  refine ⟨exceptionalize_apply_of_mem E hjMemE, ?_, ?_, ?_⟩
  · exact exceptionalize_apply_of_predecessor E hsuccNotMemE
      hsuccPreviousE
  · rw [exceptionalize_apply_of_not_mem_of_no_predecessor D hjNotMemD
      hjNoPreviousD]
    exact j.2.2.choose_spec.1
  · rw [exceptionalize_apply_of_not_mem_of_no_predecessor D hsuccNotMemD
      hsuccNoPreviousD]
    exact j.2.2.choose_spec.2

theorem insert_entryList_take_eq {h : Nat}
    {c : DecoNormalizedCode h} {s : Finset (EligibleStart c)}
    {j : EligibleStart c} :
    (ofEligibleFinset (insert j s)).exceptionalize.entryList.take j.1.1 =
      (ofEligibleFinset s).exceptionalize.entryList.take j.1.1 := by
  apply List.ext_get
  · simp [DecoCode.length_entryList]
  · intro k hkLeft hkRight
    simp only [List.get_eq_getElem, List.getElem_take]
    simp only [DecoCode.entryList, List.getElem_ofFn]
    have hk : k < j.1.1 := by simpa using hkLeft
    let kFin : Fin h := ⟨k, hk.trans j.1.2⟩
    apply insert_exceptionalize_apply_of_ne
    · intro heq
      exact (Nat.ne_of_lt hk) (congrArg Fin.val heq)
    · change j.1.1 + 1 ≠ k
      lia

theorem insert_entryList_drop_eq {h : Nat}
    {c : DecoNormalizedCode h} {s : Finset (EligibleStart c)}
    {j : EligibleStart c} :
    (ofEligibleFinset (insert j s)).exceptionalize.entryList.drop
        (j.1.1 + 2) =
      (ofEligibleFinset s).exceptionalize.entryList.drop (j.1.1 + 2) := by
  apply List.ext_get
  · simp [DecoCode.length_entryList]
  · intro k hkLeft hkRight
    simp only [List.get_eq_getElem, List.getElem_drop]
    simp only [DecoCode.entryList, List.getElem_ofFn]
    have hjBound := j.2.2.choose
    have hk : k < h - (j.1.1 + 2) := by
      simpa [DecoCode.length_entryList] using hkLeft
    let kFin : Fin h := ⟨j.1.1 + 2 + k, by lia⟩
    apply insert_exceptionalize_apply_of_ne
    · intro heq
      have heqVal := congrArg Fin.val heq
      change j.1.1 + 2 + k = j.1.1 at heqVal
      lia
    · change j.1.1 + 1 ≠ j.1.1 + 2 + k
      lia

/-- Adding one selected start applies exactly its final adjacent-label swap. -/
theorem insert_inverseWord_eq_swapWord {h : Nat}
    {c : DecoNormalizedCode h} {s : Finset (EligibleStart c)}
    {j : EligibleStart c} (hj : j ∉ s) :
    (ofEligibleFinset (insert j s)).exceptionalize.inverseWord =
      swapWord h j.1 (ofEligibleFinset s).exceptionalize.inverseWord := by
  rcases insert_exceptionalize_pair hj with ⟨hEj, hESucc, hDj, hDSucc⟩
  exact DecoCode.inverseWord_eq_map_swap_of_pair j.2.1 j.2.2.choose
    insert_entryList_take_eq insert_entryList_drop_eq
    hEj hESucc hDj hDSucc

/-- Adding one selected start preserves the complete comparison word. -/
theorem insert_inverseWord_comparisonWord_eq {h : Nat}
    {c : DecoNormalizedCode h} {s : Finset (EligibleStart c)}
    {j : EligibleStart c} (hj : j ∉ s) :
    MinimumInsertionWord.comparisonWord
        (ofEligibleFinset (insert j s)).exceptionalize.inverseWord =
      MinimumInsertionWord.comparisonWord
        (ofEligibleFinset s).exceptionalize.inverseWord := by
  rcases insert_exceptionalize_pair hj with ⟨hEj, hESucc, hDj, hDSucc⟩
  exact DecoCode.inverseWord_comparisonWord_eq_of_pair j.2.1 j.2.2.choose
    insert_entryList_take_eq insert_entryList_drop_eq
    hEj hESucc hDj hDSucc

@[simp] theorem ofEligibleFinset_empty_exceptionalize {h : Nat}
    {c : DecoNormalizedCode h} :
    (ofEligibleFinset (∅ : Finset (EligibleStart c))).exceptionalize =
      c.toDecoCode := by
  ext k
  simp [exceptionalize, ofEligibleFinset]

theorem ofEligibleFinset_inverseWord_eq_applySwaps {h : Nat}
    {c : DecoNormalizedCode h} (s : Finset (EligibleStart c)) :
    (ofEligibleFinset s).exceptionalize.inverseWord =
      applySwaps s c.toDecoCode.inverseWord := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert j s hj ih =>
      rw [insert_inverseWord_eq_swapWord hj, ih, applySwaps_insert hj]

theorem ofEligibleFinset_inverseWord_comparisonWord_eq {h : Nat}
    {c : DecoNormalizedCode h} (s : Finset (EligibleStart c)) :
    MinimumInsertionWord.comparisonWord
        (ofEligibleFinset s).exceptionalize.inverseWord =
      MinimumInsertionWord.comparisonWord c.toDecoCode.inverseWord := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert j s hj ih =>
      exact (insert_inverseWord_comparisonWord_eq hj).trans ih

@[ext] theorem ext {h : Nat} {c : DecoNormalizedCode h}
    {D E : Decoration c} (hstarts : D.starts = E.starts) : D = E := by
  cases D
  cases E
  simp_all

/-- The selected starts, bundled with the eligibility supplied by the
decoration. -/
noncomputable def eligibleStartEmbedding {h : Nat}
    {c : DecoNormalizedCode h} (D : Decoration c) :
    {j // j ∈ D.starts} ↪ EligibleStart c where
  toFun j := ⟨j.1, mem_eligibleStarts.mp (D.starts_subset j.2)⟩
  inj' := by
    intro i j hij
    apply Subtype.ext
    exact congrArg (fun z : EligibleStart c => z.1) hij

noncomputable def eligibleFinset {h : Nat} {c : DecoNormalizedCode h}
    (D : Decoration c) : Finset (EligibleStart c) :=
  D.starts.attach.map D.eligibleStartEmbedding

@[simp] theorem mem_eligibleFinset {h : Nat} {c : DecoNormalizedCode h}
    (D : Decoration c) (j : EligibleStart c) :
    j ∈ D.eligibleFinset ↔ j.1 ∈ D.starts := by
  rw [eligibleFinset, Finset.mem_map]
  constructor
  · rintro ⟨i, hi, hij⟩
    have hijVal : i.1 = j.1 := congrArg Subtype.val hij
    rw [← hijVal]
    exact i.2
  · intro hj
    let i : {k // k ∈ D.starts} := ⟨j.1, hj⟩
    refine ⟨i, by simp [i], ?_⟩
    apply Subtype.ext
    rfl

@[simp] theorem ofEligibleFinset_eligibleFinset {h : Nat}
    {c : DecoNormalizedCode h} (D : Decoration c) :
    ofEligibleFinset D.eligibleFinset = D := by
  apply ext
  ext k
  constructor
  · intro hk
    rw [ofEligibleFinset_starts, Finset.mem_map] at hk
    obtain ⟨j, hj, hjk⟩ := hk
    rw [mem_eligibleFinset] at hj
    have hjk' : j.1 = k := hjk
    rw [← hjk']
    exact hj
  · intro hk
    have hkEligible := mem_eligibleStarts.mp (D.starts_subset hk)
    let j : EligibleStart c := ⟨k, hkEligible⟩
    rw [ofEligibleFinset_starts, Finset.mem_map]
    have hj : j ∈ D.eligibleFinset := by
      apply (mem_eligibleFinset D j).mpr
      exact hk
    exact ⟨j, hj, rfl⟩

@[simp] theorem eligibleFinset_ofEligibleFinset {h : Nat}
    {c : DecoNormalizedCode h} (s : Finset (EligibleStart c)) :
    (ofEligibleFinset s).eligibleFinset = s := by
  ext j
  rw [mem_eligibleFinset, mem_ofEligibleFinset_starts]

/-- Decorations are canonically equivalent to finite subsets of the bundled
eligible starts. -/
noncomputable def equivEligibleFinset {h : Nat} (c : DecoNormalizedCode h) :
    Decoration c ≃ Finset (EligibleStart c) where
  toFun := eligibleFinset
  invFun := ofEligibleFinset
  left_inv := ofEligibleFinset_eligibleFinset
  right_inv := eligibleFinset_ofEligibleFinset

noncomputable instance instFintype {h : Nat} (c : DecoNormalizedCode h) :
    Fintype (Decoration c) := by
  classical
  exact Fintype.ofEquiv (Finset (EligibleStart c))
    (equivEligibleFinset c).symm

/-- Apply all final-label swaps selected by a decoration. -/
noncomputable def swapOrbit {h : Nat} {c : DecoNormalizedCode h}
    (D : Decoration c) (w : List Nat) : List Nat :=
  applySwaps D.eligibleFinset w

/-- A finite decoration acts on the normalized inverse word by precisely its
commuting family of final adjacent-label swaps. -/
theorem inverseWord_eq_swapOrbit {h : Nat} {c : DecoNormalizedCode h}
    (D : Decoration c) :
    D.exceptionalize.inverseWord = D.swapOrbit c.toDecoCode.inverseWord := by
  rw [swapOrbit, ← ofEligibleFinset_inverseWord_eq_applySwaps
    D.eligibleFinset, ofEligibleFinset_eligibleFinset]

/-- Every finite decoration preserves the complete ascent/descent comparison
word of the normalized inverse word. -/
theorem inverseWord_comparisonWord_eq {h : Nat} {c : DecoNormalizedCode h}
    (D : Decoration c) :
    MinimumInsertionWord.comparisonWord D.exceptionalize.inverseWord =
      MinimumInsertionWord.comparisonWord c.toDecoCode.inverseWord := by
  rw [← ofEligibleFinset_eligibleFinset D]
  exact ofEligibleFinset_inverseWord_comparisonWord_eq D.eligibleFinset

end Decoration

end RealRooted.Applications.OEIS.DecoNormalizedCode
