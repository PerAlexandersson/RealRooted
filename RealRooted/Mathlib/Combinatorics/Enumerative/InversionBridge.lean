import RealRooted.Mathlib.Combinatorics.Enumerative.PatternCount

/-!
# Occurrences of the pattern 21 are inversions

`List.patternCount_21_eq_inversionCount` identifies the number of occurrences of the pattern
`[1, 0]` in a word with its inversion count; for permutations, occurrences of `21` are inversions,
and occurrences of `12` and `21` together count all `n.choose 2` pairs.
-/

open Finset

namespace List

private theorem card_filter_get {α : Type*} [LinearOrder α] (l : List α)
    (p : α → Bool) :
    ((univ : Finset (Fin l.length)).filter (fun i => p (l.get i))).card =
      (l.filter p).length := by
  have hmap : (List.finRange l.length).map l.get = l := by
    change List.map l.get (List.ofFn (fun i : Fin l.length => i)) = l
    rw [List.map_ofFn]
    change List.ofFn l.get = l
    exact List.ofFn_get l
  have hfilter :
      ((List.finRange l.length).filter (fun i => p (l.get i))).length =
        (l.filter p).length := by
    calc
      ((List.finRange l.length).filter (fun i => p (l.get i))).length =
          (List.filter p ((List.finRange l.length).map l.get)).length := by
            rw [List.filter_map]
            simp only [List.length_map]
            apply congrArg List.length
            apply List.filter_congr
            intro i hi
            rfl
      _ = (l.filter p).length := by rw [hmap]
  have htofinset :
      ((List.finRange l.length).filter (fun i => p (l.get i))).toFinset =
        (univ : Finset (Fin l.length)).filter (fun i => p (l.get i)) := by
    rw [List.toFinset_filter, List.toFinset_finRange]
  rw [← htofinset]
  exact (List.toFinset_card_of_nodup
    ((List.nodup_finRange l.length).filter _)).trans hfilter

private theorem inversionCount_cons {α : Type*} [LinearOrder α] (a : α) (l : List α) :
    (a :: l).inversionCount =
      (l.filter (fun x => x < a)).length + l.inversionCount := by
  let s : Finset (Fin (a :: l).length × Fin (a :: l).length) :=
    (univ.product univ).filter fun p =>
      p.1 < p.2 ∧ (a :: l).get p.2 < (a :: l).get p.1
  have hsplit : s.card =
      (s.filter (fun p => p.1 = 0)).card +
        (s.filter (fun p => ¬p.1 = 0)).card := by
    symm
    exact Finset.card_filter_add_card_filter_not
      (fun p : Fin (a :: l).length × Fin (a :: l).length => p.1 = 0)
  have hzero :
      (s.filter (fun p => p.1 = 0)).card =
        ((univ : Finset (Fin l.length)).filter
          (fun i => decide (l.get i < a))).card := by
    refine Finset.card_bij' (s := s.filter (fun p => p.1 = 0))
      (t := (univ : Finset (Fin l.length)).filter
        (fun i => decide (l.get i < a)))
      (fun (p : Fin (a :: l).length × Fin (a :: l).length) hp =>
        p.2.pred ?_)
      (fun (i : Fin l.length) hi => (0, i.succ)) ?_ ?_ ?_ ?_
    · have hp := (Finset.mem_filter.1 hp).1
      have hlt := (Finset.mem_filter.1 hp).2.1
      intro hzero
      rw [hzero] at hlt
      simp at hlt
    · intro p hp
      have hp' := (Finset.mem_filter.1 hp).1
      have hpzero := (Finset.mem_filter.1 hp).2
      have hlt := (Finset.mem_filter.1 hp').2.2
      have horder := (Finset.mem_filter.1 hp').2.1
      have hne : p.2 ≠ 0 := by
        intro hzero
        rw [hzero] at horder
        simp at horder
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq]
      have hlt' := hlt
      rw [hpzero] at hlt'
      have hget : (a :: l).get p.2 = l.get (p.2.pred hne) := by
        exact (congrArg (a :: l).get (Fin.succ_pred p.2 hne)).symm
      rw [hget] at hlt'
      exact hlt'
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq] at hi
      apply Finset.mem_filter.2
      constructor
      · apply Finset.mem_filter.2
        constructor
        · simp
        · exact ⟨by simp, by simpa using hi⟩
      · rfl
    · intro p hp
      have hpeq := (Finset.mem_filter.1 hp).2
      have hp := (Finset.mem_filter.1 hp).1
      have hne : p.2 ≠ 0 := by
        have hlt := (Finset.mem_filter.1 hp).2.1
        intro hzero
        rw [hzero] at hlt
        simp at hlt
      apply Prod.ext
      · exact hpeq.symm
      · simp only [Fin.succ_pred]
    · intro i hi
      exact Fin.pred_succ i
  have hrest :
      (s.filter (fun p => ¬p.1 = 0)).card = l.inversionSet.card := by
    symm
    refine Finset.card_bij (s := l.inversionSet)
      (t := s.filter (fun p => ¬p.1 = 0))
      (fun p hp => (p.1.succ, p.2.succ)) ?_ ?_ ?_
    · intro p hp
      apply Finset.mem_filter.2
      constructor
      · apply Finset.mem_filter.2
        constructor
        · simp
        · have hp' := (Finset.mem_filter.1 hp).2
          simpa [List.get_cons_succ] using hp'
      · simp
    · intro p hp q hq heq
      exact Prod.ext ((Fin.succ_injective _)
          (congrArg Prod.fst heq)) ((Fin.succ_injective _)
          (congrArg Prod.snd heq))
    · intro q hq
      have hq' := (Finset.mem_filter.1 hq).1
      have hne₁ := (Finset.mem_filter.1 hq).2
      have hlt := (Finset.mem_filter.1 hq').2.1
      have hne₂ : q.2 ≠ 0 := by
        intro hzero
        rw [hzero] at hlt
        simp at hlt
      refine ⟨(q.1.pred hne₁, q.2.pred hne₂), ?_, ?_⟩
      · apply Finset.mem_filter.2
        constructor
        · simp
        · have hpair := (Finset.mem_filter.1 hq').2
          have hlt' : q.1.pred hne₁ < q.2.pred hne₂ := by
            apply (Fin.succ_lt_succ_iff.mp)
            simpa only [Fin.succ_pred q.1 hne₁, Fin.succ_pred q.2 hne₂]
              using hpair.1
          have hv' : l.get (q.2.pred hne₂) < l.get (q.1.pred hne₁) := by
            have hv := hpair.2
            rw [← Fin.succ_pred q.1 hne₁, ← Fin.succ_pred q.2 hne₂] at hv
            change l.get (q.2.pred hne₂) < l.get (q.1.pred hne₁) at hv
            exact hv
          exact ⟨hlt', hv'⟩
      · apply Prod.ext <;> simp only [Fin.succ_pred]
  change s.card = _
  rw [hsplit, hzero, hrest]
  have hcard := card_filter_get l (fun x => decide (x < a))
  change ((univ : Finset (Fin l.length)).filter
      (fun i => decide (l.get i < a))).card + l.inversionCount = _
  rw [hcard]

end List

namespace List

private theorem patternCount_cons {α : Type*} [LinearOrder α] (a : α) (l : List α) :
    (a :: l).patternCount [1, 0] =
      l.patternCount [1, 0] + (l.filter (fun x => x < a)).length := by
  unfold patternCount
  rw [show [1, 0].length = 1 + 1 by decide, List.sublistsLen_succ_cons]
  rw [List.filter_append]
  simp only [List.length_append]
  have hnew :
      (((List.sublistsLen 1 l).map (List.cons a)).filter
          (fun s => decide (s.SameOrderType [1, 0]))).length =
        (l.filter (fun x => x < a)).length := by
    rw [List.sublistsLen_one, List.filter_map]
    have hfilter :
        List.filter (fun x => decide (([a, x] : List α).SameOrderType [1, 0]))
            l.reverse =
          (l.filter (fun x => x < a)).reverse := by
      rw [List.filter_reverse]
      have heq :
          List.filter (fun x => decide (([a, x] : List α).SameOrderType [1, 0])) l =
            l.filter (fun x => decide (x < a)) := by
        apply List.filter_congr
        intro x hx
        by_cases h : x < a
        · simp [h, List.SameOrderType, List.sameOrderTypeBool, h.le]
        · simp [h, List.SameOrderType, List.sameOrderTypeBool]
      exact congrArg List.reverse heq
    rw [List.filter_map]
    simp only [List.map_map]
    have hpred :
        List.filter
            (((fun s => decide (s.SameOrderType [1, 0])) ∘ List.cons a) ∘
              (fun x => [x])) l.reverse =
          List.filter (fun x => decide (([a, x] : List α).SameOrderType [1, 0]))
            l.reverse := by
      apply List.filter_congr
      intro x hx
      rfl
    rw [hpred, hfilter]
    simp
  rw [hnew]

private theorem patternCount_12_cons {α : Type*} [LinearOrder α] (a : α) (l : List α) :
    (a :: l).patternCount [0, 1] =
      l.patternCount [0, 1] + (l.filter (fun x => a < x)).length := by
  unfold patternCount
  rw [show [0, 1].length = 1 + 1 by decide, List.sublistsLen_succ_cons]
  rw [List.filter_append]
  simp only [List.length_append]
  have hnew :
      (((List.sublistsLen 1 l).map (List.cons a)).filter
          (fun s => decide (s.SameOrderType [0, 1]))).length =
        (l.filter (fun x => a < x)).length := by
    rw [List.sublistsLen_one, List.filter_map]
    have hfilter :
        List.filter (fun x => decide (([a, x] : List α).SameOrderType [0, 1]))
            l.reverse =
          (l.filter (fun x => a < x)).reverse := by
      rw [List.filter_reverse]
      have heq :
          List.filter (fun x => decide (([a, x] : List α).SameOrderType [0, 1])) l =
            l.filter (fun x => decide (a < x)) := by
        apply List.filter_congr
        intro x hx
        by_cases h : a < x
        · simp [h, List.SameOrderType, List.sameOrderTypeBool, h.le]
        · simp [h, List.SameOrderType, List.sameOrderTypeBool]
      exact congrArg List.reverse heq
    rw [List.filter_map]
    simp only [List.map_map]
    have hpred :
        List.filter
            (((fun s => decide (s.SameOrderType [0, 1])) ∘ List.cons a) ∘
              (fun x => [x])) l.reverse =
          List.filter (fun x => decide (([a, x] : List α).SameOrderType [0, 1]))
            l.reverse := by
      apply List.filter_congr
      intro x hx
      rfl
    rw [hpred, hfilter]
    simp
  rw [hnew]

/-- The number of `21` occurrences in a list equals its inversion number. -/
theorem patternCount_21_eq_inversionCount {α : Type*} [LinearOrder α] (l : List α) :
    l.patternCount [1, 0] = l.inversionCount := by
  induction l with
  | nil => simp [patternCount, List.inversionCount, List.inversionSet]
  | cons a l ih =>
    rw [patternCount_cons, inversionCount_cons, ih, Nat.add_comm]

private theorem filter_lt_add_filter_gt_length {α : Type*} [LinearOrder α]
    (a : α) (l : List α) (h : a ∉ l) :
    (l.filter (fun x => a < x)).length +
        (l.filter (fun x => x < a)).length = l.length := by
  induction l with
  | nil => simp
  | cons b l ih =>
    have hne : b ≠ a := by
      intro hba
      apply h
      simp [hba]
    have htail : a ∉ l := by
      intro hmem
      apply h
      simp [hmem]
    by_cases hab : a < b
    · have hnotba : ¬b < a := not_lt_of_ge hab.le
      simp only [hab, decide_true, filter_cons_of_pos, length_cons, hnotba, decide_false,
        Bool.false_eq_true, not_false_eq_true, filter_cons_of_neg]
      rw [← ih htail]
      ac_rfl
    · have hba : b < a := lt_of_le_of_ne (le_of_not_gt hab) hne
      simp only [hab, decide_false, Bool.false_eq_true, not_false_eq_true, filter_cons_of_neg, hba,
        decide_true, filter_cons_of_pos, length_cons]
      rw [← ih htail]
      ac_rfl

private theorem patternCount_12_add_inversion {α : Type*} [LinearOrder α]
    (l : List α) (h : l.Nodup) :
    l.patternCount [0, 1] + l.inversionCount = l.length.choose 2 := by
  induction l with
  | nil => simp [patternCount, List.inversionCount, List.inversionSet]
  | cons a l ih =>
    have h' := (List.nodup_cons.mp h)
    rw [patternCount_12_cons, inversionCount_cons]
    have hfilter := filter_lt_add_filter_gt_length a l h'.1
    calc
      l.patternCount [0, 1] + (l.filter (fun x => a < x)).length +
          ((l.filter (fun x => x < a)).length + l.inversionCount) =
          (l.patternCount [0, 1] + l.inversionCount) +
            ((l.filter (fun x => a < x)).length +
              (l.filter (fun x => x < a)).length) := by ac_rfl
      _ = l.length.choose 2 + l.length := by rw [ih h'.2, hfilter]
      _ = (a :: l).length.choose 2 := by
        change l.length.choose 2 + l.length = (l.length + 1).choose 2
        rw [Nat.choose_succ_succ]
        simp [Nat.choose_one_right]
        ac_rfl

end List

/-- The decreasing pattern of length two. -/
def pattern21 : Equiv.Perm (Fin 2) := Equiv.swap 0 1

/-- The increasing pattern of length two. -/
def pattern12 : Equiv.Perm (Fin 2) := Equiv.refl (Fin 2)

private theorem pattern21_fin_nat (i j : Fin 2) :
    (([1, 0] : List (Fin 2)).get i < ([1, 0] : List (Fin 2)).get j) ↔
      (([1, 0] : List Nat).get i < ([1, 0] : List Nat).get j) := by
  refine Fin.cases ?_ (fun i => ?_) i
  · refine Fin.cases ?_ (fun j => ?_) j
    · decide
    · have hj : j = 0 := Subsingleton.elim _ _
      subst hj
      decide
  · have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    refine Fin.cases ?_ (fun j => ?_) j
    · decide
    · have hj : j = 0 := Subsingleton.elim _ _
      subst hj
      decide

private theorem pattern12_fin_nat (i j : Fin 2) :
    (([0, 1] : List (Fin 2)).get i < ([0, 1] : List (Fin 2)).get j) ↔
      (([0, 1] : List Nat).get i < ([0, 1] : List Nat).get j) := by
  refine Fin.cases ?_ (fun i => ?_) i
  · refine Fin.cases ?_ (fun j => ?_) j
    · decide
    · have hj : j = 0 := Subsingleton.elim _ _
      subst hj
      decide
  · have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    refine Fin.cases ?_ (fun j => ?_) j
    · decide
    · have hj : j = 0 := Subsingleton.elim _ _
      subst hj
      decide

/-- The `21` pattern count of a permutation equals its inversion number. -/
theorem Equiv.Perm.patternCount_21_eq_inversionCount {n : ℕ}
    (σ : Equiv.Perm (Fin n)) :
    σ.patternCount pattern21 = σ.inversionCount := by
  unfold Equiv.Perm.patternCount
  have hp : List.ofFn pattern21 = ([1, 0] : List (Fin 2)) := by decide
  rw [hp]
  have hpat :
      (List.ofFn σ).patternCount ([1, 0] : List (Fin 2)) =
        (List.ofFn σ).patternCount ([1, 0] : List Nat) := by
    unfold List.patternCount
    simp only [List.length_cons, List.length_nil]
    apply congrArg List.length
    apply List.filter_congr
    intro s hs
    apply Bool.eq_iff_iff.mpr
    rw [decide_eq_true_eq, decide_eq_true_eq]
    simp only [List.SameOrderType, List.sameOrderTypeBool, Fin.isValue, List.length_cons,
      List.length_nil, zero_add, Nat.reduceAdd, List.get_eq_getElem, Fin.val_cast,
      Bool.dite_false_right_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨h, hs⟩
      refine ⟨h, ?_⟩
      intro i j
      have hs' := hs i j
      exact hs'.trans (pattern21_fin_nat (Fin.cast h i) (Fin.cast h j))
    · rintro ⟨h, hs⟩
      refine ⟨h, ?_⟩
      intro i j
      have hs' := hs i j
      exact hs'.trans (pattern21_fin_nat (Fin.cast h i) (Fin.cast h j)).symm
  rw [hpat, List.patternCount_21_eq_inversionCount]
  exact σ.inversionCount_toWord

/-- The `12` and `21` pattern counts partition pairs in a permutation. -/
theorem Equiv.Perm.patternCount_12_add_inversionCount {n : ℕ}
    (σ : Equiv.Perm (Fin n)) :
    σ.patternCount pattern12 + σ.inversionCount = n.choose 2 := by
  unfold Equiv.Perm.patternCount
  have hp : List.ofFn pattern12 = ([0, 1] : List (Fin 2)) := by decide
  rw [hp]
  have hpat :
      (List.ofFn σ).patternCount ([0, 1] : List (Fin 2)) =
        (List.ofFn σ).patternCount ([0, 1] : List Nat) := by
    unfold List.patternCount
    simp only [List.length_cons, List.length_nil]
    apply congrArg List.length
    apply List.filter_congr
    intro s hs
    apply Bool.eq_iff_iff.mpr
    rw [decide_eq_true_eq, decide_eq_true_eq]
    simp only [List.SameOrderType, List.sameOrderTypeBool, Fin.isValue, List.length_cons,
      List.length_nil, zero_add, Nat.reduceAdd, List.get_eq_getElem, Fin.val_cast,
      Bool.dite_false_right_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨h, hs⟩
      refine ⟨h, ?_⟩
      intro i j
      have hs' := hs i j
      exact hs'.trans (pattern12_fin_nat (Fin.cast h i) (Fin.cast h j))
    · rintro ⟨h, hs⟩
      refine ⟨h, ?_⟩
      intro i j
      have hs' := hs i j
      exact hs'.trans (pattern12_fin_nat (Fin.cast h i) (Fin.cast h j)).symm
  rw [hpat]
  have hnodup : (List.ofFn σ).Nodup := List.nodup_ofFn.mpr σ.injective
  have hlist := List.patternCount_12_add_inversion (List.ofFn σ) hnodup
  rw [← σ.inversionCount_toWord]
  change (List.ofFn σ).patternCount ([0, 1] : List Nat) +
      (List.ofFn σ).inversionCount = n.choose 2
  simpa only [List.length_ofFn] using hlist
