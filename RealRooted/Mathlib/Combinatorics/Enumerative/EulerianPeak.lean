import Mathlib.Data.Fintype.Perm
import Mathlib.Data.List.Permutation
import Mathlib.Data.List.GetD
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.IntervalCases
import RealRooted.Mathlib.Combinatorics.Enumerative.Descent
import RealRooted.Mathlib.Combinatorics.Enumerative.Peak
import RealRooted.Mathlib.Combinatorics.Enumerative.PermStatistics

namespace Equiv.Perm

open _root_.Finset

/-! The insertion proof below is staged in `Equiv.Perm`, using the canonical
permutation statistics from `PermStatistics`.  The temporary natural-valued
words are only private helpers for the insertion argument. -/

/-- Eulerian numbers, counted by the canonical permutation descent statistic. -/
def eulerianNumber (n k : ℕ) : ℕ :=
  (Finset.univ.filter fun σ : Equiv.Perm (Fin n) => σ.descentCount = k).card

/-- Peak numbers, counted by the canonical permutation peak statistic. -/
def peakNumber (n k : ℕ) : ℕ :=
  (Finset.univ.filter fun σ : Equiv.Perm (Fin n) => σ.peakCount = k).card

example : (List.range 4).map (eulerianNumber 4) = [1, 11, 11, 1] := by decide

example : (List.range 3).map (peakNumber 4) = [8, 16, 0] := by decide

private def natWord {n : ℕ} (σ : Equiv.Perm (Fin n)) : List ℕ :=
  (List.ofFn σ).map Fin.val

private def IsDes (l : List ℕ) (i : ℕ) : Prop :=
  i + 1 < l.length ∧ l.getD (i + 1) 0 < l.getD i 0

private def IsPk (l : List ℕ) (i : ℕ) : Prop :=
  0 < i ∧ i + 1 < l.length ∧ l.getD (i - 1) 0 < l.getD i 0 ∧
    l.getD (i + 1) 0 < l.getD i 0

private instance (l : List ℕ) (i : ℕ) : Decidable (IsDes l i) := by
  unfold IsDes
  infer_instance

private instance (l : List ℕ) (i : ℕ) : Decidable (IsPk l i) := by
  unfold IsPk
  infer_instance

private lemma mem_descentSet_iff_isDes (l : List ℕ) (i : ℕ) :
    i ∈ l.descentSet ↔ IsDes l i := by
  simp only [List.mem_descentSet]
  constructor
  · rintro ⟨h, hlt⟩
    refine ⟨h, ?_⟩
    rw [List.getD_eq_getElem _ _ h, List.getD_eq_getElem _ _ (by lia)]
    exact hlt
  · rintro ⟨h, hlt⟩
    refine ⟨h, ?_⟩
    rw [List.getD_eq_getElem _ _ h, List.getD_eq_getElem _ _ (by lia)] at hlt
    exact hlt

private lemma mem_peakSet_iff_isPk (l : List ℕ) (i : ℕ) :
    i ∈ l.peakSet ↔ IsPk l i := by
  simp only [List.mem_peakSet]
  constructor
  · rintro ⟨h0, h, hlt⟩
    refine ⟨h0, h, ?_, ?_⟩
    · rw [List.getD_eq_getElem _ _ (by lia), List.getD_eq_getElem _ _ (by lia)]
      exact hlt.1
    · rw [List.getD_eq_getElem _ _ h, List.getD_eq_getElem _ _ (by lia)]
      exact hlt.2
  · rintro ⟨h0, h, h1, h2⟩
    refine ⟨h0, h, ?_, ?_⟩
    · rw [List.getD_eq_getElem _ _ (by lia), List.getD_eq_getElem _ _ (by lia)] at h1
      exact h1
    · rw [List.getD_eq_getElem _ _ h, List.getD_eq_getElem _ _ (by lia)] at h2
      exact h2

private lemma natWord_descentSet {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    σ.descentSet = (natWord σ).descentSet := by
  rw [Equiv.Perm.descentSet_eq_list, natWord]
  exact (List.descentSet_map_strictMono _ Fin.val Fin.val_strictMono).symm

private lemma natWord_peakSet {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    σ.peakSet = (natWord σ).peakSet := by
  rw [Equiv.Perm.peakSet, natWord]
  exact (List.peakSet_map_strictMono _ Fin.val Fin.val_strictMono).symm

private lemma des_cons (a : ℕ) (m : List ℕ) :
    (a :: m).descentSet.card = (if IsDes (a :: m) 0 then 1 else 0) +
      m.descentSet.card := by
  cases m with
  | nil =>
    rw [List.descentSet_singleton, List.descentSet_nil]
    unfold IsDes
    simp
  | cons b m =>
    rw [List.descentSet_cons_cons]
    have hd : _root_.Disjoint (if b < a then ({0} : Finset ℕ) else ∅)
        ((b :: m).descentSet.map ⟨Nat.succ, Nat.succ_injective⟩) := by
      split_ifs <;> simp [Finset.disjoint_left]
    rw [Finset.card_union_of_disjoint hd, Finset.card_map]
    have hdes : IsDes (a :: b :: m) 0 ↔ b < a := by
      simp only [IsDes, List.length_cons, List.getD_cons_zero, List.getD_cons_succ]
      simp
    simp only [hdes]
    split_ifs <;> simp

private lemma pk_cons (a : ℕ) (m : List ℕ) :
    (a :: m).peakSet.card = (if IsPk (a :: m) 1 then 1 else 0) +
      m.peakSet.card := by
  have hs : (a :: m).peakSet = (if IsPk (a :: m) 1 then {1} else ∅) ∪
      m.peakSet.image Nat.succ := by
    ext i
    rcases i with _ | _ | i
    · rw [mem_peakSet_iff_isPk]
      have hi : ¬IsPk (a :: m) 0 := by simp [IsPk]
      simp only [Finset.mem_union, Finset.mem_image]
      split_ifs with h <;> simp [hi]
    · rw [mem_peakSet_iff_isPk]
      simp only [Finset.mem_union, Finset.mem_image]
      split_ifs with h <;> simp [h]
    · split_ifs with h <;> simp
  rw [hs, Finset.card_union_of_disjoint, Finset.card_image_of_injective _
    Nat.succ_injective]
  · split_ifs <;> simp
  · split_ifs <;> simp [Finset.disjoint_left]

private lemma getD_insertIdx (l : List ℕ) (x : ℕ) (j i : ℕ) (hj : j ≤ l.length) :
    (l.insertIdx j x).getD i 0 =
      if i < j then l.getD i 0 else if i = j then x else l.getD (i - 1) 0 := by
  induction l generalizing j i with
  | nil =>
    simp only [List.length_nil, nonpos_iff_eq_zero] at hj
    subst hj
    rcases i with _ | i <;> simp
  | cons a l ih =>
    rcases j with _ | j
    · rcases i with _ | i <;> simp
    · rcases i with _ | i
      · simp
      · simp only [List.insertIdx_succ_cons, List.getD_cons_succ]
        rw [ih j i (by simpa using hj)]
        rcases i with _ | i
        · simp
          split_ifs <;> lia
        · simp

private lemma getD_lt_of_forall {l : List ℕ} {N : ℕ} (hN : ∀ x ∈ l, x < N)
    (i : ℕ) (hi : i < l.length) : l.getD i 0 < N := by
  rw [List.getD_eq_getElem _ _ hi]
  exact hN _ (List.getElem_mem hi)

/-- Inserting a largest letter changes the descent count by the displayed terms. -/
private lemma des_insert (N : ℕ) (l : List ℕ) (hN : ∀ x ∈ l, x < N) (j : ℕ)
    (hj : j ≤ l.length) :
    (l.insertIdx j N).descentSet.card +
        (if 0 < j ∧ IsDes l (j - 1) then 1 else 0) =
      l.descentSet.card + (if j < l.length then 1 else 0) := by
  induction l generalizing j with
  | nil =>
    simp only [List.length_nil, nonpos_iff_eq_zero] at hj
    subst hj
    simp only [List.insertIdx_zero, List.descentSet_singleton, List.descentSet_nil]
    unfold IsDes
    simp
  | cons a l ih =>
    have hNa : a < N := hN a (by simp)
    have hNl : ∀ x ∈ l, x < N := fun x hx => hN x (by simp [hx])
    rcases j with _ | j
    · simp only [List.insertIdx_zero, des_cons N (a :: l)]
      simp [IsDes, hNa]
      lia
    · simp only [List.insertIdx_succ_cons, des_cons a]
      have hj' : j ≤ l.length := by simpa using hj
      have ih' := ih hNl j hj'
      have hlen := List.length_insertIdx_of_le_length hj' N
      have hg := getD_insertIdx l N j 0 hj'
      have hg0 := fun h => getD_lt_of_forall hNl 0 h
      clear ih hN
      rcases j with _ | j <;>
        simp only [IsDes, List.getD_cons_zero, List.getD_cons_succ, List.length_cons,
          hlen, hg] at ih' ⊢
      · simp at ih' hg0 ⊢
        split_ifs at ih' ⊢ <;> lia
      · simp at ih' hg0 ⊢
        split_ifs at ih' ⊢ <;> lia

/-- Inserting a largest letter changes the peak count by the displayed terms. -/
private lemma pk_insert (N : ℕ) (l : List ℕ) (hN : ∀ x ∈ l, x < N) (j : ℕ)
    (hj : j ≤ l.length) :
    (l.insertIdx j N).peakSet.card +
        (if 0 < j ∧ IsPk l (j - 1) then 1 else 0) +
        (if IsPk l j then 1 else 0) =
      l.peakSet.card + (if 0 < j ∧ j < l.length then 1 else 0) := by
  induction l generalizing j with
  | nil =>
    simp only [List.length_nil, nonpos_iff_eq_zero] at hj
    subst hj
    simp only [List.insertIdx_zero, List.peakSet_singleton, List.peakSet_nil]
    simp [IsPk]
  | cons a l ih =>
    have hNa : a < N := hN a (by simp)
    have hNl : ∀ x ∈ l, x < N := fun x hx => hN x (by simp [hx])
    rcases j with _ | j
    · simp only [List.insertIdx_zero, pk_cons N (a :: l)]
      simp [IsPk]
      lia
    · simp only [List.insertIdx_succ_cons, pk_cons a]
      have hj' : j ≤ l.length := by simpa using hj
      have ih' := ih hNl j hj'
      have hlen := List.length_insertIdx_of_le_length hj' N
      have hg0 := getD_insertIdx l N j 0 hj'
      have hg1 := getD_insertIdx l N j 1 hj'
      have hb0 := fun h => getD_lt_of_forall hNl 0 h
      clear ih hN
      rcases j with _ | _ | j <;>
        simp only [IsPk, List.getD_cons_succ, List.length_cons, hlen, hg0, hg1] at ih' ⊢
      · simp at ih' hb0 ⊢
        split_ifs at ih' ⊢ <;> lia
      · simp at ih' hb0 ⊢
        split_ifs at ih' ⊢ <;> lia
      · simp at ih' hb0 ⊢
        split_ifs at ih' ⊢ <;> lia

private lemma IsPk_not_succ {l : List ℕ} {i : ℕ} (h : IsPk l i) :
    ¬ IsPk l (i + 1) := by
  unfold IsPk at *
  simp only [add_tsub_cancel_right] at *
  lia

private lemma count_des (N : ℕ) (l : List ℕ) (hN : ∀ x ∈ l, x < N) (m : ℕ) :
    ((range (l.length + 1)).filter
        (fun j => (l.insertIdx j N).descentSet.card = m)).card =
      (if l.descentSet.card = m then l.descentSet.card + 1 else 0) +
      (if l.descentSet.card + 1 = m then l.length - l.descentSet.card else 0) := by
  set d := l.descentSet.card with hd
  set L := l.length with hL
  have key := fun j (hj : j ∈ range (L + 1)) =>
    des_insert N l hN j (by simp at hj; lia)
  have hK : (range (L + 1)).filter
      (fun j => (l.insertIdx j N).descentSet.card = d) =
      insert L (l.descentSet.image Nat.succ) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_image, mem_descentSet_iff_isDes]
    constructor
    · rintro ⟨hj, hv⟩
      have hkey := key j hj
      simp only [Finset.mem_range] at hj
      by_cases hjL : j = L
      · exact Or.inl hjL
      · right
        refine ⟨j - 1, ?_, by split_ifs at hkey <;> lia⟩
        split_ifs at hkey with h1 h2 <;> lia
    · rintro (rfl | ⟨i, hi, rfl⟩)
      · refine ⟨by simp, ?_⟩
        have hkey := key L (by simp)
        rw [← hL] at hkey
        have hnot : ¬(0 < L ∧ IsDes l (L - 1)) := by
          rintro ⟨_, hdes⟩
          have hlt := hdes.1
          rw [← hL] at hlt
          lia
        simp only [hnot, Nat.lt_irrefl, ite_false] at hkey
        lia
      · have hi' := hi
        unfold IsDes at hi'
        refine ⟨by simp; lia, ?_⟩
        have hkey := key (i + 1) (by simp; lia)
        simp only [add_tsub_cancel_right] at hkey
        split_ifs at hkey <;> simp_all
  have hKc : ((range (L + 1)).filter
      (fun j => (l.insertIdx j N).descentSet.card = d)).card = d + 1 := by
    rw [hK, Finset.card_insert_of_notMem, Finset.card_image_of_injective _
      Nat.succ_injective]
    simp only [Finset.mem_image, mem_descentSet_iff_isDes, not_exists, not_and]
    intro i hi h
    unfold IsDes at hi
    lia
  have hval : ∀ j ∈ range (L + 1),
      (l.insertIdx j N).descentSet.card = d ∨
        (l.insertIdx j N).descentSet.card = d + 1 := by
    intro j hj
    have hkey := key j hj
    rw [← hL] at hkey
    have e1 : (if 0 < j ∧ IsDes l (j - 1) then 1 else 0) ≤
        (if j < L then 1 else 0) := by
      by_cases h1 : 0 < j ∧ IsDes l (j - 1)
      · have h1' := h1.2.1
        simp only [h1, show j < L by lia, true_and, ite_true]
        lia
      · simp only [h1, ite_false]
        exact Nat.zero_le _
    have e2 : (if j < L then 1 else 0) ≤ 1 := by split_ifs <;> lia
    lia
  have hIc : ((range (L + 1)).filter
      (fun j => (l.insertIdx j N).descentSet.card = d + 1)).card = L - d := by
    have h1 := Finset.card_filter_add_card_filter_not
      (s := range (L + 1)) (fun j => (l.insertIdx j N).descentSet.card = d)
    have h2 : (range (L + 1)).filter
        (fun j => ¬ (l.insertIdx j N).descentSet.card = d) =
        (range (L + 1)).filter
          (fun j => (l.insertIdx j N).descentSet.card = d + 1) := by
      apply Finset.filter_congr
      intro j hj
      rcases hval j hj with h | h <;> lia
    rw [h2, hKc] at h1
    simp only [Finset.card_range] at h1
    lia
  by_cases hm : d = m
  · subst hm
    simp [hKc]
  · by_cases hm' : d + 1 = m
    · subst hm'
      simp [hIc]
    · simp only [hm, hm', ite_false]
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro j hj hv
      rcases hval j hj with h | h <;> lia

private lemma count_pk (N : ℕ) (l : List ℕ) (hN : ∀ x ∈ l, x < N)
    (hl : 1 ≤ l.length) (m : ℕ) :
    ((range (l.length + 1)).filter
        (fun j => (l.insertIdx j N).peakSet.card = m)).card =
      (if l.peakSet.card = m then 2 * l.peakSet.card + 2 else 0) +
      (if l.peakSet.card + 1 = m then l.length - 1 - 2 * l.peakSet.card else 0) := by
  set p := l.peakSet.card with hp
  set L := l.length with hL
  have key := fun j (hj : j ∈ range (L + 1)) =>
    pk_insert N l hN j (by simp at hj; lia)
  have hK : (range (L + 1)).filter
      (fun j => (l.insertIdx j N).peakSet.card = p) =
      insert 0 (insert L (l.peakSet ∪ l.peakSet.image Nat.succ)) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_union,
      Finset.mem_image, mem_peakSet_iff_isPk]
    constructor
    · rintro ⟨hj, hv⟩
      have hkey := key j hj
      simp only [Finset.mem_range] at hj
      by_cases hj0 : j = 0
      · exact Or.inl hj0
      by_cases hjL : j = L
      · exact Or.inr (Or.inl hjL)
      right
      right
      by_cases hB : IsPk l j
      · exact Or.inl hB
      · right
        refine ⟨j - 1, ?_, by lia⟩
        split_ifs at hkey with h1 h2 <;> lia
    · rintro (rfl | rfl | h | ⟨i, hi, rfl⟩)
      · refine ⟨by simp, ?_⟩
        have hkey := key 0 (by simp)
        have h0 : ¬IsPk l 0 := by simp [IsPk]
        simp only [Nat.not_lt_zero, false_and, h0, ite_false] at hkey
        lia
      · refine ⟨by simp, ?_⟩
        have hkey := key L (by simp)
        have hprev : ¬(0 < L ∧ IsPk l (L - 1)) := by
          rintro ⟨_, hprev⟩
          have hlt := hprev.2.1
          rw [← hL] at hlt
          lia
        have hcurr : ¬IsPk l L := by
          intro hcurr
          have hlt := hcurr.2.1
          rw [← hL] at hlt
          lia
        have hright : ¬(0 < L ∧ L < l.length) := by
          rw [← hL]
          lia
        simp only [hprev, hcurr, hright, ite_false] at hkey
        lia
      · have h' := h
        unfold IsPk at h'
        refine ⟨by simp; lia, ?_⟩
        have hkey := key j (by simp; lia)
        have hn : ¬(0 < j ∧ IsPk l (j - 1)) := by
          rintro ⟨hj0, hj1⟩
          have hnot := IsPk_not_succ hj1
          rw [Nat.sub_add_cancel hj0] at hnot
          exact hnot h
        have hright : 0 < j ∧ j < l.length := ⟨h'.1, by lia⟩
        simp only [hn, h] at hkey
        simp only [hright] at hkey
        simp only [ite_false] at hkey
        simpa [hp] using Nat.add_right_cancel hkey
      · have hi' := hi
        unfold IsPk at hi'
        refine ⟨by simp; lia, ?_⟩
        have hkey := key (i + 1) (by simp; lia)
        simp only [add_tsub_cancel_right] at hkey
        have hnot := IsPk_not_succ hi
        have hprev : 0 < i + 1 ∧ IsPk l i := ⟨by lia, hi⟩
        have hright : 0 < i + 1 ∧ i + 1 < l.length := ⟨by lia, hi'.2.1⟩
        simp only [hprev, hnot] at hkey
        simp only [hright] at hkey
        simp only [ite_false] at hkey
        simpa [hp] using Nat.add_right_cancel hkey
  have hKc : ((range (L + 1)).filter
      (fun j => (l.insertIdx j N).peakSet.card = p)).card = 2 * p + 2 := by
    have hd : _root_.Disjoint l.peakSet (l.peakSet.image Nat.succ) := by
      rw [Finset.disjoint_left]
      intro a ha hb
      simp only [Finset.mem_image] at hb
      obtain ⟨i, hi, rfl⟩ := hb
      rw [mem_peakSet_iff_isPk] at ha hi
      exact IsPk_not_succ hi ha
    rw [hK, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_union_of_disjoint hd, Finset.card_image_of_injective _
        Nat.succ_injective]
    · lia
    · simp only [Finset.mem_union, Finset.mem_image, mem_peakSet_iff_isPk, not_or,
        not_exists, not_and]
      refine ⟨fun h => by unfold IsPk at h; lia,
        fun i hi h => by unfold IsPk at hi; lia⟩
    · simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_image,
        mem_peakSet_iff_isPk, not_or, not_exists, not_and]
      refine ⟨by lia, fun h => by unfold IsPk at h; lia,
        fun i _ h => by lia⟩
  have hval : ∀ j ∈ range (L + 1),
      (l.insertIdx j N).peakSet.card = p ∨
        (l.insertIdx j N).peakSet.card = p + 1 := by
    intro j hj
    have hkey := key j hj
    rw [← hL] at hkey
    have e1 : (if 0 < j ∧ IsPk l (j - 1) then 1 else 0) ≤
        (if 0 < j ∧ j < L then 1 else 0) := by
      by_cases h1 : 0 < j ∧ IsPk l (j - 1)
      · have h1' := h1.2.2.1
        simp only [h1, show j < L by lia, true_and, ite_true]
        lia
      · simp only [h1, ite_false]
        exact Nat.zero_le _
    have e2 : (if IsPk l j then 1 else 0) ≤
        (if 0 < j ∧ j < L then 1 else 0) := by
      by_cases h1 : IsPk l j
      · have h1' := h1.2.1
        simp only [h1, show 0 < j ∧ j < L by exact ⟨h1.1, by lia⟩,
          true_and, ite_true]
        lia
      · simp only [h1, ite_false]
        exact Nat.zero_le _
    have e3 : (if 0 < j ∧ IsPk l (j - 1) then 1 else 0) +
        (if IsPk l j then 1 else 0) ≤ 1 := by
      by_cases h1 : 0 < j ∧ IsPk l (j - 1)
      · have h2 := IsPk_not_succ h1.2
        rw [Nat.sub_add_cancel h1.1] at h2
        simp only [h1, h2, true_and, ite_true, ite_false]
        lia
      · simp only [h1, ite_false]
        split_ifs <;> lia
    have e4 : (if 0 < j ∧ j < L then 1 else 0) ≤ 1 := by
      split_ifs <;> lia
    lia
  have hIc : ((range (L + 1)).filter
      (fun j => (l.insertIdx j N).peakSet.card = p + 1)).card =
        L - 1 - 2 * p := by
    have h1 := Finset.card_filter_add_card_filter_not
      (s := range (L + 1)) (fun j => (l.insertIdx j N).peakSet.card = p)
    have h2 : (range (L + 1)).filter
        (fun j => ¬ (l.insertIdx j N).peakSet.card = p) =
        (range (L + 1)).filter
          (fun j => (l.insertIdx j N).peakSet.card = p + 1) := by
      apply Finset.filter_congr
      intro j hj
      rcases hval j hj with h | h <;> lia
    rw [h2, hKc, Finset.card_range] at h1
    lia
  by_cases hm : p = m
  · subst hm
    simp [hKc]
  · by_cases hm' : p + 1 = m
    · subst hm'
      simp [hIc]
    · simp only [hm, hm', ite_false]
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro j hj hv
      rcases hval j hj with h | h <;> lia
private def perms (n : ℕ) : List (List ℕ) :=
  (List.range n).reverse.permutations'

private lemma natWord_mem_perms {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    natWord σ ∈ perms n := by
  rw [perms, List.mem_permutations']
  have h1 : natWord σ = ((List.finRange n).map σ).map Fin.val := by
    simp [natWord, List.ofFn_eq_map, List.map_map, Function.comp_def]
  rw [h1]
  refine ((σ.map_finRange_perm).map _).trans ?_
  rw [List.map_coe_finRange_eq_range]
  exact (List.reverse_perm _).symm

private lemma natWord_injective (n : ℕ) :
    Function.Injective (natWord (n := n)) := by
  intro σ τ h
  ext i
  have hi := congrArg (fun l => l[i.1]?) h
  simpa [natWord] using hi

private lemma nodup_perms (n : ℕ) : (perms n).Nodup :=
  (List.permutations_perm_permutations' _).nodup_iff.mp
    (List.nodup_permutations _ (List.nodup_reverse.mpr List.nodup_range))

private lemma image_natWord (n : ℕ) :
    (univ : Finset (Equiv.Perm (Fin n))).image natWord = (perms n).toFinset := by
  apply Finset.eq_of_subset_of_card_le
  · intro l hl
    simp only [Finset.mem_image] at hl
    obtain ⟨σ, -, rfl⟩ := hl
    simpa using natWord_mem_perms σ
  · rw [Finset.card_image_of_injective _ (natWord_injective n),
      List.toFinset_card_of_nodup (nodup_perms n), perms,
      ← (List.permutations_perm_permutations' _).length_eq,
      List.length_permutations]
    simp [Fintype.card_perm]

private lemma card_filter_natWord (n : ℕ) (Q : List ℕ → Prop)
    [DecidablePred Q] :
    (univ.filter fun σ : Equiv.Perm (Fin n) => Q (natWord σ)).card =
      (perms n).countP (fun l => decide (Q l)) := by
  rw [← Finset.card_image_of_injective _ (natWord_injective n),
    ← Finset.filter_image, image_natWord,
    List.countP_eq_length_filter,
    ← List.toFinset_card_of_nodup ((nodup_perms n).filter _)]
  congr 1
  ext l
  simp

private lemma mem_perms {n : ℕ} {l : List ℕ} (hl : l ∈ perms n) :
    l.length = n ∧ ∀ x ∈ l, x < n := by
  rw [perms, List.mem_permutations'] at hl
  refine ⟨by simpa using hl.length_eq, fun x hx => ?_⟩
  simpa using hl.mem_iff.mp hx

private lemma perms_succ (n : ℕ) :
    perms (n + 1) = (perms n).flatMap (List.permutations'Aux n) := by
  simp [perms, List.range_succ, List.permutations']

private lemma permutationsAux_eq (x : ℕ) (s : List ℕ) :
    List.permutations'Aux x s =
      (List.range (s.length + 1)).map (fun j => s.insertIdx j x) := by
  apply List.ext_getElem
  · simp [List.length_permutations'Aux]
  · intro i h1 h2
    simp [List.getElem_permutations'Aux]

private lemma countP_range (n : ℕ) (p : ℕ → Prop) [DecidablePred p] :
    (List.range n).countP (fun j => decide (p j)) =
      ((Finset.range n).filter p).card := by
  rw [List.countP_eq_length_filter, Finset.card_def, Finset.filter_val,
    Finset.range_val]
  simp [Multiset.range]

private lemma countP_perms_succ (n : ℕ) (Q : List ℕ → Prop) [DecidablePred Q] :
    (perms (n + 1)).countP (fun l => decide (Q l)) =
      ((perms n).map fun l =>
        ((Finset.range (l.length + 1)).filter
          (fun j => Q (l.insertIdx j n))).card).sum := by
  rw [perms_succ, List.countP_flatMap]
  congr 1
  apply List.map_congr_left
  intro l _
  simp only [Function.comp_apply, permutationsAux_eq, List.countP_map]
  exact countP_range _ _

private lemma sum_map_ite (L : List (List ℕ)) (f : List ℕ → ℕ)
    (p q : List ℕ → Prop) [DecidablePred p] [DecidablePred q] (a b : ℕ)
    (hf : ∀ x ∈ L, f x = (if p x then a else 0) + (if q x then b else 0)) :
    (L.map f).sum = a * L.countP (fun x => decide (p x)) +
      b * L.countP (fun x => decide (q x)) := by
  induction L with
  | nil => simp
  | cons x L ih =>
    rw [List.map_cons, List.sum_cons,
      ih (fun y hy => hf y (by simp [hy])), hf x (by simp),
      List.countP_cons, List.countP_cons]
    split_ifs <;> simp_all <;> ring

private lemma eulerian_eq_countP (n m : ℕ) :
    eulerianNumber n m = (perms n).countP
      (fun l => decide (l.descentSet.card = m)) := by
  rw [eulerianNumber]
  have h := card_filter_natWord n (fun l => l.descentSet.card = m)
  rw [← h]
  congr 1
  apply Finset.filter_congr
  intro σ hσ
  change σ.descentSet.card = m ↔ (natWord σ).descentSet.card = m
  rw [natWord_descentSet]

private lemma peakNumber_eq_countP (n m : ℕ) :
    peakNumber n m = (perms n).countP
      (fun l => decide (l.peakSet.card = m)) := by
  rw [peakNumber]
  have h := card_filter_natWord n (fun l => l.peakSet.card = m)
  rw [← h]
  congr 1
  apply Finset.filter_congr
  intro σ hσ
  change σ.peakSet.card = m ↔ (natWord σ).peakSet.card = m
  rw [natWord_peakSet]

private lemma eulerian_succ_sum (n m : ℕ) :
    eulerianNumber (n + 1) m = ((perms n).map fun l =>
      (if l.descentSet.card = m then l.descentSet.card + 1 else 0) +
      (if l.descentSet.card + 1 = m then n - l.descentSet.card else 0)).sum := by
  rw [eulerian_eq_countP, countP_perms_succ]
  congr 1
  apply List.map_congr_left
  intro l hl
  obtain ⟨hlen, hN⟩ := mem_perms hl
  rw [count_des n l hN m, hlen]

private lemma peakNumber_succ_sum (n m : ℕ) (hn : 1 ≤ n) :
    peakNumber (n + 1) m = ((perms n).map fun l =>
      (if l.peakSet.card = m then 2 * l.peakSet.card + 2 else 0) +
      (if l.peakSet.card + 1 = m then n - 1 - 2 * l.peakSet.card else 0)).sum := by
  rw [peakNumber_eq_countP, countP_perms_succ]
  congr 1
  apply List.map_congr_left
  intro l hl
  obtain ⟨hlen, hN⟩ := mem_perms hl
  rw [count_pk n l hN (by lia) m, hlen]

private lemma peakSet_card_le (l : List ℕ) : l.peakSet.card ≤ l.length - 1 := by
  have h := List.peakCount_le l
  unfold List.peakCount at h
  lia

private lemma peakNumber_succ_of_le_one (n k : ℕ) (hn : n ≤ 1) :
    peakNumber n (k + 1) = 0 := by
  rw [peakNumber, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro σ _
  have h1 := peakSet_card_le (natWord σ)
  have h2 : (natWord σ).length = n := by simp [natWord]
  have h3 : σ.peakCount = (natWord σ).peakSet.card := by
    change σ.peakSet.card = (natWord σ).peakSet.card
    rw [natWord_peakSet]
  have h1' : σ.peakCount ≤ n - 1 := by
    calc
      σ.peakCount = (natWord σ).peakSet.card := h3
      _ ≤ (natWord σ).length - 1 := h1
      _ = n - 1 := by rw [h2]
  lia

/-- The Eulerian insertion recurrence for the canonical descent statistic. -/
theorem eulerianNumber_succ_succ (n k : ℕ) :
    eulerianNumber (n + 1) (k + 1) = (k + 2) * eulerianNumber n (k + 1) +
      (n - k) * eulerianNumber n k := by
  rw [eulerian_succ_sum, eulerian_eq_countP, eulerian_eq_countP]
  apply sum_map_ite
  intro l _
  split_ifs <;> lia

/-- The zero-descent Eulerian number for the canonical descent statistic. -/
theorem eulerianNumber_succ_zero (n : ℕ) : eulerianNumber (n + 1) 0 = 1 := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [eulerian_succ_sum,
      sum_map_ite _ _ (fun l => l.descentSet.card = 0) (fun _ => False) 1 0,
      ← eulerian_eq_countP, ih]
    · simp
    · intro l _
      by_cases h : l.descentSet.card = 0 <;> simp [h]

/-- The peak insertion recurrence for the canonical interior-peak statistic. -/
theorem peakNumber_succ_succ (n k : ℕ) :
    peakNumber (n + 1) (k + 1) = (2 * k + 4) * peakNumber n (k + 1) +
      (n - 1 - 2 * k) * peakNumber n k := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [peakNumber_succ_of_le_one 1 k le_rfl,
      peakNumber_succ_of_le_one 0 k (by lia)]
    simp
  rw [peakNumber_succ_sum n _ hn, peakNumber_eq_countP, peakNumber_eq_countP]
  apply sum_map_ite
  intro l _
  split_ifs <;> lia

/-- The zero-peak value for the canonical interior-peak statistic. -/
theorem peakNumber_succ_zero (n : ℕ) : peakNumber (n + 1) 0 = 2 ^ n := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [peakNumber_succ_sum (n + 1) 0 (by lia),
      sum_map_ite _ _ (fun l => l.peakSet.card = 0) (fun _ => False) 2 0,
      ← peakNumber_eq_countP, ih, pow_succ]
    · simp [mul_comm]
    · intro l _
      by_cases h : l.peakSet.card = 0 <;> simp [h]

end Equiv.Perm
