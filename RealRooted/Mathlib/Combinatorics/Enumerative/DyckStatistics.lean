import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Linarith

/-!
# The Narayana distribution of Dyck-word peaks

`DyckWord.peakCount` counts the `UD` factors of a Dyck word, and `Nat.narayana n k` is the
Narayana number `C(n,k) C(n,k-1) / n` (with `N(0,0) = 1`).
`DyckWord.card_semilength_peakCount`: the Dyck words of semilength `n` with `k` peaks number
`Nat.narayana n k`, except for `(n, k) = (1, 0)` (`card_semilength_one_peakCount_zero`), where
the natural-number formula gives `1`.  The proof counts suffix-ballot words by first letter;
it was found by Aristotle (Harmonic) and adapted.
-/

open List
open DyckStep

/-- The Narayana number, with the empty-path convention `N(0,0) = 1`. -/
def Nat.narayana (n k : ℕ) : ℕ :=
  if n = 0 then if k = 0 then 1 else 0
  else Nat.choose n k * Nat.choose n (k - 1) / n

namespace DyckWord

private def peakCountList : List DyckStep → ℕ
  | [] => 0
  | U :: D :: l => peakCountList l + 1
  | _ :: l => peakCountList l

/-- The number of `UD` peaks in a Dyck word. -/
def peakCount (p : DyckWord) : ℕ := peakCountList p.toList

/-! ### Proof infrastructure

We count *suffix-ballot* words (every suffix has at least as many `D`s as `U`s) with
`a` copies of `U`, `b` copies of `D` and a given number of peaks, split by first letter.
Prepending a letter gives linear recurrences, whose solutions are explicit
differences of products of binomial coefficients (verified via Pascal's rule).
The balanced suffix-ballot words are exactly the Dyck words. -/

private def Good (l : List DyckStep) : Prop := ∀ i, (l.drop i).count U ≤ (l.drop i).count D

private lemma good_nil : Good [] := by intro i; simp

private lemma good_cons {x : DyckStep} {l : List DyckStep} :
    Good (x :: l) ↔ Good l ∧ (x::l).count U ≤ (x::l).count D := by
  constructor
  · intro h; exact ⟨fun i => h (i+1), h 0⟩
  · rintro ⟨h1, h2⟩ (_|i)
    exacts [h2, h1 i]

private def S : ℕ → ℕ → Finset (List DyckStep)
  | 0, 0 => {[]}
  | _+1, 0 => ∅
  | 0, b+1 => (S 0 b).image (D :: ·)
  | a+1, b+1 => (S (a+1) b).image (D :: ·) ∪
      (if a+1 ≤ b+1 then (S a (b+1)).image (U :: ·) else ∅)
termination_by a b => a + b

private lemma mem_S {l : List DyckStep} {a b : ℕ} :
    l ∈ S a b ↔ l.count U = a ∧ l.count D = b ∧ Good l := by
  induction l generalizing a b with
  | nil =>
    cases a with
    | zero =>
      cases b with
      | zero =>
        simp only [S, good_nil, Finset.mem_singleton, count_nil, true_and]
      | succ b =>
        simp only [S, Finset.mem_image, reduceCtorEq, false_and, exists_const,
          count_nil, Nat.right_eq_add, Nat.add_eq_zero_iff, one_ne_zero, and_false,
]
    | succ a =>
      cases b with
      | zero =>
        simp only [S, Finset.notMem_empty, count_nil, Nat.right_eq_add,
          Nat.add_eq_zero_iff, one_ne_zero, and_false, true_and, false_and]
      | succ b =>
        simp only [S, Finset.mem_union, Finset.mem_image, reduceCtorEq,
          false_and, exists_const, count_nil, Nat.right_eq_add, Nat.add_eq_zero_iff,
          one_ne_zero, and_false, and_self, iff_false]
        split_ifs with h
        · simp only [Finset.mem_image, reduceCtorEq, 
            false_or]
          exact fun ⟨_, _, hfalse⟩ => hfalse
        · simp only [Finset.notMem_empty, false_or]
          exact fun hfalse => hfalse
  | cons x l ih =>
    cases x with
    | U =>
      cases a with
      | zero =>
        cases b with
        | zero =>
          simp only [S, Finset.mem_singleton, reduceCtorEq, count_cons_self,
            Nat.add_eq_zero_iff, one_ne_zero, and_false, ne_eq, not_false_eq_true,
            count_cons_of_ne, good_cons, false_and]
        | succ b =>
          simp only [S, Finset.mem_image, cons.injEq, reduceCtorEq, false_and,
            and_false, exists_const, count_cons_self, Nat.add_eq_zero_iff,
            one_ne_zero, ne_eq, not_false_eq_true, count_cons_of_ne, good_cons]
      | succ a =>
        cases b with
        | zero =>
          simp only [S, Finset.notMem_empty, count_cons_self, Nat.add_right_cancel_iff,
            ne_eq, reduceCtorEq, not_false_eq_true, count_cons_of_ne, good_cons,
            false_iff, not_and, not_le]
          lia
        | succ b =>
          simp only [S, add_le_add_iff_right, Finset.mem_union, Finset.mem_image,
            cons.injEq, reduceCtorEq, false_and, and_false, exists_const,
            false_or, count_cons_self, Nat.add_right_cancel_iff, ne_eq,
            not_false_eq_true, count_cons_of_ne, good_cons, 
]
          split_ifs <;> grind
    | D =>
      cases a with
      | zero =>
        cases b with
        | zero =>
          simp only [S, Finset.mem_singleton, reduceCtorEq, ne_eq, not_false_eq_true,
            count_cons_of_ne, count_cons_self, Nat.add_eq_zero_iff, one_ne_zero,
            and_false, good_cons, false_and]
        | succ b =>
          simp only [S, Finset.mem_image, cons.injEq, true_and, exists_eq_right,
            ih, ne_eq, reduceCtorEq, not_false_eq_true, count_cons_of_ne,
            count_cons_self, Nat.add_right_cancel_iff, good_cons,
            and_congr_right_iff, iff_self_and]
          lia
      | succ a =>
        cases b with
        | zero =>
          simp only [S, 
            ne_eq, reduceCtorEq,
            Finset.notMem_empty, not_false_eq_true, count_cons_of_ne, count_cons_self,
            good_cons]
          lia
        | succ b =>
          simp only [S, add_le_add_iff_right, Finset.mem_union, Finset.mem_image,
            cons.injEq, true_and, exists_eq_right, ih, ne_eq, reduceCtorEq,
            not_false_eq_true, count_cons_of_ne, count_cons_self,
            Nat.add_right_cancel_iff, good_cons]
          have hEmpty : D :: l ∉ (∅ : Finset (List DyckStep)) := Finset.notMem_empty _
          have hGood : ∀ r : List DyckStep, Good r → r.count U ≤ r.count D := by
            intro r hr
            simpa using hr 0
          split_ifs <;> simp only [hEmpty] at * <;> grind

private lemma good_le {l : List DyckStep} (h : Good l) : l.count U ≤ l.count D := by
  simpa using h 0

private lemma S_le {l : List DyckStep} {a b : ℕ} (h : l ∈ S a b) : a ≤ b := by
  obtain ⟨rfl, rfl, h'⟩ := mem_S.1 h
  exact good_le h'

private lemma pc_U (l : List DyckStep) :
    peakCountList (U :: l) = peakCountList l + if l.head? = some D then 1 else 0 := by
  rcases l with _ | ⟨_ | _, l⟩ <;> simp [peakCountList]

private lemma pc_D (l : List DyckStep) : peakCountList (D :: l) = peakCountList l := by
  rcases l with _ | ⟨_ | _, l⟩ <;> simp [peakCountList]

private def cU (a b k : ℕ) : ℕ :=
  ((S a b).filter (fun l => l.head? = some U ∧ peakCountList l = k)).card
private def cD (a b k : ℕ) : ℕ :=
  ((S a b).filter (fun l => l.head? = some D ∧ peakCountList l = k)).card
private def cT (a b k : ℕ) : ℕ := ((S a b).filter (fun l => peakCountList l = k)).card

private lemma card_split (s : Finset (List DyckStep)) (Q : List DyckStep → Prop)
    [DecidablePred Q] :
    (s.filter Q).card = (s.filter (fun l => l.head? = some U ∧ Q l)).card +
      (s.filter (fun l => l.head? = some D ∧ Q l)).card +
      (s.filter (fun l => l = [] ∧ Q l)).card := by
  simp only [Finset.card_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rcases l with _ | ⟨_ | _, l⟩ <;> simp

private lemma card_nil (a b k : ℕ) :
    ((S a b).filter (fun l => l = [] ∧ peakCountList l = k)).card =
      if a = 0 ∧ b = 0 ∧ k = 0 then 1 else 0 := by
  split_ifs with h
  · obtain ⟨rfl, rfl, rfl⟩ := h
    rw [Finset.card_eq_one]
    refine ⟨[], ?_⟩
    ext l
    simp only [Finset.mem_filter, mem_S, Finset.mem_singleton]
    constructor
    · exact fun h => h.2.1
    · rintro rfl; simp [good_nil, peakCountList]
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro l hl ⟨rfl, hk⟩
    simp only [mem_S, count_nil, peakCountList] at hl hk
    lia

private lemma cT_eq (a b k : ℕ) :
    cT a b k = cU a b k + cD a b k + if a = 0 ∧ b = 0 ∧ k = 0 then 1 else 0 := by
  unfold cT cU cD
  rw [card_split _ (fun l => peakCountList l = k), card_nil]

private lemma cD_succ (a b k : ℕ) : cD a (b+1) k = cT a b k := by
  unfold cD cT
  rw [show (S a (b+1)).filter (fun l => l.head? = some D ∧ peakCountList l = k) =
      ((S a b).filter (fun l => peakCountList l = k)).image (D :: ·) from ?_]
  · exact Finset.card_image_of_injective _ (List.cons_injective)
  ext l
  rcases l with _ | ⟨_ | _, l⟩
  · simp only [Finset.mem_filter, head?_nil, reduceCtorEq, false_and, and_false,
      Finset.mem_image, exists_const]
  · simp only [Finset.mem_filter, head?_cons, Option.some.injEq, reduceCtorEq,
      false_and, and_false, Finset.mem_image, cons.injEq, exists_const]
  · simp only [Finset.mem_filter, head?_cons, reduceCtorEq,
      true_and, Finset.mem_image, cons.injEq, exists_eq_right, mem_S, good_cons, pc_D,
      count_cons_self, count_cons_of_ne, ne_eq, not_false_eq_true,
      Nat.add_right_cancel_iff]
    constructor
    · rintro ⟨⟨hu, hd, hg, htotal⟩, hk⟩
      exact ⟨⟨hu, hd, hg⟩, hk⟩
    · rintro ⟨⟨hu, hd, hg⟩, hk⟩
      refine ⟨⟨hu, hd, hg, ?_⟩, hk⟩
      have hle := good_le hg
      lia

private lemma cD_zero (a k : ℕ) : cD a 0 k = 0 := by
  unfold cD
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro (_ | ⟨_ | _, l⟩) hl ⟨hh, _⟩ <;> simp [mem_S] at hl hh

private lemma cU_zero (b k : ℕ) : cU 0 b k = 0 := by
  unfold cU
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro (_ | ⟨_ | _, l⟩) hl ⟨hh, _⟩ <;> simp [mem_S] at hl hh

private lemma cU_gt {a b : ℕ} (h : b < a) (k : ℕ) : cU a b k = 0 := by
  unfold cU
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro l hl
  have := S_le hl
  lia

private lemma cD_gt {a b : ℕ} (h : b < a) (k : ℕ) : cD a b k = 0 := by
  unfold cD
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro l hl
  have := S_le hl
  lia

private lemma cU_succ_aux {a b : ℕ} (hab : a + 1 ≤ b) (k : ℕ) :
    cU (a+1) b k = cU a b k +
      ((S a b).filter (fun l => l.head? = some D ∧ peakCountList l + 1 = k)).card := by
  unfold cU
  rw [show (S (a+1) b).filter (fun l => l.head? = some U ∧ peakCountList l = k) =
      ((S a b).filter (fun l => peakCountList l + (if l.head? = some D then 1 else 0) = k)).image
        (U :: ·) from ?_]
  · rw [Finset.card_image_of_injective _ (List.cons_injective), card_split]
    have h0 : ((S a b).filter (fun l => l = [] ∧
        peakCountList l + (if l.head? = some D then 1 else 0) = k)).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      rintro l hl ⟨rfl, -⟩
      simp only [mem_S, count_nil] at hl
      lia
    rw [h0, add_zero]
    congr 2
    · apply Finset.filter_congr
      intro l _
      constructor
      · rintro ⟨h1, h2⟩; simp_all
      · rintro ⟨h1, h2⟩; simp_all
    · apply Finset.filter_congr
      intro l _
      constructor
      · rintro ⟨h1, h2⟩; simp_all
      · rintro ⟨h1, h2⟩; simp_all
  ext l
  rcases l with _ | ⟨_ | _, l⟩
  · simp only [Finset.mem_filter, mem_S, count_nil, Nat.right_eq_add,
      Nat.add_eq_zero_iff, one_ne_zero, and_false, false_and, head?_nil, reduceCtorEq,
      and_self, Finset.mem_image, exists_const]
  · simp only [Finset.mem_filter, mem_S, count_cons_self, Nat.add_right_cancel_iff,
      ne_eq, reduceCtorEq, not_false_eq_true, count_cons_of_ne, good_cons, head?_cons,
      pc_U, true_and, Finset.mem_image, cons.injEq, exists_eq_right,
      and_congr_left_iff, and_congr_right_iff, and_iff_left_iff_imp]
    intro _ hu hd hg
    lia
  · simp only [Finset.mem_filter, mem_S, ne_eq, reduceCtorEq, not_false_eq_true,
      count_cons_of_ne, count_cons_self, good_cons, head?_cons, Option.some.injEq,
      false_and, and_false, Finset.mem_image, cons.injEq, exists_const]

private lemma cU_succ (a b k : ℕ) :
    cU (a+1) b k = if a + 1 ≤ b then cU a b k + (if k = 0 then 0 else cD a b (k-1)) else 0 := by
  split_ifs with hab hk
  · subst hk
    rw [cU_succ_aux hab]
    simp
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by lia⟩
    rw [cU_succ_aux hab]
    simp only [cD, add_tsub_cancel_right, add_left_inj]
  · exact cU_gt (by lia) k


private def fT (a b k : ℕ) : ℤ :=
  if a = 0 then (if k = 0 then 1 else 0)
  else (a.choose k * b.choose k : ℤ) - ((a-1).choose k * (b+1).choose k : ℤ)

private def fU (a b k : ℕ) : ℤ :=
  if a = 0 ∨ b = 0 ∨ k = 0 then 0
  else (a.choose k * (b-1).choose (k-1) : ℤ) - ((a-1).choose k * b.choose (k-1) : ℤ)

private def fD (a b k : ℕ) : ℤ := if b = 0 then 0 else fT a (b-1) k

private lemma id1 {a b : ℕ} (hab : a ≤ b) (k : ℕ) :
    fU a b k + fD a b k + (if a = 0 ∧ b = 0 ∧ k = 0 then 1 else 0) = fT a b k := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · rcases Nat.eq_zero_or_pos b with rfl | hb
    · simp [fU, fD, fT]
    · obtain ⟨b, rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by lia⟩
      simp [fU, fD, fT]
  obtain ⟨a, rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by lia⟩
  obtain ⟨b, rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by lia⟩
  rcases k with _ | k
  · simp [fU, fD, fT]
  · have h1 := Nat.choose_succ_succ b k
    have h2 := Nat.choose_succ_succ (b+1) k
    simp only [fU, fD, fT, Nat.add_one_ne_zero, ite_false, or_self, add_tsub_cancel_right,
      and_false, add_zero]
    rw [h2, h1]
    push_cast
    ring

private lemma id2 {a b : ℕ} (hab : a + 1 ≤ b) (k : ℕ) :
    fU a b k + (if k = 0 then 0 else fD a b (k-1)) = fU (a+1) b k := by
  obtain ⟨b, rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by lia⟩
  rcases k with _ | k
  · simp [fU]
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · rcases k with _ | k
    · simp [fU, fD, fT]
    · simp [fU, fD, fT, Nat.choose_eq_zero_of_lt (by lia : 1 < k + 1 + 1)]
  obtain ⟨a, rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by lia⟩
  have h1 := Nat.choose_succ_succ a k
  have h2 := Nat.choose_succ_succ (a+1) k
  simp only [fU, fD, fT, Nat.add_one_ne_zero, ite_false, or_self, add_tsub_cancel_right]
  rw [h2, h1]
  push_cast
  ring

private lemma id3 {a : ℕ} (ha : a ≠ 0) (k : ℕ) : fT a (a-1) k = 0 := by
  obtain ⟨a, rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by lia⟩
  simp [fT, mul_comm]


private lemma main_ind (n : ℕ) : ∀ a b, a + b = n → a ≤ b → ∀ k,
    (cU a b k : ℤ) = fU a b k ∧ (cD a b k : ℤ) = fD a b k := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro a b hn hab k
  constructor
  · rcases a with _ | a
    · simp [cU_zero, fU]
    · rw [cU_succ, ite_eq_left hab, ← id2 hab]
      obtain ⟨h1, h2⟩ := ih (a + b) (by lia) a b rfl (by lia) k
      split_ifs with hk
      · simp [h1]
      · obtain ⟨-, h3⟩ := ih (a + b) (by lia) a b rfl (by lia) (k - 1)
        push_cast
        rw [h1, h3]
  · rcases b with _ | b
    · simp [cD_zero, fD]
    · rw [cD_succ, cT_eq]
      simp only [fD, Nat.add_one_ne_zero, ite_false, add_tsub_cancel_right]
      rcases Nat.lt_or_ge b a with h | h
      · have ha : a = b + 1 := by lia
        have h3 := id3 (Nat.add_one_ne_zero b) k
        rw [add_tsub_cancel_right] at h3
        rw [cU_gt h, cD_gt h, ite_eq_right (by lia), ha, h3]
        simp
      · obtain ⟨h1, h2⟩ := ih (a + b) (by lia) a b rfl h k
        rw [← id1 h k]
        push_cast
        rw [h1, h2]

private lemma cT_diag (n k : ℕ) : (cT n n k : ℤ) = fT n n k := by
  obtain ⟨h1, h2⟩ := main_ind (n + n) n n rfl le_rfl k
  rw [cT_eq, ← id1 le_rfl k]
  push_cast
  rw [h1, h2]

private lemma fT_diag {n k : ℕ} (hn : n ≠ 0) (hk : k ≠ 0) :
    (n : ℤ) * fT n n k = (n.choose k * n.choose (k - 1) : ℕ) := by
  rw [← id1 le_rfl k, ite_eq_right (by lia)]
  have : fD n n k = 0 := by simp [fD, hn, id3 hn]
  rw [this]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by lia⟩
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by lia⟩
  simp only [fU, Nat.add_one_ne_zero, ite_false, or_self, add_tsub_cancel_right, add_zero]
  rcases Nat.lt_or_ge m j with hj | hj
  · rw [Nat.choose_eq_zero_of_lt (by lia : m + 1 < j + 1), Nat.choose_eq_zero_of_lt hj,
      Nat.choose_eq_zero_of_lt (by lia : m < j + 1)]
    simp
  have e1 := Nat.add_one_mul_choose_eq m j
  have e2 := Nat.choose_succ_right_eq (m + 1) j
  have e3 := Nat.choose_mul_succ_eq m (j + 1)
  have e1' : ((m : ℤ) + 1) * (m.choose j : ℕ) = ((m + 1).choose (j + 1) : ℕ) * ((j : ℤ) + 1) := by
    exact_mod_cast e1
  have e2' : (((m + 1).choose (j + 1) : ℕ) : ℤ) * ((j : ℤ) + 1) =
      ((m + 1).choose j : ℕ) * ((m : ℤ) + 1 - j) := by
    rw [show (m : ℤ) + 1 - j = ((m + 1 - j : ℕ) : ℤ) by lia]
    exact_mod_cast e2
  have e3' : ((m.choose (j + 1) : ℕ) : ℤ) * ((m : ℤ) + 1) =
      ((m + 1).choose (j + 1) : ℕ) * ((m : ℤ) - j) := by
    rw [show (m : ℤ) - j = ((m + 1 - (j + 1) : ℕ) : ℤ) by lia]
    exact_mod_cast e3
  push_cast
  set A : ℤ := (((m + 1).choose (j + 1) : ℕ) : ℤ)
  set E : ℤ := (((m + 1).choose j : ℕ) : ℤ)
  calc ((m : ℤ) + 1) * (A * (m.choose j : ℕ) - (m.choose (j + 1) : ℕ) * E)
      = A * (((m : ℤ) + 1) * (m.choose j : ℕ)) - E * ((m.choose (j + 1) : ℕ) * ((m : ℤ) + 1)) := by
        ring
    _ = A * (A * ((j : ℤ) + 1)) - E * (A * ((m : ℤ) - j)) := by rw [e1', e3']
    _ = A * (E * ((m : ℤ) + 1 - j)) - E * (A * ((m : ℤ) - j)) := by rw [e2']
    _ = A * E := by ring

private lemma narayana_eq_cT {n k : ℕ} (h : ¬(n = 1 ∧ k = 0)) : Nat.narayana n k = cT n n k := by
  have hc := cT_diag n k
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [fT, ite_true] at hc
    simp only [Nat.narayana, ite_true]
    split_ifs at hc ⊢ <;> lia
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have h0 : cT n n 0 = 0 := by
      have : fT n n 0 = 0 := by simp [fT, hn.ne']
      lia
    rw [h0, Nat.narayana, ite_eq_right hn.ne']
    simp only [Nat.choose_zero_right, zero_tsub, mul_one]
    exact Nat.div_eq_of_lt (by lia)
  · have h2 := fT_diag hn.ne' hk.ne'
    rw [← hc] at h2
    have h3 : n * cT n n k = n.choose k * n.choose (k - 1) := by exact_mod_cast h2
    rw [Nat.narayana, ite_eq_right hn.ne', ← h3, Nat.mul_div_cancel_left _ hn]

private lemma good_of_dyck (p : DyckWord) : Good p.toList := by
  intro i
  have h1 := p.count_U_eq_count_D
  have h2 := p.count_D_le_count_U i
  have e1 := congrArg (count U) (take_append_drop i p.toList)
  have e2 := congrArg (count D) (take_append_drop i p.toList)
  rw [count_append] at e1 e2
  lia

private lemma take_le_of_good {l : List DyckStep} (h1 : l.count U = l.count D) (h2 : Good l)
    (i : ℕ) : (l.take i).count D ≤ (l.take i).count U := by
  have h3 := h2 i
  have e1 := congrArg (count U) (take_append_drop i l)
  have e2 := congrArg (count D) (take_append_drop i l)
  rw [count_append] at e1 e2
  lia

private def peakEquiv (n k : ℕ) :
    {p : {p : DyckWord // p.semilength = n} // p.1.peakCount = k} ≃
      ((S n n).filter (fun l => peakCountList l = k)) where
  toFun p := ⟨p.1.1.toList, by
    rw [Finset.mem_filter, mem_S]
    refine ⟨⟨p.1.2, ?_, good_of_dyck _⟩, p.2⟩
    rw [← p.1.1.count_U_eq_count_D]
    exact p.1.2⟩
  invFun l := by
    have hl := (Finset.mem_filter.1 l.2).1
    rw [mem_S] at hl
    refine ⟨⟨⟨l.1, ?_, take_le_of_good ?_ hl.2.2⟩, hl.1⟩, (Finset.mem_filter.1 l.2).2⟩ <;> lia
  left_inv p := rfl
  right_inv l := rfl

private lemma card_eq_cT (n k : ℕ) :
    Fintype.card {p : {p : DyckWord // p.semilength = n} // p.1.peakCount = k} = cT n n k := by
  rw [Fintype.card_congr (peakEquiv n k), Fintype.card_coe]
  rfl

/-!
The uncorrected quotient identity fails at `(n, k) = (2, 0)`, and the
uncorrected fibre identity fails at `(n, k) = (1, 0)`, because subtraction
in `k - 1` is truncated.  The hypotheses below exclude exactly these
boundary failures.
-/

/-- The binomial quotient identity for positive semilength.
Corrected: the hypothesis `hk : k ≠ 0` was added (the original is false for `n = 2, k = 0`). -/
theorem _root_.Nat.narayana_mul (n k : ℕ) (hn : n ≠ 0) (hk : k ≠ 0) :
    n * Nat.narayana n k = Nat.choose n k * Nat.choose n (k - 1) := by
  have h2 := fT_diag hn hk
  rw [← cT_diag] at h2
  rw [narayana_eq_cT (by lia)]
  exact_mod_cast h2

/-- The number of Dyck words of semilength `n` with exactly `k` peaks is the
Narayana number.
Corrected: the hypothesis `¬(n = 1 ∧ k = 0)` was added (the original is false there). -/
theorem card_semilength_peakCount (n k : ℕ) (h : ¬(n = 1 ∧ k = 0)) :
    Fintype.card {p : {p : DyckWord // p.semilength = n} // p.1.peakCount = k} =
      Nat.narayana n k := by
  rw [card_eq_cT, narayana_eq_cT h]

/-- The excluded case of `card_semilength_peakCount`: the Dyck word `UD` has one peak. -/
theorem card_semilength_one_peakCount_zero :
    Fintype.card {p : {p : DyckWord // p.semilength = 1} // p.1.peakCount = 0} = 0 := by
  rw [card_eq_cT]
  simp [cT, S, peakCountList]

end DyckWord
