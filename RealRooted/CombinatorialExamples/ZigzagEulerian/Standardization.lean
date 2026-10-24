/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import RealRooted.CombinatorialExamples.ZigzagEulerian.GeneratingSeries
public import RealRooted.Combinatorics.ForcedGapWords
public import Mathlib.Data.Fin.Tuple.Sort

/-!
# Fence standardization for weak up-down words

Appendix A.2 of the zig-zag Eulerian proof: tie-breaking labels
run through two-position blocks in reverse order, with the even position
first inside each block. Sorting by letter and this label turns a weak
up-down word into its up-down permutation of ranks.
-/

@[expose] public section

open Finset

noncomputable section

namespace RealRooted.ZigzagEulerian

/-- The reversed-domino tie key: later two-position blocks come first,
and the even position precedes the odd position in each block. -/
def zigzagTieKey {n : ℕ} (i : Fin n) : OrderDual ℕ ×ₗ ℕ :=
  (OrderDual.toDual (i.val / 2), i.val % 2)

/-- The lexicographic key used to standardize a weak fence word. -/
def zigzagSortKey {n k : ℕ} (w : Fin n → Fin k) (i : Fin n) :
    Fin k ×ₗ (OrderDual ℕ ×ₗ ℕ) :=
  (w i, zigzagTieKey i)

/-- Rank each position by letter, breaking ties with the reversed-domino
label. The result maps a position to its rank. -/
def standardizeZigzagWord {n k : ℕ} (w : Fin n → Fin k) :
    Equiv.Perm (Fin n) :=
  (Tuple.sort (zigzagSortKey w)).symm

private theorem tieKey_lt_iff {n : ℕ} (i j : Fin n) :
    zigzagTieKey i < zigzagTieKey j ↔
      j.val / 2 < i.val / 2 ∨
        i.val / 2 = j.val / 2 ∧ i.val % 2 < j.val % 2 := by
  rw [show zigzagTieKey i = toLex (OrderDual.toDual (i.val / 2), i.val % 2) from rfl,
    show zigzagTieKey j = toLex (OrderDual.toDual (j.val / 2), j.val % 2) from rfl,
    Prod.Lex.toLex_lt_toLex]
  simp only [OrderDual.toDual_lt_toDual, OrderDual.toDual_inj]

private theorem tieKey_injective {n : ℕ} :
    Function.Injective (zigzagTieKey (n := n)) := by
  intro i j hij
  have hdiv : i.val / 2 = j.val / 2 := by
    have h := congrArg
      (fun z : OrderDual ℕ ×ₗ ℕ => OrderDual.ofDual z.1) hij
    simpa only [zigzagTieKey, OrderDual.ofDual_toDual] using h
  have hmod : i.val % 2 = j.val % 2 := by
    have h := congrArg (fun z : OrderDual ℕ ×ₗ ℕ => z.2) hij
    simpa only [zigzagTieKey] using h
  apply Fin.ext
  have hi := Nat.mod_add_div i.val 2
  have hj := Nat.mod_add_div j.val 2
  lia

private theorem sortKey_injective {n k : ℕ} (w : Fin n → Fin k) :
    Function.Injective (zigzagSortKey w) := by
  intro i j hij
  apply tieKey_injective
  have h := congrArg (fun z : Fin k ×ₗ (OrderDual ℕ ×ₗ ℕ) => z.2) hij
  simpa only [zigzagSortKey] using h

private theorem sorted_sortKey_strictMono {n k : ℕ} (w : Fin n → Fin k) :
    StrictMono (zigzagSortKey w ∘ Tuple.sort (zigzagSortKey w)) := by
  let key := zigzagSortKey w
  have hmono := Tuple.monotone_sort key
  intro i j hij
  have hle := hmono hij.le
  rcases hle.eq_or_lt with heq | hlt
  · have hpos := sortKey_injective w heq
    have heqij := (Tuple.sort key).injective hpos
    exact (hij.ne heqij).elim
  · exact hlt

/-- The letters in standardized rank order are weakly increasing. -/
theorem standardizeZigzagWord_rankWord_monotone {n k : ℕ} (w : Fin n → Fin k) :
    Monotone (fun r => w ((standardizeZigzagWord w).symm r)) := by
  have hmono := Tuple.monotone_sort (zigzagSortKey w)
  intro i j hij
  have hkey := hmono hij
  exact (Prod.Lex.le_iff'.mp hkey).1

/-- Consecutive ranks at which the reversed-domino label decreases. -/
def zigzagTieDescentSet {n : ℕ} (π : Equiv.Perm (Fin n)) : Finset (Fin n) :=
  univ.filter fun i => ∃ j : Fin n,
    i.val + 1 = j.val ∧ zigzagTieKey (π.symm j) < zigzagTieKey (π.symm i)

private theorem tieDescentSet_has_next {n : ℕ} (π : Equiv.Perm (Fin n))
    (i : Fin n) (hi : i ∈ zigzagTieDescentSet π) : i.val + 1 < n := by
  obtain ⟨j, hj, _⟩ := (mem_filter.mp hi).2
  have := j.isLt
  lia

/-- A standardized word increases strictly across every tie-label descent. -/
theorem standardizeZigzagWord_strict_at_tieDescent {n k : ℕ}
    (w : Fin n → Fin k) (i : Fin n)
    (hi : i ∈ zigzagTieDescentSet (standardizeZigzagWord w))
    (j : Fin n) (hij : i.val + 1 = j.val) :
    w ((standardizeZigzagWord w).symm i) <
      w ((standardizeZigzagWord w).symm j) := by
  let key := zigzagSortKey w
  have hsorted := sorted_sortKey_strictMono w (Fin.lt_def.mpr (by lia : i.val < j.val))
  have hlabel : zigzagTieKey ((standardizeZigzagWord w).symm j) <
      zigzagTieKey ((standardizeZigzagWord w).symm i) := by
    obtain ⟨j', hj', hdescent⟩ := (mem_filter.mp hi).2
    have hsame : j' = j := Fin.ext (by lia)
    simpa only [hsame] using hdescent
  rcases Prod.Lex.toLex_lt_toLex.mp hsorted with hstrict | ⟨_, hsmall⟩
  · exact hstrict
  · exact (lt_asymm hsmall hlabel).elim

private theorem tieKey_even_adjacent_lt {n : ℕ} (i j : Fin n)
    (hij : i.val + 1 = j.val) (heven : Even i.val) :
    zigzagTieKey i < zigzagTieKey j := by
  have hmod : i.val % 2 = 0 := Nat.even_iff.mp heven
  have hdiv : i.val / 2 = j.val / 2 := by lia
  have hrem : i.val % 2 < j.val % 2 := by lia
  apply Prod.Lex.toLex_lt_toLex.2
  right
  exact ⟨congrArg OrderDual.toDual hdiv, hrem⟩

private theorem tieKey_odd_adjacent_gt {n : ℕ} (i j : Fin n)
    (hij : i.val + 1 = j.val) (hodd : ¬Even i.val) :
    zigzagTieKey j < zigzagTieKey i := by
  have hmod : i.val % 2 = 1 := by
    have hne : i.val % 2 ≠ 0 := by exact mt Nat.even_iff.mpr hodd
    lia
  have hdiv : i.val / 2 < j.val / 2 := by lia
  apply Prod.Lex.toLex_lt_toLex.2
  left
  change i.val / 2 < j.val / 2
  exact hdiv

private theorem rank_lt_of_key_lt {n k : ℕ} (w : Fin n → Fin k)
    (i j : Fin n) (h : zigzagSortKey w i < zigzagSortKey w j) :
    standardizeZigzagWord w i < standardizeZigzagWord w j := by
  let key := zigzagSortKey w
  have hgraph : Tuple.graphEquiv₁ key i < Tuple.graphEquiv₁ key j := by
    apply Prod.Lex.toLex_lt_toLex.2
    exact Or.inl h
  have hrank := (Tuple.graphEquiv₂ key).symm.strictMono hgraph
  exact hrank

private theorem tieKey_descent_iff_forward_gap {n : ℕ}
    (π : Equiv.Perm (Fin n)) (hπ : IsUpDown π) (p q : Fin n)
    (hpq : π p < π q) :
    zigzagTieKey q < zigzagTieKey p ↔ p.val + 1 < q.val := by
  have hpmod := Nat.mod_add_div p.val 2
  have hqmod := Nat.mod_add_div q.val 2
  have hprem : p.val % 2 < 2 := Nat.mod_lt _ (by norm_num)
  have hqrem : q.val % 2 < 2 := Nat.mod_lt _ (by norm_num)
  constructor
  · intro hdesc
    rcases (tieKey_lt_iff q p).mp hdesc with hblock | ⟨hsame, hrem⟩
    · by_contra hfar
      have hadj : p.val + 1 = q.val := by lia
      have hodd : ¬Even p.val := by
        intro heven
        have he : p.val % 2 = 0 := Nat.even_iff.mp heven
        lia
      have hwrong := hπ p q hadj
      simp only [hodd, ↓reduceIte] at hwrong
      exact (not_lt_of_ge hwrong.le) hpq
    · have hqeven : Even q.val := Nat.even_iff.mpr (by lia)
      have hadj : q.val + 1 = p.val := by lia
      have hwrong := hπ q p hadj
      simp only [hqeven, ↓reduceIte] at hwrong
      exact False.elim ((not_lt_of_ge hwrong.le) hpq)
  · intro hgap
    apply (tieKey_lt_iff q p).mpr
    left
    lia

/-- On an up-down permutation, a label descent between consecutive ranks
is exactly the manuscript's forward inverse-position swap. -/
theorem zigzagTieDescentSet_eq_swapSet {n : ℕ} (π : Equiv.Perm (Fin n))
    (hπ : IsUpDown π) : zigzagTieDescentSet π = swapSet π := by
  ext i
  constructor
  · intro hi
    obtain ⟨j, hij, hdesc⟩ := (mem_filter.mp hi).2
    have hpq : π (π.symm i) < π (π.symm j) := by
      simpa using (Fin.lt_def.mpr (by lia : i.val < j.val))
    have hgap := (tieKey_descent_iff_forward_gap π hπ (π.symm i) (π.symm j) hpq).mp hdesc
    exact mem_filter.mpr ⟨mem_univ _, ⟨j, hij, hgap⟩⟩
  · intro hi
    obtain ⟨j, hij, hgap⟩ := (mem_filter.mp hi).2
    have hpq : π (π.symm i) < π (π.symm j) := by
      simpa using (Fin.lt_def.mpr (by lia : i.val < j.val))
    have hdesc := (tieKey_descent_iff_forward_gap π hπ (π.symm i) (π.symm j) hpq).mpr hgap
    exact mem_filter.mpr ⟨mem_univ _, ⟨j, hij, hdesc⟩⟩

/-- Standardizing an actual weak up-down word produces an actual up-down
permutation in the manuscript's zero-based convention. -/
theorem standardizeZigzagWord_isUpDown {n k : ℕ} (w : Fin n → Fin k)
    (hw : IsWeakUpDown w) : IsUpDown (standardizeZigzagWord w) := by
  intro i j hij
  by_cases heven : Even i.val
  · simp only [heven, ↓reduceIte]
    have hword := hw i j hij
    simp only [heven, ↓reduceIte] at hword
    apply rank_lt_of_key_lt w i j
    apply Prod.Lex.toLex_lt_toLex.2
    rcases hword.eq_or_lt with heq | hlt
    · exact Or.inr ⟨heq, tieKey_even_adjacent_lt i j hij heven⟩
    · exact Or.inl hlt
  · simp only [heven, ↓reduceIte]
    have hword := hw i j hij
    simp only [heven, ↓reduceIte] at hword
    apply rank_lt_of_key_lt w j i
    apply Prod.Lex.toLex_lt_toLex.2
    rcases hword.eq_or_lt with heq | hlt
    · exact Or.inr ⟨heq, tieKey_odd_adjacent_gt i j hij heven⟩
    · exact Or.inl hlt

private theorem strictMono_of_adjacent {n : ℕ} {α : Type*} [Preorder α]
    (f : Fin n → α)
    (h : ∀ i j : Fin n, i.val + 1 = j.val → f i < f j) : StrictMono f := by
  cases n with
  | zero =>
      intro i
      exact Fin.elim0 i
  | succ m =>
      apply Fin.strictMono_iff_lt_succ.mpr
      intro i
      exact h i.castSucc i.succ rfl

/-- The forced gaps recover the prescribed permutation after sorting the
letters with the reversed-domino tie labels. -/
theorem standardizeZigzagWord_of_forcedGaps {n k : ℕ}
    (π : Equiv.Perm (Fin n)) (v : Fin n → Fin k) (hv : Monotone v)
    (hgap : ∀ i ∈ zigzagTieDescentSet π, ∀ j : Fin n,
      i.val + 1 = j.val → v i < v j) :
    standardizeZigzagWord (fun p => v (π p)) = π := by
  let w : Fin n → Fin k := fun p => v (π p)
  have hsort : π.symm = Tuple.sort (zigzagSortKey w) := by
    apply Tuple.eq_sort_iff'.mpr
    apply strictMono_of_adjacent
    intro i j hij
    have hle : v i ≤ v j := hv (Fin.le_def.mpr (by lia))
    have hne : π.symm i ≠ π.symm j := by
      intro heq
      have := π.symm.injective heq
      exact (Fin.ne_of_lt (Fin.lt_def.mpr (by lia : i.val < j.val))) this
    have hkey : zigzagSortKey w (π.symm i) < zigzagSortKey w (π.symm j) := by
      have hfirsti : w (π.symm i) = v i := by simp only [w, Equiv.apply_symm_apply]
      have hfirstj : w (π.symm j) = v j := by simp only [w, Equiv.apply_symm_apply]
      change toLex (w (π.symm i), zigzagTieKey (π.symm i)) <
        toLex (w (π.symm j), zigzagTieKey (π.symm j))
      rw [hfirsti, hfirstj]
      by_cases heq : v i = v j
      · have hnotdesc : ¬zigzagTieKey (π.symm j) < zigzagTieKey (π.symm i) := by
          intro hdesc
          have hi : i ∈ zigzagTieDescentSet π :=
            mem_filter.mpr ⟨mem_univ _, ⟨j, hij, hdesc⟩⟩
          exact (ne_of_lt (hgap i hi j hij)) heq
        have hlabelne : zigzagTieKey (π.symm i) ≠ zigzagTieKey (π.symm j) := by
          intro hlabel
          exact hne (tieKey_injective hlabel)
        have hlabel : zigzagTieKey (π.symm i) < zigzagTieKey (π.symm j) :=
          lt_of_le_of_ne (le_of_not_gt hnotdesc) hlabelne
        apply Prod.Lex.toLex_lt_toLex.2
        exact Or.inr ⟨heq, hlabel⟩
      · have hlt : v i < v j := lt_of_le_of_ne hle heq
        apply Prod.Lex.toLex_lt_toLex.2
        exact Or.inl hlt
    apply Prod.Lex.toLex_lt_toLex.2
    exact Or.inl hkey
  have hsymm : (Tuple.sort (zigzagSortKey w)).symm = π := by
    rw [← hsort]
    exact π.symm_symm
  exact hsymm

/-- Pulling a monotone rank word back through an up-down permutation gives
a weak up-down word. -/
theorem isWeakUpDown_of_rankWord {n k : ℕ} (π : Equiv.Perm (Fin n))
    (hπ : IsUpDown π) (v : Fin n → Fin k) (hv : Monotone v) :
    IsWeakUpDown (fun p => v (π p)) := by
  intro i j hij
  have hpq := hπ i j hij
  by_cases heven : Even i.val
  · simp only [heven, ↓reduceIte] at hpq ⊢
    exact hv hpq.le
  · simp only [heven, ↓reduceIte] at hpq ⊢
    exact hv hpq.le

/-- Fence standardization as a bijection with up-down permutations
decorated by monotone rank words having their prescribed strict gaps. -/
def zigzagStandardizationEquiv (n k : ℕ) :
    {w : Fin n → Fin k // IsWeakUpDown w} ≃
      Σ π : {π : Equiv.Perm (Fin n) // IsUpDown π},
        {v : Fin n → Fin k //
          v ∈ ForcedGapWords.forcedGapWords n k (swapSet π.1)} where
  toFun w := by
    let π := standardizeZigzagWord w.1
    have hπ : IsUpDown π := standardizeZigzagWord_isUpDown w.1 w.2
    let v : Fin n → Fin k := fun r => w.1 (π.symm r)
    refine ⟨⟨π, hπ⟩, ⟨v, ?_⟩⟩
    apply mem_filter.mpr
    refine ⟨mem_univ _, standardizeZigzagWord_rankWord_monotone w.1, ?_⟩
    intro i hi j hij
    rw [← zigzagTieDescentSet_eq_swapSet π hπ] at hi
    exact standardizeZigzagWord_strict_at_tieDescent w.1 i hi j hij
  invFun pair := by
    rcases pair with ⟨⟨π, hπ⟩, ⟨v, hv⟩⟩
    exact ⟨fun p => v (π p), isWeakUpDown_of_rankWord π hπ v (mem_filter.mp hv).2.1⟩
  left_inv := by
    intro w
    apply Subtype.ext
    funext p
    simp only [Equiv.symm_apply_apply]
  right_inv := by
    rintro ⟨⟨π, hπ⟩, ⟨v, hv⟩⟩
    have hvmono : Monotone v := (mem_filter.mp hv).2.1
    have hgap : ∀ i ∈ zigzagTieDescentSet π, ∀ j : Fin n,
        i.val + 1 = j.val → v i < v j := by
      intro i hi j hij
      rw [zigzagTieDescentSet_eq_swapSet π hπ] at hi
      exact (mem_filter.mp hv).2.2 i hi j hij
    have hstd := standardizeZigzagWord_of_forcedGaps π v hvmono hgap
    apply Sigma.ext
    · exact Subtype.ext hstd
    · simp only [hstd, Equiv.apply_symm_apply]
      apply (Subtype.heq_iff_coe_eq (by intro u; simp only [hstd])).2
      rfl

/-- Appendix A.2, formula (A.4): actual weak fence words are counted by the
binomial weight of the actual swap statistic on up-down permutations. -/
theorem weakUpDownWordCount_eq_zigzagBinomialWordCount (n k : ℕ) :
    weakUpDownWordCount n k = zigzagBinomialWordCount n k := by
  classical
  have hleft : weakUpDownWordCount n k =
      Fintype.card {w : Fin n → Fin k // IsWeakUpDown w} := by
    simp only [weakUpDownWordCount, Fintype.card_subtype]
  rw [hleft, Fintype.card_congr (zigzagStandardizationEquiv n k), Fintype.card_sigma]
  calc
    (∑ π : {π : Equiv.Perm (Fin n) // IsUpDown π},
        Fintype.card {v : Fin n → Fin k //
          v ∈ ForcedGapWords.forcedGapWords n k (swapSet π.1)}) =
      ∑ π : {π : Equiv.Perm (Fin n) // IsUpDown π},
        (ForcedGapWords.forcedGapWords n k (swapSet π.1)).card := by
          apply Finset.sum_congr rfl
          intro π _
          exact Fintype.card_coe _
    _ = ∑ π : {π : Equiv.Perm (Fin n) // IsUpDown π},
          Nat.choose (k + n - 1 - swapCount π.1) n := by
          apply Finset.sum_congr rfl
          intro π _
          exact ForcedGapWords.forcedGapWords_card n k (swapSet π.1) (by
            intro i hi
            obtain ⟨j, hj, _⟩ := (mem_filter.mp hi).2
            have := j.isLt
            lia)
    _ = zigzagBinomialWordCount n k := by
          unfold zigzagBinomialWordCount
          rw [← Finset.sum_subtype_eq_sum_filter]
          simp only [Finset.subtype_univ]

end RealRooted.ZigzagEulerian
