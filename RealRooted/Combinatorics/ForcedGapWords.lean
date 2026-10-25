/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Fintype.Card
public import Mathlib.Order.Fin.Basic
public import Mathlib.Tactic

/-!
# Weakly increasing words with prescribed strict gaps

The marked positions in a word must be strict ascents; other positions may be
equalities.  The resulting count depends only on the number of marked gaps.
This is the finite stars-and-bars lemma used by fence standardization in
Appendix A.2 of the zig-zag Eulerian proof.
-/

@[expose] public section

open Finset

noncomputable section

namespace RealRooted.ForcedGapWords

/-- Weakly increasing words with strict rises at every gap in `D`.
The assumption that marked indices have successors is made in the cardinality theorem. -/
def forcedGapWords (n k : ℕ) (D : Finset (Fin n)) : Finset (Fin n → Fin k) := by
  classical
  exact (univ : Finset (Fin n → Fin k)).filter fun v =>
    Monotone v ∧ ∀ i ∈ D, ∀ j : Fin n, i.val + 1 = j.val → v i < v j

/-- Increasing `n`-tuples in `[N]`, prior to identifying them with `n`-subsets. -/
private def strictTuples (n N : ℕ) : Finset (Fin n → Fin N) := by
  classical
  exact (univ : Finset (Fin n → Fin N)).filter StrictMono

/-- An increasing tuple enumerates a unique subset of the target alphabet. -/
private def strictTupleSubset {n N : ℕ} (f : {f : Fin n → Fin N // StrictMono f}) :
    {s : Finset (Fin N) // s.card = n} := by
  classical
  refine ⟨Finset.univ.image f.1, ?_⟩
  rw [Finset.card_image_of_injective _ f.2.injective]
  simp

/-- Every `n`-subset has a unique increasing enumeration. -/
private def subsetStrictTuple {n N : ℕ} (s : {s : Finset (Fin N) // s.card = n}) :
    {f : Fin n → Fin N // StrictMono f} :=
  ⟨s.1.orderEmbOfFin s.2, (s.1.orderEmbOfFin s.2).strictMono⟩

private theorem strictTupleSubset_left_inv {n N : ℕ}
    (f : {f : Fin n → Fin N // StrictMono f}) :
    subsetStrictTuple (strictTupleSubset f) = f := by
  apply Subtype.ext
  have huniq := Finset.orderEmbOfFin_unique (strictTupleSubset f).2
    (f := f.1) (by intro i; exact Finset.mem_image_of_mem _ (Finset.mem_univ i)) f.2
  exact huniq.symm

private theorem strictTupleSubset_right_inv {n N : ℕ}
    (s : {s : Finset (Fin N) // s.card = n}) :
    strictTupleSubset (subsetStrictTuple s) = s := by
  apply Subtype.ext
  exact Finset.image_orderEmbOfFin_univ s.1 s.2

/-- Increasing tuples are equinumerous with subsets of the same cardinality. -/
private def strictTupleSubsetEquiv (n N : ℕ) :
    {f : Fin n → Fin N // StrictMono f} ≃
      {s : Finset (Fin N) // s.card = n} where
  toFun := strictTupleSubset
  invFun := subsetStrictTuple
  left_inv := strictTupleSubset_left_inv
  right_inv := strictTupleSubset_right_inv

/-- A finite increasing-tuple count, including `n = 0` and `N < n`. -/
private theorem strictTuples_card (n N : ℕ) :
    (strictTuples n N).card = Nat.choose N n := by
  classical
  have hcard : (strictTuples n N).card =
      Fintype.card {f : Fin n → Fin N // StrictMono f} := by
    simp [strictTuples, Fintype.card_subtype]
  rw [hcard, Fintype.card_congr (strictTupleSubsetEquiv n N)]
  rw [Fintype.card_subtype]
  have hpow : (Finset.powersetCard n (univ : Finset (Fin N))).card =
      Nat.choose N n := by simp
  rw [← hpow]
  congr 1
  ext s
  simp

/-- The number of marked gaps strictly before position `i`. -/
private def gapPrefix {n : ℕ} (D : Finset (Fin n)) (i : Fin n) : ℕ :=
  (D.filter fun j => j < i).card

private theorem gapPrefix_le_val {n : ℕ} (D : Finset (Fin n)) (i : Fin n) :
    gapPrefix D i ≤ i.val := by
  have hs : D.filter (fun j => j < i) ⊆ Finset.Iio i := by
    intro j hj
    exact Finset.mem_Iio.mpr (Finset.mem_filter.mp hj).2
  exact (Finset.card_le_card hs).trans (by simp)

private theorem gapPrefix_last {n : ℕ} (hn : 0 < n) (D : Finset (Fin n))
    (hD : ∀ i ∈ D, i.val + 1 < n) :
    gapPrefix D ⟨n - 1, by lia⟩ = D.card := by
  unfold gapPrefix
  rw [Finset.filter_eq_self.mpr]
  intro i hi
  have h := hD i hi
  exact Fin.lt_def.mpr (by lia)

private theorem gapPrefix_succ {n : ℕ} (D : Finset (Fin (n + 1))) (i : Fin n) :
    gapPrefix D i.succ =
      gapPrefix D i.castSucc + if i.castSucc ∈ D then 1 else 0 := by
  have hcmp (j : Fin (n + 1)) :
      j < i.succ ↔ j = i.castSucc ∨ j < i.castSucc := by
    constructor
    · intro hj
      by_cases heq : j.val = i.val
      · exact Or.inl (Fin.ext heq)
      · have hsucc : i.succ.val = i.val + 1 := rfl
        have hcast : i.castSucc.val = i.val := rfl
        exact Or.inr (Fin.lt_def.mpr (by have := Fin.lt_def.mp hj; lia))
    · rintro (rfl | hj)
      · exact i.castSucc_lt_succ
      · exact hj.trans i.castSucc_lt_succ
  by_cases hi : i.castSucc ∈ D
  · have heq : D.filter (fun j => j < i.succ) =
        insert i.castSucc (D.filter fun j => j < i.castSucc) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_insert, hcmp]
      aesop
    have hnot : i.castSucc ∉ D.filter (fun j => j < i.castSucc) := by simp
    simp [gapPrefix, heq, hi, Finset.card_insert_of_notMem hnot]
  · have heq : D.filter (fun j => j < i.succ) =
        D.filter (fun j => j < i.castSucc) := by
      ext j
      simp only [Finset.mem_filter, hcmp]
      aesop
    simp [gapPrefix, heq, hi]

private def shiftedRank {n k : ℕ} (D : Finset (Fin (n + 1)))
    (v : Fin (n + 1) → Fin k) (i : Fin (n + 1)) : ℕ :=
  (v i).val + i.val - gapPrefix D i

private theorem shiftedRank_strictMono {n k : ℕ} (D : Finset (Fin (n + 1)))
    (v : Fin (n + 1) → Fin k) (hv : v ∈ forcedGapWords (n + 1) k D) :
    StrictMono (shiftedRank D v) := by
  obtain ⟨hmono, hgap⟩ := (Finset.mem_filter.mp hv).2
  apply Fin.strictMono_iff_lt_succ.mpr
  intro i
  have hp := gapPrefix_succ D i
  have hpLe := gapPrefix_le_val D i.castSucc
  have hm := hmono i.castSucc_lt_succ.le
  have hmVal := Fin.le_def.mp hm
  have hcast : i.castSucc.val = i.val := rfl
  have hsucc : i.succ.val = i.val + 1 := rfl
  by_cases hi : i.castSucc ∈ D
  · have hs := hgap i.castSucc hi i.succ rfl
    have hsVal := Fin.lt_def.mp hs
    unfold shiftedRank
    simp only [Fin.val_castSucc, Fin.val_succ]
    rw [hp]
    simp only [hi, ↓reduceIte]
    lia
  · unfold shiftedRank
    simp only [Fin.val_castSucc, Fin.val_succ]
    rw [hp]
    simp only [hi, ↓reduceIte, add_zero]
    lia

private theorem shiftedRank_lt {n k : ℕ} (D : Finset (Fin (n + 1)))
    (hD : ∀ i ∈ D, i.val + 1 < n + 1)
    (v : Fin (n + 1) → Fin k) (hv : v ∈ forcedGapWords (n + 1) k D)
    (i : Fin (n + 1)) : shiftedRank D v i < k + n - D.card := by
  have hm := (shiftedRank_strictMono D v hv).monotone i.le_last
  have hl : gapPrefix D (Fin.last n) = D.card := by
    have hidx : (Fin.last n : Fin (n + 1)) = ⟨n + 1 - 1, by lia⟩ :=
      Fin.ext (by simp)
    rw [hidx]
    exact gapPrefix_last (Nat.succ_pos n) D hD
  have hDcard : D.card ≤ n := by
    rw [← hl]
    simpa using gapPrefix_le_val D (Fin.last n)
  have hvLast := (v (Fin.last n)).isLt
  unfold shiftedRank at hm ⊢
  rw [hl] at hm
  simp only [Fin.val_last] at hm
  have hlast : (Fin.last n).val = n := rfl
  lia

private def shiftedTuple {n k : ℕ} (D : Finset (Fin (n + 1)))
    (hD : ∀ i ∈ D, i.val + 1 < n + 1)
    (v : {v : Fin (n + 1) → Fin k // v ∈ forcedGapWords (n + 1) k D}) :
    {g : Fin (n + 1) → Fin (k + n - D.card) // StrictMono g} := by
  refine ⟨fun i => ⟨shiftedRank D v.1 i, shiftedRank_lt D hD v.1 v.2 i⟩, ?_⟩
  intro i j hij
  exact Fin.lt_def.mpr ((shiftedRank_strictMono D v.1 v.2) hij)

private theorem strictTuple_ge_index {n N : ℕ}
    (g : Fin (n + 1) → Fin N) (hg : StrictMono g) (i : Fin (n + 1)) :
    i.val ≤ (g i).val := by
  induction i using Fin.induction with
  | zero => simp
  | succ i ih =>
    have hs := Fin.strictMono_iff_lt_succ.mp hg i
    have hval := Fin.lt_def.mp hs
    have hsucc : i.succ.val = i.val + 1 := rfl
    have hcast : i.castSucc.val = i.val := rfl
    lia

private def unshiftedRank {n N : ℕ} (D : Finset (Fin (n + 1)))
    (g : Fin (n + 1) → Fin N) (i : Fin (n + 1)) : ℕ :=
  (g i).val - i.val + gapPrefix D i

private theorem unshiftedRank_monotone {n N : ℕ}
    (D : Finset (Fin (n + 1)))
    (g : Fin (n + 1) → Fin N) (hg : StrictMono g) :
    Monotone (unshiftedRank D g) := by
  apply Fin.monotone_iff_le_succ.mpr
  intro i
  have hs := Fin.strictMono_iff_lt_succ.mp hg i
  have hge := strictTuple_ge_index g hg i.castSucc
  have hp := gapPrefix_succ D i
  unfold unshiftedRank
  simp only [Fin.val_castSucc, Fin.val_succ]
  rw [hp]
  split_ifs <;> lia

private theorem unshiftedRank_strict_gap {n N : ℕ}
    (D : Finset (Fin (n + 1)))
    (g : Fin (n + 1) → Fin N) (hg : StrictMono g)
    (i : Fin n) (hi : i.castSucc ∈ D) :
    unshiftedRank D g i.castSucc < unshiftedRank D g i.succ := by
  have hs := Fin.strictMono_iff_lt_succ.mp hg i
  have hge := strictTuple_ge_index g hg i.castSucc
  have hp := gapPrefix_succ D i
  unfold unshiftedRank
  simp only [Fin.val_castSucc, Fin.val_succ]
  rw [hp]
  simp only [hi, ↓reduceIte]
  lia

private theorem unshiftedRank_lt {n k : ℕ} (D : Finset (Fin (n + 1)))
    (hD : ∀ i ∈ D, i.val + 1 < n + 1)
    (g : Fin (n + 1) → Fin (k + n - D.card)) (hg : StrictMono g)
    (i : Fin (n + 1)) : unshiftedRank D g i < k := by
  have hm := (unshiftedRank_monotone D g hg) i.le_last
  have hl : gapPrefix D (Fin.last n) = D.card := by
    have hidx : (Fin.last n : Fin (n + 1)) = ⟨n + 1 - 1, by lia⟩ :=
      Fin.ext (by simp)
    rw [hidx]
    exact gapPrefix_last (Nat.succ_pos n) D hD
  have hDcard : D.card ≤ n := by
    rw [← hl]
    simpa using gapPrefix_le_val D (Fin.last n)
  have hgLast := (g (Fin.last n)).isLt
  have hindex := strictTuple_ge_index g hg (Fin.last n)
  unfold unshiftedRank at hm ⊢
  rw [hl] at hm
  simp only [Fin.val_last] at hm
  have hlast : (Fin.last n).val = n := rfl
  lia

private def unshiftedTuple {n k : ℕ} (D : Finset (Fin (n + 1)))
    (hD : ∀ i ∈ D, i.val + 1 < n + 1)
    (g : {g : Fin (n + 1) → Fin (k + n - D.card) // StrictMono g}) :
    {v : Fin (n + 1) → Fin k // v ∈ forcedGapWords (n + 1) k D} := by
  refine ⟨fun i => ⟨unshiftedRank D g.1 i, unshiftedRank_lt D hD g.1 g.2 i⟩, ?_⟩
  rw [forcedGapWords, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_, ?_⟩
  · intro i j hij
    exact Fin.le_def.mpr ((unshiftedRank_monotone D g.1 g.2) hij)
  · intro i hi j hij
    have hiVal : i.val < n := by have := hD i hi; lia
    have hidx : i = (⟨i.val, hiVal⟩ : Fin n).castSucc := Fin.ext rfl
    have hjdx : j = (⟨i.val, hiVal⟩ : Fin n).succ := Fin.ext hij.symm
    have hi' : (⟨i.val, hiVal⟩ : Fin n).castSucc ∈ D := hidx ▸ hi
    rw [hidx, hjdx]
    exact Fin.lt_def.mpr (unshiftedRank_strict_gap D g.1 g.2 ⟨i.val, hiVal⟩ hi')

private theorem unshifted_shifted {n k : ℕ} (D : Finset (Fin (n + 1)))
    (hD : ∀ i ∈ D, i.val + 1 < n + 1)
    (v : {v : Fin (n + 1) → Fin k // v ∈ forcedGapWords (n + 1) k D}) :
    unshiftedTuple D hD (shiftedTuple D hD v) = v := by
  apply Subtype.ext
  funext i
  apply Fin.ext
  have hge := strictTuple_ge_index (shiftedTuple D hD v).1
    (shiftedTuple D hD v).2 i
  have hp := gapPrefix_le_val D i
  change i.val ≤ shiftedRank D v.1 i at hge
  change shiftedRank D v.1 i - i.val + gapPrefix D i = (v.1 i).val
  unfold shiftedRank at hge ⊢
  lia

private theorem shifted_unshifted {n k : ℕ} (D : Finset (Fin (n + 1)))
    (hD : ∀ i ∈ D, i.val + 1 < n + 1)
    (g : {g : Fin (n + 1) → Fin (k + n - D.card) // StrictMono g}) :
    shiftedTuple D hD (unshiftedTuple D hD g) = g := by
  apply Subtype.ext
  funext i
  apply Fin.ext
  have hge := strictTuple_ge_index g.1 g.2 i
  have hp := gapPrefix_le_val D i
  change unshiftedRank D g.1 i + i.val - gapPrefix D i = (g.1 i).val
  unfold unshiftedRank
  lia

/-- The rank shift removes prescribed strict rises, then turns a weak word
into an increasing tuple. -/
private def forcedGapEquiv {n k : ℕ} (D : Finset (Fin (n + 1)))
    (hD : ∀ i ∈ D, i.val + 1 < n + 1) :
    {v : Fin (n + 1) → Fin k // v ∈ forcedGapWords (n + 1) k D} ≃
      {g : Fin (n + 1) → Fin (k + n - D.card) // StrictMono g} where
  toFun := shiftedTuple D hD
  invFun := unshiftedTuple D hD
  left_inv := unshifted_shifted D hD
  right_inv := shifted_unshifted D hD

/-- Prescribing `s` strict gaps among the `n - 1` possible gaps removes `s`
available letter levels from the ordinary multichoose count. -/
theorem forcedGapWords_card (n k : ℕ) (D : Finset (Fin n))
    (hD : ∀ i ∈ D, i.val + 1 < n) :
    (forcedGapWords n k D).card = Nat.choose (k + n - 1 - D.card) n := by
  classical
  cases n with
  | zero =>
    have hDEmpty : D = ∅ := by
      ext i
      exact Fin.elim0 i
    subst D
    have hmono (v : Fin 0 → Fin k) : Monotone v := by
      intro i
      exact Fin.elim0 i
    simp [forcedGapWords, hmono]
  | succ n =>
    have hcard : (forcedGapWords (n + 1) k D).card =
        Fintype.card {v : Fin (n + 1) → Fin k //
          v ∈ forcedGapWords (n + 1) k D} := by
      simp [forcedGapWords, Fintype.card_subtype]
    calc
      (forcedGapWords (n + 1) k D).card =
          Fintype.card {v : Fin (n + 1) → Fin k //
            v ∈ forcedGapWords (n + 1) k D} := hcard
      _ = Fintype.card {g : Fin (n + 1) → Fin (k + n - D.card) //
            StrictMono g} := Fintype.card_congr (forcedGapEquiv D hD)
      _ = Nat.choose (k + n - D.card) (n + 1) := by
        rw [← strictTuples_card]
        simp [strictTuples, Fintype.card_subtype]
      _ = Nat.choose (k + (n + 1) - 1 - D.card) (n + 1) := by congr 1

end RealRooted.ForcedGapWords
