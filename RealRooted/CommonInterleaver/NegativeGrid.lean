/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import RealRooted.CommonInterleaver.RootDesc
import RealRooted.CommonInterleaver.StrictSlots
import Mathlib.Tactic

/-!
# A strict common grid below zero

Adjacent cross-slot separation gives one negative grid for a finite family.
The grid comes with exact upper root counts, hence a common alternating sign pattern.
-/

public section

noncomputable section

open Polynomial Finset

namespace RealRooted

private theorem exists_descending_separator {ι : Type*} [Finite ι] [Nonempty ι]
    (r : ι → ℕ → ℝ) {d : ℕ}
    (hnonpos : ∀ i j, j < d → r i j ≤ 0)
    (hcross : ∀ i i' j, 0 < j → j < d → r i j < r i' (j - 1))
    (j : Fin d) :
    ∃ c : ℝ, c < 0 ∧ (∀ i, c < r i j.val) ∧
      ∀ i, j.val + 1 < d → r i (j.val + 1) < c := by
  classical
  let := Fintype.ofFinite ι
  let lo n := univ.inf' univ_nonempty (fun i => r i n)
  let hi n := univ.sup' univ_nonempty (fun i => r i n)
  have hlo i n : lo n ≤ r i n := inf'_le (fun i => r i n) (mem_univ i)
  have hhi i n : r i n ≤ hi n := le_sup' (fun i => r i n) (mem_univ i)
  by_cases hlast : j.val + 1 < d
  · have hgap : hi (j.val + 1) < lo j.val := by
      apply (sup'_lt_iff univ_nonempty).mpr
      intro i _
      apply (lt_inf'_iff univ_nonempty).mpr
      intro i' _
      simpa only [Nat.add_sub_cancel] using hcross i i' (j.val + 1) (by lia) hlast
    obtain ⟨c, hcl, hcu⟩ := exists_between hgap
    refine ⟨c, ?_, fun i => hcu.trans_le (hlo i j.val), fun i _ => (hhi i _).trans_lt hcl⟩
    exact (hcu.trans_le (hlo (Classical.ofNonempty : ι) _)).trans_le
      (hnonpos _ _ j.isLt)
  · refine ⟨lo j.val - 1, ?_, ?_, ?_⟩
    · have := (hlo (Classical.ofNonempty : ι) j.val).trans (hnonpos _ _ j.isLt)
      linarith
    · intro i
      have := hlo i j.val
      linarith
    · intro i hh
      exact (hlast hh).elim

/-- Strict cross-slot separation supplies a common negative grid with the
same upper root count for every family member at each grid point. -/
theorem exists_negative_root_grid {ι : Type*} [Finite ι] [Nonempty ι]
    (f : ι → ℝ[X]) {m : ℕ}
    (hs : ∀ i, (f i).Splits) (hd : ∀ i, (f i).natDegree = m + 1)
    (hn : ∀ i, (f i).roots.Nodup)
    (hneg : ∀ i x, x ∈ (f i).roots → x ≤ 0)
    (hcross : ∀ i i' j, 0 < j → j < m + 1 →
      (rootSeqDesc (f i)).getD j 0 < (rootSeqDesc (f i')).getD (j - 1) 0) :
    ∃ c : Fin (m + 1) → ℝ, StrictAnti c ∧ (∀ j, c j < 0) ∧
      ∀ i j, ¬ (f i).IsRoot (c j) ∧
        ((f i).roots.filter (c j < ·)).card = j.val + 1 := by
  classical
  let := Fintype.ofFinite ι
  let r i j := (rootSeqDesc (f i)).getD j 0
  have hlen i : (rootSeqDesc (f i)).length = m + 1 := (rootSeqDesc_length (hs i)).trans (hd i)
  have hr i j (hj : j < m + 1) : r i j ∈ (f i).roots :=
    rootSeqDesc_getD_mem_roots (by rw [hlen i]; exact hj)
  have hnonpos i j hj : r i j ≤ 0 := hneg i _ (hr i j hj)
  choose c hcn hcupper hclower using fun j : Fin (m + 1) =>
    exists_descending_separator r hnonpos hcross j
  have hcanti : StrictAnti c := by
    apply Fin.strictAnti_iff_succ_lt.mpr
    intro j
    let i : ι := Classical.ofNonempty
    exact (hcupper j.succ i).trans (hclower j.castSucc i (Nat.succ_lt_succ j.isLt))
  refine ⟨c, hcanti, hcn, ?_⟩
  intro i j
  let l := rootSeqDesc (f i)
  have hleni : l.length = m + 1 := hlen i
  have hsorted : Antitone l.get :=
    (List.sortedGE_iff_pairwise.mpr rootSeqDesc_pairwise).antitone_get
  have hconv (a : Fin l.length) : l.get a = r i a.val := by
    simp [r, l, a.isLt]
  have hlocation (x : ℝ) (hx : x ∈ (f i).roots) : x ≠ c j := by
    have hxl : x ∈ l := by
      simpa only [l, rootSeqDesc, List.mem_reverse, Multiset.mem_sort] using hx
    obtain ⟨a, ha⟩ := List.get_of_mem hxl
    have haz : r i a.val = x := (hconv a).symm.trans ha
    by_cases haj : a.val ≤ j.val
    · have hh := hsorted (show a ≤ ⟨j.val, j.isLt.trans_eq hleni.symm⟩ from haj)
      rw [hconv, hconv, haz] at hh
      exact ((hcupper j i).trans_le hh).ne'
    · have haj' : j.val + 1 < m + 1 := by have := a.isLt.trans_eq hleni; lia
      have hh := hsorted (show (⟨j.val + 1, haj'.trans_eq hleni.symm⟩ : Fin l.length) ≤ a
        from by change j.val + 1 ≤ a.val; lia)
      rw [hconv, hconv, haz] at hh
      exact (hh.trans_lt (hclower j i haj')).ne
  constructor
  · intro hx
    have hfn : f i ≠ 0 := ne_zero_of_mem_roots (hr i j.val j.isLt)
    exact hlocation _ ((mem_roots hfn).mpr hx) rfl
  · apply card_roots_gt_of_rootSeqDesc_gap (hn i) ⟨j.val, j.isLt.trans_eq hleni.symm⟩ (c j)
    · rw [hconv]
      exact hcupper j i
    · intro hnext
      rw [hconv]
      exact hclower j i (hnext.trans_eq hleni)

end RealRooted
