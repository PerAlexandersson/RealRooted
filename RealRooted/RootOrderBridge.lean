import Mathlib

/-!
# Root-order bridge

This file contains a purely order-theoretic bridge extracted from the
same-degree Chudnovsky--Seymour root-crossing target.
-/

namespace RealRooted

set_option linter.flexible false in
/-- If two finite multisets of reals have the same cardinality and their
counting functions differ by at most one at every threshold, then their
descending sorted lists satisfy the two interior crossing inequalities. -/
theorem rootCrossing_of_count_diff_le_one
    {M N : Multiset ℝ} {d : ℕ}
    (hM : M.card = d) (hN : N.card = d)
    (hcount : ∀ x : ℝ,
      ((M.filter (· ≤ x)).card : ℤ) - (N.filter (· ≤ x)).card ≤ 1 ∧
      ((N.filter (· ≤ x)).card : ℤ) - (M.filter (· ≤ x)).card ≤ 1) :
    (∀ j, 1 ≤ j → j < d →
        ((N.sort (· ≤ ·)).reverse).getD j 0 ≤
          ((M.sort (· ≤ ·)).reverse).getD (j - 1) 0) ∧
    (∀ j, 1 ≤ j → j < d →
        ((M.sort (· ≤ ·)).reverse).getD j 0 ≤
          ((N.sort (· ≤ ·)).reverse).getD (j - 1) 0) := by
  set sM := M.sort (· ≤ ·)
  set sN := N.sort (· ≤ ·)
  have hM_sorted : sM.Pairwise (· ≤ ·) := Multiset.pairwise_sort _ _
  have hN_sorted : sN.Pairwise (· ≤ ·) := Multiset.pairwise_sort _ _
  have hsM : sM.length = d := by aesop
  have hsN : sN.length = d := by aesop
  have hsM_eq : Multiset.ofList sM = M := Multiset.sort_eq M (· ≤ ·)
  have hsN_eq : Multiset.ofList sN = N := Multiset.sort_eq N (· ≤ ·)
  have h_helper (s : List ℝ) (hs : s.Pairwise (· ≤ ·)) (P : Multiset ℝ)
      (hsP : Multiset.ofList s = P) (x : ℝ) (k : ℕ) (hk : k < s.length) :
      s[k]! ≤ x ↔ k < (P.filter (· ≤ x)).card := by
    have h_helper (s : List ℝ) (hs : s.Pairwise (· ≤ ·)) (x : ℝ) (k : ℕ)
        (hk : k < s.length) : s[k]! ≤ x ↔ k < (s.filter (· ≤ x)).length := by
      induction s generalizing k with
      | nil =>
          simp at hk
      | cons hd tl ih =>
          rw [List.pairwise_cons] at hs
          rcases hs with ⟨hhd, htl⟩
          rcases k with _ | k
          · by_cases hdx : hd ≤ x
            · simp [hdx]
            · have hfilter : tl.filter (· ≤ x) = [] := by
                rw [List.filter_eq_nil_iff]
                intro y hy hyx
                exact hdx ((hhd y hy).trans (of_decide_eq_true hyx))
              exact iff_of_false hdx (by simp [hdx, hfilter])
          · have hk_tl : k < tl.length := by simpa using hk
            by_cases hdx : hd ≤ x
            · have ihk := ih htl k hk_tl
              simpa [hdx, Nat.succ_lt_succ_iff] using ihk
            · have hfilter : tl.filter (· ≤ x) = [] := by
                rw [List.filter_eq_nil_iff]
                intro y hy hyx
                exact hdx ((hhd y hy).trans (of_decide_eq_true hyx))
              have hnot : ¬tl[k]! ≤ x := by
                intro hyx
                have hmem : tl[k]! ∈ tl := by
                  rw [getElem!_pos tl k hk_tl]
                  exact List.getElem_mem hk_tl
                exact hdx ((hhd _ hmem).trans hyx)
              exact iff_of_false hnot (by simp [hdx, hfilter])
    convert h_helper s hs x k hk using 1
    aesop (simp_config := { singlePass := true })
  have h_reverse_getD (l : List ℝ) (hl : l.length = d) (i : ℕ) (hi : i < d) :
      l.reverse.getD i 0 = l[d - 1 - i]! := by
    grind +splitIndPred
  constructor <;> intros j hj₁ hj₂ <;>
    rw [h_reverse_getD _ hsN _ (by lia), h_reverse_getD _ hsM _ (by lia)]
  · rw [h_helper _ hN_sorted _ hsN_eq _ _ (by lia)]
    have := h_helper sM hM_sorted M hsM_eq (sM[d - 1 - (j - 1)]!)
      (d - 1 - (j - 1)) ?_ <;> norm_num at *
    · specialize hcount (sM[d - 1 - (j - 1)]?.getD default)
      lia
    · lia
  · rw [h_helper _ hM_sorted _ hsM_eq _ _ (by lia)]
    have := hcount (sN[d - 1 - (j - 1)]!)
    have := h_helper sN hN_sorted N hsN_eq (sN[d - 1 - (j - 1)]!)
      (d - 1 - (j - 1)) (by lia)
    norm_num at *
    lia

end RealRooted
