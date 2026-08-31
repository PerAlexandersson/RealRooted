import RealRooted.RootCounting.Threshold.Basic
import RealRooted.SortedRoots

/-!
# Thresholded counts through sorted root magnitudes

This layer translates thresholded root counts into the ascending sequence of
negative root magnitudes.
-/

namespace RealRooted.RootCounting

open Polynomial
open SortedRoots

/-- A thresholded root count is the number of sorted root magnitudes below it. -/
theorem card_rootsAbove_eq_filter (p : ℝ[X]) (s : ℝ) :
    Multiset.card (rootsAbove p s)
      = ((rootMags p).filter (fun x => x < s)).length := by
  classical
  have hcoe : ((rootMags p : List ℝ) : Multiset ℝ)
      = p.roots.map (fun r : ℝ => -r) := by
    rw [rootMags, Multiset.sort_eq]
  have h₁ : ((rootMags p).filter (fun x => x < s)).length
      = Multiset.card ((p.roots.map (fun r : ℝ => -r)).filter (fun x => x < s)) := by
    rw [← hcoe]
    rfl
  rw [h₁, Multiset.filter_map, Multiset.card_map, rootsAbove]
  congr 1
  refine Multiset.filter_congr (fun ξ _ => ?_)
  simp only [Function.comp_apply]
  constructor <;> intro h <;> linarith

/-- A sorted root magnitude at least `s` bounds the thresholded count by its index. -/
theorem card_le_of_rootSeq_ge {p : ℝ[X]} {s : ℝ} {i : ℕ}
    (hi : i < (rootMags p).length) (hge : s ≤ rootSeq p i) :
    Multiset.card (rootsAbove p s) ≤ i := by
  classical
  have hsorted : (rootMags p).Pairwise (· ≤ ·) :=
    Multiset.pairwise_sort (p.roots.map (fun r : ℝ => -r)) (· ≤ ·)
  have hdrop : ((rootMags p).drop i).filter (fun x => x < s) = [] := by
    refine List.filter_eq_nil_iff.mpr ?_
    intro x hx
    simp only [decide_eq_true_eq, not_lt]
    rw [List.mem_drop_iff_getElem] at hx
    obtain ⟨k, hk, rfl⟩ := hx
    have hik : i + k < (rootMags p).length := by lia
    have hbase : rootSeq p i = (rootMags p)[i] := rootSeq_eq_getElem p hi
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · simpa [hbase] using hge
    · have hmono := List.pairwise_iff_getElem.mp hsorted i (i + k) hi hik (by lia)
      rw [← hbase] at hmono
      linarith
  have hsplit : (rootMags p).filter (fun x => x < s)
      = ((rootMags p).take i).filter (fun x => x < s) := by
    conv_lhs => rw [← List.take_append_drop i (rootMags p)]
    rw [List.filter_append, hdrop, List.append_nil]
  rw [card_rootsAbove_eq_filter, hsplit]
  calc
    (((rootMags p).take i).filter (fun x => x < s)).length
        ≤ ((rootMags p).take i).length := List.length_filter_le _ _
    _ ≤ i := by
      rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hi)]

/-- If a threshold contains more roots than an index, that root magnitude is below it. -/
theorem rootSeq_lt_of_lt_card {p : ℝ[X]} {s : ℝ} {i : ℕ}
    (h : i < Multiset.card (rootsAbove p s)) : rootSeq p i < s := by
  classical
  by_contra hcon
  push Not at hcon
  have hi : i < (rootMags p).length := by
    rw [card_rootsAbove_eq_filter] at h
    have hlength := List.length_filter_le (fun x => x < s) (rootMags p)
    lia
  have hle := card_le_of_rootSeq_ge hi hcon
  lia

/-- A sorted root magnitude below a threshold gives a strict lower bound on its count. -/
theorem card_ge_of_rootSeq_lt {p : ℝ[X]} {s : ℝ} {i : ℕ}
    (hi : i < (rootMags p).length) (h : rootSeq p i < s) :
    i + 1 ≤ Multiset.card (rootsAbove p s) := by
  classical
  have hsorted : (rootMags p).Pairwise (· ≤ ·) :=
    Multiset.pairwise_sort (p.roots.map (fun r : ℝ => -r)) (· ≤ ·)
  have hbase : rootSeq p i = (rootMags p)[i] := rootSeq_eq_getElem p hi
  have htake : ((rootMags p).take (i + 1)).filter (fun x => x < s)
      = (rootMags p).take (i + 1) := by
    refine List.filter_eq_self.mpr ?_
    intro x hx
    simp only [decide_eq_true_eq]
    rw [List.mem_take_iff_getElem] at hx
    obtain ⟨k, hk, rfl⟩ := hx
    have hlen : i + 1 ≤ (rootMags p).length := by lia
    have hki : k ≤ i := by
      have hlt : k < i + 1 := by
        simpa [Nat.min_eq_left hlen] using hk
      lia
    rcases eq_or_lt_of_le hki with rfl | hlt
    · rw [← hbase]
      exact h
    · have hkl : k < (rootMags p).length := by lia
      have hmono := List.pairwise_iff_getElem.mp hsorted k i hkl hi hlt
      rw [← hbase] at hmono
      linarith
  have hsplit : (rootMags p).filter (fun x => x < s)
      = ((rootMags p).take (i + 1)).filter (fun x => x < s)
        ++ ((rootMags p).drop (i + 1)).filter (fun x => x < s) := by
    conv_lhs => rw [← List.take_append_drop (i + 1) (rootMags p)]
    rw [List.filter_append]
  rw [card_rootsAbove_eq_filter, hsplit, htake, List.length_append,
    List.length_take, Nat.min_eq_left (by lia)]
  lia

/-- Equal thresholded counts at two endpoints give the intervening magnitude gap. -/
theorem gap_ge_of_rootfree {p : ℝ[X]} {s₁ s₂ : ℝ} {j : ℕ} (hj : 1 ≤ j)
    (hjlen : j < (rootMags p).length) (hc₁ : Multiset.card (rootsAbove p s₁) = j)
    (hc₂ : Multiset.card (rootsAbove p s₂) = j) :
    rootSeq p (j - 1) < s₁ ∧ s₂ ≤ rootSeq p j := by
  constructor
  · refine rootSeq_lt_of_lt_card ?_
    rw [hc₁]
    lia
  · by_contra hcon
    push Not at hcon
    have hge := card_ge_of_rootSeq_lt hjlen hcon
    rw [hc₂] at hge
    lia

/-- A root-free interval with equal endpoint counts yields an outer magnitude gap. -/
theorem outer_gap_of_count {p : ℝ[X]} {s₁ s₂ : ℝ} {j : ℕ} (hj : 1 ≤ j)
    (hjlen : j < (rootMags p).length) (hneg : ∀ ξ ∈ p.roots, ξ < 0)
    (hc₁ : Multiset.card (rootsAbove p s₁) = j)
    (hc₂ : Multiset.card (rootsAbove p s₂) = j) :
    s₂ / s₁ ≤ rootSeq p j / rootSeq p (j - 1) := by
  obtain ⟨hlow, hhigh⟩ := gap_ge_of_rootfree hj hjlen hc₁ hc₂
  have hpos : 0 < rootSeq p (j - 1) := rootSeq_pos p hneg (by lia)
  have hs₁ : 0 < s₁ := lt_trans hpos hlow
  have hstep : s₂ / s₁ ≤ rootSeq p j / s₁ := by gcongr
  refine le_trans hstep ?_
  have hnonneg : 0 ≤ rootSeq p j := le_of_lt (rootSeq_pos p hneg hjlen)
  exact div_le_div_of_nonneg_left hnonneg hpos (le_of_lt hlow)

/-- The thresholded count at a sorted root magnitude is its index. -/
theorem card_at_rootSeq {p : ℝ[X]}
    (hlt : ∀ i j, i < j → j < (rootMags p).length → rootSeq p i < rootSeq p j)
    {k : ℕ} (hk : k < (rootMags p).length) :
    Multiset.card (rootsAbove p (rootSeq p k)) = k := by
  have hle : Multiset.card (rootsAbove p (rootSeq p k)) ≤ k :=
    card_le_of_rootSeq_ge hk (le_refl _)
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  · lia
  · have hprev : rootSeq p (k - 1) < rootSeq p k := hlt (k - 1) k (by lia) hk
    have hge := card_ge_of_rootSeq_lt (i := k - 1) (by lia) hprev
    lia

end RealRooted.RootCounting
