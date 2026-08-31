import RealRooted.CoefficientDominance.Symmetric.Finite
import Mathlib.Order.Interval.Finset.Nat

/-!
# Tail contributions to elementary symmetric functions
-/

namespace RealRooted.CoefficientDominance.Symmetric

open Finset

/-- The leading product times the remaining tail sum is one positive part of
the next elementary symmetric function. -/
theorem topProd_mul_tail_le {x : ℕ → ℝ} (hpos : ∀ i, 0 < x i) {n j : ℕ} :
    topProd x (j + 1) * (∑ l ∈ Ico (j + 1) n, x l) ≤ esym x n (j + 2) := by
  classical
  have hmem : ∀ l ∈ Ico (j + 1) n, insert l (range (j + 1)) ∈
      (range n).powersetCard (j + 2) := by
    intro l hl
    rw [Finset.mem_Ico] at hl
    have hlr : l ∉ range (j + 1) := by
      rw [mem_range]
      lia
    rw [mem_powersetCard]
    refine ⟨?_, ?_⟩
    · intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy'
      · exact mem_range.mpr hl.2
      · have h := mem_range.mp hy'
        exact mem_range.mpr (by lia)
    · rw [Finset.card_insert_of_notMem hlr, card_range]
  have hinj : ∀ a ∈ Ico (j + 1) n, ∀ b ∈ Ico (j + 1) n,
      insert a (range (j + 1)) = insert b (range (j + 1)) → a = b := by
    intro a ha b hb hEq
    rw [Finset.mem_Ico] at ha hb
    have hna : a ∉ range (j + 1) := by
      rw [mem_range]
      lia
    have hnb : b ∉ range (j + 1) := by
      rw [mem_range]
      lia
    have hA : a ∈ insert b (range (j + 1)) := by
      rw [← hEq]
      exact Finset.mem_insert_self a _
    rcases Finset.mem_insert.mp hA with h | h
    · exact h
    · exact absurd h hna
  have hterm : ∀ l ∈ Ico (j + 1) n,
      topProd x (j + 1) * x l = ∏ i ∈ insert l (range (j + 1)), x i := by
    intro l hl
    rw [Finset.mem_Ico] at hl
    have hlr : l ∉ range (j + 1) := by
      rw [mem_range]
      lia
    rw [Finset.prod_insert hlr, topProd]
    ring
  calc
    topProd x (j + 1) * (∑ l ∈ Ico (j + 1) n, x l)
        = ∑ l ∈ Ico (j + 1) n, topProd x (j + 1) * x l := by rw [Finset.mul_sum]
    _ = ∑ l ∈ Ico (j + 1) n, ∏ i ∈ insert l (range (j + 1)), x i :=
      Finset.sum_congr rfl hterm
    _ = ∑ S ∈ (Ico (j + 1) n).image (fun l => insert l (range (j + 1))),
          ∏ i ∈ S, x i := by rw [Finset.sum_image hinj]
    _ ≤ esym x n (j + 2) := by
      rw [esym_eq_sum]
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_
        (fun S _ _ => prod_nonneg (fun i _ => (hpos i).le))
      intro S hS
      rw [Finset.mem_image] at hS
      obtain ⟨l, hl, rfl⟩ := hS
      exact hmem l hl

end RealRooted.CoefficientDominance.Symmetric
