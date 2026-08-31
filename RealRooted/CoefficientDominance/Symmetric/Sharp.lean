import RealRooted.CoefficientDominance.Symmetric.Finite

/-!
# Sharpened elementary-symmetric bounds

The generating-function upper bound can retain the leading-product lower bounds
for all terms other than the distinguished elementary symmetric value.
-/

namespace RealRooted.CoefficientDominance.Symmetric

open Finset

/-- In the generating expansion, all nondistinguished terms can be retained to
their leading-product lower bound. -/
theorem esym_mul_pow_le_sharp (x : ℕ → ℝ) (hnn : ∀ i, 0 ≤ x i) {n j : ℕ}
    (hj : j ≤ n) {t : ℝ} (ht : 0 ≤ t) :
    esym x n j * t ^ j ≤ (∏ i ∈ range n, (1 + x i * t))
      - ∑ k ∈ (range (n + 1)).erase j, topProd x k * t ^ k := by
  have hjmem : j ∈ range (n + 1) := mem_range.mpr (by lia)
  have hsplit : ∑ k ∈ range (n + 1), esym x n k * t ^ k
      = esym x n j * t ^ j + ∑ k ∈ (range (n + 1)).erase j, esym x n k * t ^ k :=
    (Finset.add_sum_erase _ _ hjmem).symm
  have hlow : ∑ k ∈ (range (n + 1)).erase j, topProd x k * t ^ k
      ≤ ∑ k ∈ (range (n + 1)).erase j, esym x n k * t ^ k := by
    refine Finset.sum_le_sum (fun k hk => ?_)
    have hkn : k ≤ n := by
      have h := Finset.mem_of_mem_erase hk
      rw [mem_range] at h
      lia
    exact mul_le_mul_of_nonneg_right (topProd_le_esym hnn hkn) (by positivity)
  rw [prod_one_add_eq_sum, hsplit]
  linarith

/-- The sharpened generating-function bound after division by the positive
evaluation monomial. -/
theorem esym_le_sharp (x : ℕ → ℝ) (hnn : ∀ i, 0 ≤ x i) {n j : ℕ}
    (hj : j ≤ n) {t : ℝ} (ht : 0 < t) :
    esym x n j ≤ ((∏ i ∈ range n, (1 + x i * t))
      - ∑ k ∈ (range (n + 1)).erase j, topProd x k * t ^ k) / t ^ j := by
  rw [le_div_iff₀ (by positivity)]
  exact esym_mul_pow_le_sharp x hnn hj ht.le

end RealRooted.CoefficientDominance.Symmetric
