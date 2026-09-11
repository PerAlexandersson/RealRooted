import RealRooted.BrandenLeite.Network
import RealRooted.BrandenLeite.WhitneyReduction

/-!
# First Whitney coefficient of a normalized triangular network

This opt-in bridge identifies the first Whitney reduction coefficient of a
literal normalized triangular network with its first vertical edge weight.
It is the first step toward the normalized-network uniqueness part of
Brändén--Saud Leite Theorem 2.1.
-/

namespace RealRooted.BrandenLeite

/-- In a normalized literal network, the first Whitney coefficient of the
path matrix is its first vertical edge weight. -/
theorem firstColumnRatio_networkMatrix
    (weights : ℕ → ℕ → ℝ)
    (hnormalized : ∀ n k, k ≤ n → weights n k = 0 → weights (n + 1) k = 0)
    (n : ℕ) :
    firstColumnRatio (networkMatrix weights) n = weights n 0 := by
  unfold firstColumnRatio networkMatrix
  rw [networkPathSum_succ_zero]
  by_cases hzero : networkPathSum weights n 0 = 0
  · have hweight : weights n 0 = 0 :=
      networkPathSum_zero_implies_weight_zero_of_normalized weights hnormalized n hzero
    rw [hweight, hzero]
    simp
  · exact mul_div_cancel_right₀ _ hzero

end RealRooted.BrandenLeite
