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

private theorem networkShift_normalized
    (weights : ℕ → ℕ → ℝ)
    (hnormalized : ∀ n k, k ≤ n → weights n k = 0 → weights (n + 1) k = 0) :
    ∀ n k, k ≤ n → networkShift weights n k = 0 → networkShift weights (n + 1) k = 0 := by
  intro n k hkn hzero
  exact hnormalized (n + 1) (k + 1) (Nat.succ_le_succ hkn) hzero

private theorem networkShift_iterate_normalized
    (weights : ℕ → ℕ → ℝ)
    (hnormalized : ∀ n k, k ≤ n → weights n k = 0 → weights (n + 1) k = 0) :
    ∀ r n k, k ≤ n → (networkShift^[r]) weights n k = 0 →
      (networkShift^[r]) weights (n + 1) k = 0 := by
  intro r
  induction r with
  | zero => simpa
  | succ r ih =>
      rw [Function.iterate_succ_apply']
      exact networkShift_normalized ((networkShift^[r]) weights) ih

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

/-- One Whitney reduction of a normalized literal-network path matrix is the
path matrix of the shifted network. -/
theorem whitneyReduce_networkMatrix_eq_networkShift
    (weights : ℕ → ℕ → ℝ)
    (hnormalized : ∀ n k, k ≤ n → weights n k = 0 → weights (n + 1) k = 0) :
    whitneyReduce (networkMatrix weights) = networkMatrix (networkShift weights) := by
  ext n k
  unfold whitneyReduce
  rw [firstColumnRatio_networkMatrix weights hnormalized]
  change networkPathSum weights (n + 1) (k + 1) -
      weights n 0 * networkPathSum weights n (k + 1) =
    networkPathSum (networkShift weights) n k
  by_cases hkn : k ≤ n
  · have hstep := networkPathSumFrom_step weights (n := n) (k := 0)
      (Nat.zero_le n) (k + 1)
    rw [networkPathSumFrom_zero_eq_all] at hstep
    rw [networkPathSumFrom_zero_eq_all] at hstep
    rw [networkPathSumFrom_one_eq_networkShift] at hstep
    exact sub_eq_iff_eq_add.mpr (by simpa [add_comm] using hstep)
  · rw [networkPathSum_eq_zero_of_lt weights (by lia)]
    rw [networkPathSum_eq_zero_of_lt weights (by lia)]
    rw [networkPathSum_eq_zero_of_lt (networkShift weights) (by lia)]
    simp

/-- Iterated Whitney reduction of a normalized literal-network path matrix is
the path matrix of the equally iterated shifted network. -/
theorem whitneyIterate_networkMatrix_eq_networkShift_iterate
    (weights : ℕ → ℕ → ℝ)
    (hnormalized : ∀ n k, k ≤ n → weights n k = 0 → weights (n + 1) k = 0) :
    ∀ r, whitneyIterate (networkMatrix weights) r =
      networkMatrix ((networkShift^[r]) weights) := by
  intro r
  induction r with
  | zero => rfl
  | succ r ih =>
      rw [whitneyIterate_succ, ih]
      rw [whitneyReduce_networkMatrix_eq_networkShift]
      · rw [Function.iterate_succ_apply']
      · exact networkShift_iterate_normalized weights hnormalized r

/-- The canonical Whitney coefficient of a normalized literal-network matrix
recovers its original triangular-network weight. -/
theorem resolutionLambda_networkMatrix_eq_weight
    (weights : ℕ → ℕ → ℝ)
    (hnormalized : ∀ n k, k ≤ n → weights n k = 0 → weights (n + 1) k = 0)
    (n k : ℕ) (hkn : k ≤ n) :
    resolutionLambda (networkMatrix weights) n k = weights n k := by
  unfold resolutionLambda
  rw [whitneyIterate_networkMatrix_eq_networkShift_iterate weights hnormalized]
  rw [firstColumnRatio_networkMatrix]
  · rw [networkShift_iterate_apply]
    simp only [Nat.zero_add]
    rw [Nat.sub_add_cancel hkn]
  · exact networkShift_iterate_normalized weights hnormalized k

/-- Normalized literal triangular-network weights are uniquely determined on
their triangular domain by their path matrix. -/
theorem normalized_network_weights_unique
    (weights other : ℕ → ℕ → ℝ)
    (hweights : ∀ n k, k ≤ n → weights n k = 0 → weights (n + 1) k = 0)
    (hother : ∀ n k, k ≤ n → other n k = 0 → other (n + 1) k = 0)
    (hmatrix : networkMatrix weights = networkMatrix other) :
    ∀ n k, k ≤ n → weights n k = other n k := by
  intro n k hkn
  calc
    weights n k = resolutionLambda (networkMatrix weights) n k :=
      (resolutionLambda_networkMatrix_eq_weight weights hweights n k hkn).symm
    _ = resolutionLambda (networkMatrix other) n k := by rw [hmatrix]
    _ = other n k := resolutionLambda_networkMatrix_eq_weight other hother n k hkn

/-- Every lower-unitriangular totally nonnegative matrix is the literal
triangular-network path matrix of its canonical Whitney weights. -/
theorem networkMatrix_resolutionLambda_eq
    (R : LowerTriangularMatrix ℝ)
    (hunit : LowerTriangularMatrix.IsLowerUnitriangular R)
    (hR : Matrix.IsTotallyNonneg R) :
    networkMatrix (resolutionLambda R) = R := by
  simpa [resolutionOfTotallyNonneg] using
    networkMatrix_eq_of_resolution (resolutionOfTotallyNonneg R hunit hR)

end RealRooted.BrandenLeite
