import RealRooted.BrandenLeite.Resolvable

/-!
# Brändén--Saud Leite triangular networks

This file gives the literal finite path model used in Theorem 2.1 of
Brändén--Saud Leite. A path from `(n, 0)` to `(k, k)` is encoded by the finite
set of its `k` horizontal step times. It defines the associated weighted path
matrix and proves its lower-unitriangular and entrywise-nonnegative boundaries.

The Lindström--Gessel--Viennot total-nonnegativity theorem, the identification
with an arbitrary totally nonnegative matrix, and normalized weight uniqueness
are intentionally later steps.
-/

open BigOperators Polynomial

namespace RealRooted.BrandenLeite

noncomputable section

/-- The finite collection of paths from `(n, 0)` to `(k, k)`, encoded by
their horizontal step times. -/
def networkPaths (n k : ℕ) : Finset (Finset (Fin n)) :=
  (Finset.univ : Finset (Fin n)).powerset.filter fun horizontalSteps =>
    horizontalSteps.card = k

/-- Number of horizontal steps strictly before a time. -/
def horizontalBefore {n : ℕ} (horizontalSteps : Finset (Fin n)) (t : Fin n) : ℕ :=
  (horizontalSteps.filter fun i => i < t).card

/-- Paths from `(n, k)` to `(j, j)`, encoded by horizontal step times. -/
def networkPathsFrom (n k j : ℕ) : Finset (Finset (Fin (n - k))) :=
  if k ≤ j ∧ j ≤ n then
    (Finset.univ : Finset (Fin (n - k))).powerset.filter fun horizontalSteps =>
      horizontalSteps.card = j - k
  else ∅

/-- Weight of the path encoded by a set of horizontal step times in the
triangular network. Horizontal edges have weight `1`; vertical edges have the
given array weight. -/
def networkPathWeight {R : Type*} [CommSemiring R] (weights : ℕ → ℕ → R)
    {n : ℕ} (horizontalSteps : Finset (Fin n)) : R :=
  ∏ t, if t ∈ horizontalSteps then 1 else
    weights (n - (t.val - horizontalBefore horizontalSteps t) - 1)
      (horizontalBefore horizontalSteps t)

/-- Weight of a path from `(n, k)` to a diagonal vertex. -/
def networkPathWeightFrom {R : Type*} [CommSemiring R] (weights : ℕ → ℕ → R)
    (n k : ℕ) {length : ℕ} (horizontalSteps : Finset (Fin length)) : R :=
  ∏ t, if t ∈ horizontalSteps then 1 else
    weights (n - (t.val - horizontalBefore horizontalSteps t) - 1)
      (k + horizontalBefore horizontalSteps t)

/-- Weighted path count from `(n, 0)` to `(k, k)`. -/
noncomputable def networkPathSum {R : Type*} [CommSemiring R]
    (weights : ℕ → ℕ → R) (n k : ℕ) : R := by
  classical
  exact ∑ horizontalSteps ∈ networkPaths n k, networkPathWeight weights horizontalSteps

/-- Weighted path count from `(n, k)` to `(j, j)`. -/
noncomputable def networkPathSumFrom {R : Type*} [CommSemiring R]
    (weights : ℕ → ℕ → R) (n k j : ℕ) : R :=
  ∑ horizontalSteps ∈ networkPathsFrom n k j,
    networkPathWeightFrom weights n k horizontalSteps

/-- The infinite matrix of weighted triangular-network path counts. -/
def networkMatrix {R : Type*} [CommSemiring R] (weights : ℕ → ℕ → R) :
    LowerTriangularMatrix R :=
  networkPathSum weights

/-- The resolving polynomial obtained from weighted paths starting at `(n, k)`.
The recurrence relating neighboring values is a later network step. -/
def networkResolvingPolynomial (weights : ℕ → ℕ → ℝ) (n k : ℕ) : ℝ[X] :=
  ∑ j ∈ Finset.range (n + 1), C (networkPathSumFrom weights n k j) * X ^ j

private theorem networkPath_card_le {n k : ℕ} {horizontalSteps : Finset (Fin n)}
    (hpath : horizontalSteps ∈ networkPaths n k) : k ≤ n := by
  classical
  rw [← (Finset.mem_filter.mp hpath).2]
  simpa using Finset.card_le_univ horizontalSteps

private theorem networkPaths_self (n : ℕ) :
    networkPaths n n = {Finset.univ} := by
  ext horizontalSteps
  simp only [networkPaths, Finset.mem_filter, Finset.mem_powerset,
    Finset.mem_singleton]
  constructor
  · intro h
    apply (Finset.card_eq_iff_eq_univ _).mp
    simpa using h.2
  · rintro rfl
    simp

private theorem networkPathsFrom_self (n : ℕ) :
    networkPathsFrom n n n = {Finset.univ} := by
  ext horizontalSteps
  simp only [networkPathsFrom, le_refl, and_self, if_true, Finset.mem_filter,
    Finset.mem_powerset, Finset.mem_singleton]
  constructor
  · intro h
    apply (Finset.card_eq_iff_eq_univ _).mp
    simpa using h.2
  · rintro rfl
    simp

/-- No path from `(n, 0)` can reach `(k, k)` when `k > n`. -/
theorem networkPathSum_eq_zero_of_lt {R : Type*} [CommSemiring R]
    (weights : ℕ → ℕ → R) {n k : ℕ} (h : n < k) :
    networkPathSum weights n k = 0 := by
  classical
  unfold networkPathSum
  apply Finset.sum_eq_zero
  intro horizontalSteps hpath
  exact (not_le_of_gt h (networkPath_card_le hpath)).elim

/-- A path count is zero when its target diagonal vertex lies left of its
starting column. -/
theorem networkPathSumFrom_eq_zero_of_lt_left {R : Type*} [CommSemiring R]
    (weights : ℕ → ℕ → R) {n k j : ℕ} (hjk : j < k) :
    networkPathSumFrom weights n k j = 0 := by
  unfold networkPathSumFrom networkPathsFrom
  rw [if_neg]
  · simp
  · exact fun h => (not_le_of_gt hjk h.1).elim

/-- Starting in column zero recovers the path counts defining `networkMatrix`. -/
theorem networkPathSumFrom_zero_eq {R : Type*} [CommSemiring R]
    (weights : ℕ → ℕ → R) {n j : ℕ} (hj : j ≤ n) :
    networkPathSumFrom weights n 0 j = networkPathSum weights n j := by
  classical
  unfold networkPathSumFrom networkPathsFrom networkPathSum networkPaths
    networkPathWeightFrom networkPathWeight
  simp only [Nat.zero_le, true_and, if_pos hj, Nat.sub_zero, zero_add]

/-- Every weighted triangular-network path matrix is lower triangular. -/
theorem isLowerTriangular_networkMatrix {R : Type*} [CommSemiring R]
    (weights : ℕ → ℕ → R) :
    LowerTriangularMatrix.IsLowerTriangular (networkMatrix weights) := by
  intro n k hnk
  exact networkPathSum_eq_zero_of_lt weights hnk

/-- The unique path from `(n, 0)` to `(n, n)` uses only horizontal edges. -/
theorem networkPathSum_self {R : Type*} [CommSemiring R]
    (weights : ℕ → ℕ → R) (n : ℕ) :
    networkPathSum weights n n = 1 := by
  classical
  unfold networkPathSum
  rw [networkPaths_self, Finset.sum_singleton]
  unfold networkPathWeight
  simp

/-- The only path from `(n, n)` to the diagonal is the empty path. -/
theorem networkPathSumFrom_self {R : Type*} [CommSemiring R]
    (weights : ℕ → ℕ → R) (n : ℕ) :
    networkPathSumFrom weights n n n = 1 := by
  unfold networkPathSumFrom
  rw [networkPathsFrom_self, Finset.sum_singleton]
  unfold networkPathWeightFrom
  simp

/-- Over the reals, every weighted triangular-network path matrix is lower
unitriangular. -/
theorem isLowerUnitriangular_networkMatrix (weights : ℕ → ℕ → ℝ) :
    LowerTriangularMatrix.IsLowerUnitriangular (networkMatrix weights) :=
  ⟨isLowerTriangular_networkMatrix weights, networkPathSum_self weights⟩

/-- The path polynomial in column zero is the row-generating polynomial of the
associated path matrix. -/
theorem networkResolvingPolynomial_zero (weights : ℕ → ℕ → ℝ) (n : ℕ) :
    networkResolvingPolynomial weights n 0 =
      LowerTriangularMatrix.rowPolynomial (networkMatrix weights) n := by
  unfold networkResolvingPolynomial LowerTriangularMatrix.rowPolynomial networkMatrix
  apply Finset.sum_congr rfl
  intro j hj
  rw [networkPathSumFrom_zero_eq weights (Nat.le_of_lt_succ (Finset.mem_range.mp hj))]

/-- The diagonal path polynomial is `X ^ n`. -/
theorem networkResolvingPolynomial_self (weights : ℕ → ℕ → ℝ) (n : ℕ) :
    networkResolvingPolynomial weights n n = X ^ n := by
  unfold networkResolvingPolynomial
  rw [Finset.sum_eq_single n]
  · rw [networkPathSumFrom_self]
    simp
  · intro j hj hjn
    have hjle : j ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    rw [networkPathSumFrom_eq_zero_of_lt_left weights (lt_of_le_of_ne hjle hjn)]
    simp
  · simp

/-- Every path polynomial from `(n, k)` is divisible by `X ^ k`. -/
theorem X_pow_dvd_networkResolvingPolynomial (weights : ℕ → ℕ → ℝ)
    (n k : ℕ) :
    X ^ k ∣ networkResolvingPolynomial weights n k := by
  unfold networkResolvingPolynomial
  apply Finset.dvd_sum
  intro j hj
  by_cases hkj : k ≤ j
  · exact (pow_dvd_pow X hkj).mul_left _
  · rw [networkPathSumFrom_eq_zero_of_lt_left weights (Nat.lt_of_not_ge hkj)]
    simp

/-- Nonnegative edge weights give nonnegative weighted path counts. -/
theorem networkPathSum_nonneg {R : Type*} [CommSemiring R] [PartialOrder R]
    [IsOrderedRing R]
    (weights : ℕ → ℕ → R) (hweights : ∀ n k, 0 ≤ weights n k) (n k : ℕ) :
    0 ≤ networkPathSum weights n k := by
  classical
  unfold networkPathSum
  apply Finset.sum_nonneg
  intro horizontalSteps _
  unfold networkPathWeight
  apply Finset.prod_nonneg
  intro t _
  split_ifs
  · exact zero_le_one
  · exact hweights _ _

end

end RealRooted.BrandenLeite
