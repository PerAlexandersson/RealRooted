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

open BigOperators

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

/-- Weight of the path encoded by a set of horizontal step times in the
triangular network. Horizontal edges have weight `1`; vertical edges have the
given array weight. -/
def networkPathWeight {R : Type*} [CommSemiring R] (weights : ℕ → ℕ → R)
    {n : ℕ} (horizontalSteps : Finset (Fin n)) : R :=
  ∏ t, if t ∈ horizontalSteps then 1 else
    weights (n - (t.val - horizontalBefore horizontalSteps t) - 1)
      (horizontalBefore horizontalSteps t)

/-- Weighted path count from `(n, 0)` to `(k, k)`. -/
noncomputable def networkPathSum {R : Type*} [CommSemiring R]
    (weights : ℕ → ℕ → R) (n k : ℕ) : R := by
  classical
  exact ∑ horizontalSteps ∈ networkPaths n k, networkPathWeight weights horizontalSteps

/-- The infinite matrix of weighted triangular-network path counts. -/
def networkMatrix {R : Type*} [CommSemiring R] (weights : ℕ → ℕ → R) :
    LowerTriangularMatrix R :=
  networkPathSum weights

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

/-- No path from `(n, 0)` can reach `(k, k)` when `k > n`. -/
theorem networkPathSum_eq_zero_of_lt {R : Type*} [CommSemiring R]
    (weights : ℕ → ℕ → R) {n k : ℕ} (h : n < k) :
    networkPathSum weights n k = 0 := by
  classical
  unfold networkPathSum
  apply Finset.sum_eq_zero
  intro horizontalSteps hpath
  exact (not_le_of_gt h (networkPath_card_le hpath)).elim

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

/-- Over the reals, every weighted triangular-network path matrix is lower
unitriangular. -/
theorem isLowerUnitriangular_networkMatrix (weights : ℕ → ℕ → ℝ) :
    LowerTriangularMatrix.IsLowerUnitriangular (networkMatrix weights) :=
  ⟨isLowerTriangular_networkMatrix weights, networkPathSum_self weights⟩

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
