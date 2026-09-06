import RealRooted.LowerTriangularMatrix

/-!
# Resolvable lower unitriangular matrices

This file formalizes Brändén--Saud Leite, Definition 2.2, for infinite
lower-triangular matrices.  The construction of this data from total
nonnegativity is deliberately separate: it is the Whitney-reduction theorem
tracked by issue #398.
-/

open Polynomial BigOperators

noncomputable section

namespace RealRooted

namespace LowerTriangularMatrix

/-- An infinite matrix is lower unitriangular when it is lower triangular and
has diagonal entries equal to one. -/
def IsLowerUnitriangular (R : LowerTriangularMatrix ℝ) : Prop :=
  IsLowerTriangular R ∧ ∀ n, R n n = 1

namespace IsLowerUnitriangular

theorem lower {R : LowerTriangularMatrix ℝ} (hR : IsLowerUnitriangular R) :
    IsLowerTriangular R :=
  hR.1

theorem diagonal {R : LowerTriangularMatrix ℝ} (hR : IsLowerUnitriangular R)
    (n : ℕ) : R n n = 1 :=
  hR.2 n

end IsLowerUnitriangular

end LowerTriangularMatrix

namespace BrandenLeite

/-- Data witnessing that a lower unitriangular matrix is resolvable in the
sense of Brändén--Saud Leite, Definition 2.2. -/
structure Resolution (R : LowerTriangularMatrix ℝ) where
  lowerUnitriangular : LowerTriangularMatrix.IsLowerUnitriangular R
  lambda : ℕ → ℕ → ℝ
  polynomial : ℕ → ℕ → ℝ[X]
  lambda_nonneg : ∀ n k, k ≤ n → 0 ≤ lambda n k
  monic : ∀ n k, k ≤ n → (polynomial n k).Monic
  row_zero : ∀ n, polynomial n 0 = LowerTriangularMatrix.rowPolynomial R n
  diagonal : ∀ n, polynomial n n = X ^ n
  dvd_X_pow : ∀ n k, k ≤ n → X ^ k ∣ polynomial n k
  recurrence : ∀ n k, k ≤ n →
    polynomial (n + 1) k =
      polynomial (n + 1) (k + 1) + C (lambda n k) * polynomial n k

/-- A matrix is resolvable when it admits resolution data. -/
def IsResolvable (R : LowerTriangularMatrix ℝ) : Prop :=
  Nonempty (Resolution R)

namespace Resolution

variable {R : LowerTriangularMatrix ℝ} (resolution : Resolution R)

/-- Telescoping Definition 2.2 gives equation (2.4). -/
theorem polynomial_eq_pow_add_sum {n k : ℕ} (hk : k ≤ n + 1) :
    resolution.polynomial (n + 1) k =
      X ^ (n + 1) +
        ∑ j ∈ Finset.Ico k (n + 1),
          C (resolution.lambda n j) * resolution.polynomial n j := by
  induction hk using Nat.decreasingInduction with
  | self => simp [resolution.diagonal]
  | of_succ k hk ih =>
      rw [resolution.recurrence n k (Nat.le_of_lt_succ hk), ih]
      calc
        X ^ (n + 1) +
              ∑ j ∈ Finset.Ico (k + 1) (n + 1),
                C (resolution.lambda n j) * resolution.polynomial n j +
            C (resolution.lambda n k) * resolution.polynomial n k =
            X ^ (n + 1) +
              (C (resolution.lambda n k) * resolution.polynomial n k +
                ∑ j ∈ Finset.Ico (k + 1) (n + 1),
                  C (resolution.lambda n j) * resolution.polynomial n j) := by ring
        _ = X ^ (n + 1) +
              ∑ j ∈ Finset.Ico k (n + 1),
                C (resolution.lambda n j) * resolution.polynomial n j := by
          rw [Finset.sum_eq_sum_Ico_succ_bot hk]

/-- The bottom member of a resolving row is its row-generating polynomial. -/
theorem rowPolynomial_eq_pow_add_sum (n : ℕ) :
    LowerTriangularMatrix.rowPolynomial R (n + 1) =
      X ^ (n + 1) +
        ∑ j ∈ Finset.range (n + 1),
          C (resolution.lambda n j) * resolution.polynomial n j := by
  rw [← resolution.row_zero (n + 1),
    resolution.polynomial_eq_pow_add_sum (k := 0) (by lia)]
  simp

end Resolution

end BrandenLeite

end RealRooted
