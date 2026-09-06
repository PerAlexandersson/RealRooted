import RealRooted.BrandenLeite.Resolvable
import RealRooted.Mathlib.Algebra.Polynomial.BasisTransform
import RealRooted.RowThresholdOne
import RealRooted.SymmetricDecomposition.FPolynomialInterlacing

/-!
# Chain polynomials of a resolvable matrix

Definitions and the conditional Brändén--Saud Leite induction.  The public
theorems in this file assume explicit `Resolution` data; constructing that data
from total nonnegativity remains the separate Whitney-reduction problem #398.
-/

open Polynomial BigOperators

noncomputable section

namespace RealRooted.BrandenLeite

/-- Brändén--Saud Leite chain polynomials, Definition 3.2. -/
def chainPolynomial (R : LowerTriangularMatrix ℝ) : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 =>
      X * ∑ k : Fin (n + 1), C (R (n + 1) k) * chainPolynomial R k
termination_by n => n
decreasing_by exact k.isLt

@[simp] theorem chainPolynomial_zero (R : LowerTriangularMatrix ℝ) :
    chainPolynomial R 0 = 1 := by
  rw [chainPolynomial]

@[simp] theorem chainPolynomial_succ (R : LowerTriangularMatrix ℝ) (n : ℕ) :
    chainPolynomial R (n + 1) =
      X * ∑ k : Fin (n + 1), C (R (n + 1) k) * chainPolynomial R k := by
  rw [chainPolynomial]

/-- The subdivision operator sending `X ^ n` to the `n`th chain polynomial. -/
def subdivisionOperator (R : LowerTriangularMatrix ℝ) : ℝ[X] →ₗ[ℝ] ℝ[X] where
  toFun := basisTransform (chainPolynomial R)
  map_add' := basisTransform_add (chainPolynomial R)
  map_smul' := by
    intro a p
    simpa [Polynomial.smul_eq_C_mul] using
      basisTransform_smul (chainPolynomial R) a p

@[simp] theorem subdivisionOperator_apply (R : LowerTriangularMatrix ℝ) (p : ℝ[X]) :
    subdivisionOperator R p = basisTransform (chainPolynomial R) p :=
  rfl

@[simp] theorem subdivisionOperator_X_pow (R : LowerTriangularMatrix ℝ) (n : ℕ) :
    subdivisionOperator R (X ^ n) = chainPolynomial R n := by
  simp [subdivisionOperator]

@[simp] theorem subdivisionOperator_C_mul_X_pow
    (R : LowerTriangularMatrix ℝ) (a : ℝ) (n : ℕ) :
    subdivisionOperator R (C a * X ^ n) = C a * chainPolynomial R n := by
  simp [subdivisionOperator, basisTransform_C_mul_X_pow]

theorem subdivisionOperator_C_mul
    (R : LowerTriangularMatrix ℝ) (a : ℝ) (p : ℝ[X]) :
    subdivisionOperator R (C a * p) = C a * subdivisionOperator R p := by
  simpa [Polynomial.smul_eq_C_mul] using
    (subdivisionOperator R).map_smul a p

private theorem rowPolynomial_sub_top
    {R : LowerTriangularMatrix ℝ}
    (hR : LowerTriangularMatrix.IsLowerUnitriangular R) (n : ℕ) :
    LowerTriangularMatrix.rowPolynomial R (n + 1) - X ^ (n + 1) =
      ∑ k : Fin (n + 1), C (R (n + 1) k) * X ^ (k : ℕ) := by
  unfold LowerTriangularMatrix.rowPolynomial
  rw [Finset.sum_range_succ, hR.diagonal]
  simp only [map_one, one_mul, add_sub_cancel_right]
  exact (Fin.sum_univ_eq_sum_range
    (fun k : ℕ => C (R (n + 1) k) * X ^ k) (n + 1)).symm

/-- Alternative recursion (3.2) for the subdivision operator. -/
theorem subdivisionOperator_X_pow_succ_eq
    {R : LowerTriangularMatrix ℝ}
    (hR : LowerTriangularMatrix.IsLowerUnitriangular R) (n : ℕ) :
    subdivisionOperator R (X ^ (n + 1)) =
      X * subdivisionOperator R
        (LowerTriangularMatrix.rowPolynomial R (n + 1) - X ^ (n + 1)) := by
  rw [subdivisionOperator_X_pow, chainPolynomial_succ,
    rowPolynomial_sub_top hR]
  rw [map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  exact (subdivisionOperator_C_mul_X_pow R (R (n + 1) k) k).symm

/-- The subdivision recursion written in terms of one resolving row. -/
theorem chainPolynomial_succ_eq_resolution_sum
    {R : LowerTriangularMatrix ℝ} (resolution : Resolution R) (n : ℕ) :
    chainPolynomial R (n + 1) =
      X * ∑ j ∈ Finset.range (n + 1),
        C (resolution.lambda n j) *
          subdivisionOperator R (resolution.polynomial n j) := by
  have hrow :
      LowerTriangularMatrix.rowPolynomial R (n + 1) - X ^ (n + 1) =
        ∑ j ∈ Finset.range (n + 1),
          C (resolution.lambda n j) * resolution.polynomial n j := by
    rw [resolution.rowPolynomial_eq_pow_add_sum]
    ring
  calc
    chainPolynomial R (n + 1) = subdivisionOperator R (X ^ (n + 1)) := by simp
    _ = X * subdivisionOperator R
          (LowerTriangularMatrix.rowPolynomial R (n + 1) - X ^ (n + 1)) :=
      subdivisionOperator_X_pow_succ_eq resolution.lowerUnitriangular n
    _ = X * subdivisionOperator R
          (∑ j ∈ Finset.range (n + 1),
            C (resolution.lambda n j) * resolution.polynomial n j) := by rw [hrow]
    _ = X * ∑ j ∈ Finset.range (n + 1),
          C (resolution.lambda n j) *
            subdivisionOperator R (resolution.polynomial n j) := by
      rw [map_sum]
      apply congrArg (X * ·)
      apply Finset.sum_congr rfl
      intro j hj
      exact subdivisionOperator_C_mul R _ _

/-- The exact generated-family bridge used in the induction for Theorem 3.6. -/
theorem subdivisionOperator_resolution_recurrence
    {R : LowerTriangularMatrix ℝ} (resolution : Resolution R)
    {n k : ℕ} (hk : k ≤ n + 1) :
    subdivisionOperator R (resolution.polynomial (n + 1) k) =
      X * ∑ j ∈ Finset.range k,
          C (resolution.lambda n j) *
            subdivisionOperator R (resolution.polynomial n j) +
        (1 + X) * ∑ j ∈ Finset.Ico k (n + 1),
          C (resolution.lambda n j) *
            subdivisionOperator R (resolution.polynomial n j) := by
  let term : ℕ → ℝ[X] := fun j =>
    C (resolution.lambda n j) * subdivisionOperator R (resolution.polynomial n j)
  have hmap :
      subdivisionOperator R (resolution.polynomial (n + 1) k) =
        chainPolynomial R (n + 1) + ∑ j ∈ Finset.Ico k (n + 1), term j := by
    rw [resolution.polynomial_eq_pow_add_sum hk, map_add, subdivisionOperator_X_pow,
      map_sum]
    apply congrArg (chainPolynomial R (n + 1) + ·)
    apply Finset.sum_congr rfl
    intro j hj
    exact subdivisionOperator_C_mul R _ _
  rw [hmap, chainPolynomial_succ_eq_resolution_sum resolution]
  have hsplit :
      (∑ j ∈ Finset.range (n + 1), term j) =
        (∑ j ∈ Finset.range k, term j) +
          ∑ j ∈ Finset.Ico k (n + 1), term j :=
    (Finset.sum_range_add_sum_Ico term hk).symm
  rw [hsplit]
  dsimp only [term]
  ring

end RealRooted.BrandenLeite
