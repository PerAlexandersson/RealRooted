import RealRooted.LowerTriangularMatrix
import RealRooted.Mathlib.Algebra.Polynomial.BasisTransform

/-!
# Algebra of chain polynomials

This low-level module contains the semiring and commutative-ring algebra behind
Brändén--Saud Leite chain polynomials.  Resolution and real-rootedness
consequences deliberately live in the parent module.
-/

open Polynomial BigOperators

noncomputable section

namespace RealRooted.BrandenLeite

/-- Brändén--Saud Leite chain polynomials, Definition 3.2. -/
def chainPolynomial {R : Type*} [Semiring R] (A : LowerTriangularMatrix R) : ℕ → R[X]
  | 0 => 1
  | n + 1 =>
      X * ∑ k : Fin (n + 1), C (A (n + 1) k) * chainPolynomial A k
termination_by n => n
decreasing_by exact k.isLt

@[simp] theorem chainPolynomial_zero {R : Type*} [Semiring R]
    (A : LowerTriangularMatrix R) :
    chainPolynomial A 0 = 1 := by
  rw [chainPolynomial]

@[simp] theorem chainPolynomial_succ {R : Type*} [Semiring R]
    (A : LowerTriangularMatrix R) (n : ℕ) :
    chainPolynomial A (n + 1) =
      X * ∑ k : Fin (n + 1), C (A (n + 1) k) * chainPolynomial A k := by
  rw [chainPolynomial]

/-- The subdivision operator sending `X ^ n` to the `n`th chain polynomial. -/
def subdivisionOperator {R : Type*} [Semiring R]
    (A : LowerTriangularMatrix R) : R[X] →ₗ[R] R[X] where
  toFun := basisTransform (chainPolynomial A)
  map_add' := basisTransform_add (chainPolynomial A)
  map_smul' := by
    intro a p
    simpa [Polynomial.smul_eq_C_mul] using
      basisTransform_smul (chainPolynomial A) a p

@[simp] theorem subdivisionOperator_apply {R : Type*} [Semiring R]
    (A : LowerTriangularMatrix R) (p : R[X]) :
    subdivisionOperator A p = basisTransform (chainPolynomial A) p :=
  rfl

@[simp] theorem subdivisionOperator_X_pow {R : Type*} [Semiring R]
    (A : LowerTriangularMatrix R) (n : ℕ) :
    subdivisionOperator A (X ^ n) = chainPolynomial A n := by
  simp [subdivisionOperator]

@[simp] theorem subdivisionOperator_C_mul_X_pow
    {R : Type*} [Semiring R] (A : LowerTriangularMatrix R) (a : R) (n : ℕ) :
    subdivisionOperator A (C a * X ^ n) = C a * chainPolynomial A n := by
  simp [subdivisionOperator, basisTransform_C_mul_X_pow]

theorem subdivisionOperator_C_mul
    {R : Type*} [Semiring R] (A : LowerTriangularMatrix R) (a : R) (p : R[X]) :
    subdivisionOperator A (C a * p) = C a * subdivisionOperator A p := by
  simpa [Polynomial.smul_eq_C_mul] using
    (subdivisionOperator A).map_smul a p

private theorem rowPolynomial_sub_top
    {R : Type*} [CommRing R] {A : LowerTriangularMatrix R}
    (hA : LowerTriangularMatrix.IsLowerUnitriangular A) (n : ℕ) :
    LowerTriangularMatrix.rowPolynomial A (n + 1) - X ^ (n + 1) =
      ∑ k : Fin (n + 1), C (A (n + 1) k) * X ^ (k : ℕ) := by
  unfold LowerTriangularMatrix.rowPolynomial
  rw [Finset.sum_range_succ, hA.diagonal]
  simp only [map_one, one_mul, add_sub_cancel_right]
  exact (Fin.sum_univ_eq_sum_range
    (fun k : ℕ => C (A (n + 1) k) * X ^ k) (n + 1)).symm

/-- Alternative recursion (3.2) for the subdivision operator. -/
theorem subdivisionOperator_X_pow_succ_eq
    {R : Type*} [CommRing R] {A : LowerTriangularMatrix R}
    (hA : LowerTriangularMatrix.IsLowerUnitriangular A) (n : ℕ) :
    subdivisionOperator A (X ^ (n + 1)) =
      X * subdivisionOperator A
        (LowerTriangularMatrix.rowPolynomial A (n + 1) - X ^ (n + 1)) := by
  rw [subdivisionOperator_X_pow, chainPolynomial_succ,
    rowPolynomial_sub_top hA]
  rw [map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  exact (subdivisionOperator_C_mul_X_pow A (A (n + 1) k) k).symm

end RealRooted.BrandenLeite
