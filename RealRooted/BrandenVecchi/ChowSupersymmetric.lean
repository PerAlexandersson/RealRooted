import RealRooted.BrandenVecchi.ChowTotallyNonneg
import RealRooted.BrandenVecchi.SupersymmetricCoefficients

/-!
# Chow polynomials of finite supersymmetric products

This file proves the finite-product form of the Brändén--Vecchi Toeplitz
Chow theorem. It does not make an infinite-alphabet or limiting claim.
-/

open Matrix Polynomial

namespace RealRooted.BrandenVecchi

noncomputable section

/-- The lower Toeplitz matrix of the finite supersymmetric coefficient
sequence. -/
def finiteSupersymmetricToeplitz (xs ys : List ℝ) :
    LowerTriangularMatrix ℝ :=
  toeplitz (finiteSupersymmetricCoeff xs ys)

/-- The Chow polynomial attached to a finite supersymmetric product. -/
def finiteSupersymmetricChow (xs ys : List ℝ) (n : ℕ) : ℝ[X] :=
  chowPolynomial (finiteSupersymmetricToeplitz xs ys) n

/-- The Chow-derangement polynomial attached to a finite supersymmetric
product. -/
def finiteSupersymmetricChowDerangement
    (xs ys : List ℝ) (n : ℕ) : ℝ[X] :=
  chowDerangement (finiteSupersymmetricToeplitz xs ys) n

/-- The finite supersymmetric Toeplitz matrix is lower unitriangular. -/
theorem finiteSupersymmetricToeplitz_isLowerUnitriangular
    (xs ys : List ℝ) :
    LowerTriangularMatrix.IsLowerUnitriangular
      (finiteSupersymmetricToeplitz xs ys) := by
  constructor
  · intro i j hij
    simp [finiteSupersymmetricToeplitz, toeplitz_apply,
      Nat.not_le_of_lt hij]
  · intro n
    simp [finiteSupersymmetricToeplitz, toeplitz_apply]

/-- Nonnegative finite parameters give a totally nonnegative Toeplitz
matrix. -/
theorem finiteSupersymmetricToeplitz_isTotallyNonneg
    {xs ys : List ℝ} (hxs : ∀ x ∈ xs, 0 ≤ x)
    (hys : ∀ y ∈ ys, 0 ≤ y) :
    Matrix.IsTotallyNonneg (finiteSupersymmetricToeplitz xs ys) :=
  finiteSupersymmetricCoeff_isPolyaFreqSeq hxs hys

/-- Finite supersymmetric Chow polynomials have nonnegative coefficients. -/
theorem finiteSupersymmetricChow_nonnegCoeffs
    {xs ys : List ℝ} (hxs : ∀ x ∈ xs, 0 ≤ x)
    (hys : ∀ y ∈ ys, 0 ≤ y) (n : ℕ) :
    HasNonnegCoeffs (finiteSupersymmetricChow xs ys n) := by
  exact chowPolynomial_nonnegCoeffs_of_isTotallyNonneg
    (finiteSupersymmetricToeplitz_isLowerUnitriangular xs ys)
    (finiteSupersymmetricToeplitz_isTotallyNonneg hxs hys) n

/-- Finite supersymmetric Chow polynomials are zero or split. -/
theorem finiteSupersymmetricChow_eq_zero_or_splits
    {xs ys : List ℝ} (hxs : ∀ x ∈ xs, 0 ≤ x)
    (hys : ∀ y ∈ ys, 0 ≤ y) (n : ℕ) :
    finiteSupersymmetricChow xs ys n = 0 ∨
      (finiteSupersymmetricChow xs ys n).Splits := by
  exact chowPolynomial_eq_zero_or_splits_of_isTotallyNonneg
    (finiteSupersymmetricToeplitz_isLowerUnitriangular xs ys)
    (finiteSupersymmetricToeplitz_isTotallyNonneg hxs hys) n

/-- Finite supersymmetric Chow-derangement polynomials have nonnegative
coefficients. -/
theorem finiteSupersymmetricChowDerangement_nonnegCoeffs
    {xs ys : List ℝ} (hxs : ∀ x ∈ xs, 0 ≤ x)
    (hys : ∀ y ∈ ys, 0 ≤ y) (n : ℕ) :
    HasNonnegCoeffs (finiteSupersymmetricChowDerangement xs ys n) := by
  exact chowDerangement_nonnegCoeffs_of_isTotallyNonneg
    (finiteSupersymmetricToeplitz_isLowerUnitriangular xs ys)
    (finiteSupersymmetricToeplitz_isTotallyNonneg hxs hys) n

/-- Finite supersymmetric Chow-derangement polynomials are zero or split. -/
theorem finiteSupersymmetricChowDerangement_eq_zero_or_splits
    {xs ys : List ℝ} (hxs : ∀ x ∈ xs, 0 ≤ x)
    (hys : ∀ y ∈ ys, 0 ≤ y) (n : ℕ) :
    finiteSupersymmetricChowDerangement xs ys n = 0 ∨
      (finiteSupersymmetricChowDerangement xs ys n).Splits := by
  exact chowDerangement_eq_zero_or_splits_of_isTotallyNonneg
    (finiteSupersymmetricToeplitz_isLowerUnitriangular xs ys)
    (finiteSupersymmetricToeplitz_isTotallyNonneg hxs hys) n

/-- In one finite supersymmetric row, the Chow polynomial precedes its
Chow-derangement endpoint, with zeros allowed. -/
theorem finiteSupersymmetricChow_prec0_derangement
    {xs ys : List ℝ} (hxs : ∀ x ∈ xs, 0 ≤ x)
    (hys : ∀ y ∈ ys, 0 ≤ y) (n : ℕ) :
    Prec0 (finiteSupersymmetricChow xs ys n)
      (finiteSupersymmetricChowDerangement xs ys n) := by
  exact chowPolynomial_prec0_chowDerangement_of_isTotallyNonneg
    (finiteSupersymmetricToeplitz_isLowerUnitriangular xs ys)
    (finiteSupersymmetricToeplitz_isTotallyNonneg hxs hys) n

/-- Consecutive finite supersymmetric Chow polynomials are in zero-aware
proper position. -/
theorem finiteSupersymmetricChow_prec0_succ
    {xs ys : List ℝ} (hxs : ∀ x ∈ xs, 0 ≤ x)
    (hys : ∀ y ∈ ys, 0 ≤ y) (n : ℕ) :
    Prec0 (finiteSupersymmetricChow xs ys n)
      (finiteSupersymmetricChow xs ys (n + 1)) := by
  exact chowPolynomial_prec0_succ_of_isTotallyNonneg
    (finiteSupersymmetricToeplitz_isLowerUnitriangular xs ys)
    (finiteSupersymmetricToeplitz_isTotallyNonneg hxs hys) n

/-- Consecutive finite supersymmetric Chow-derangement polynomials are in
zero-aware proper position. -/
theorem finiteSupersymmetricChowDerangement_prec0_succ
    {xs ys : List ℝ} (hxs : ∀ x ∈ xs, 0 ≤ x)
    (hys : ∀ y ∈ ys, 0 ≤ y) (n : ℕ) :
    Prec0 (finiteSupersymmetricChowDerangement xs ys n)
      (finiteSupersymmetricChowDerangement xs ys (n + 1)) := by
  exact chowDerangement_prec0_succ_of_isTotallyNonneg
    (finiteSupersymmetricToeplitz_isLowerUnitriangular xs ys)
    (finiteSupersymmetricToeplitz_isTotallyNonneg hxs hys) n

end

end RealRooted.BrandenVecchi
