import RealRooted.BrandenLeite.Resolvable
import RealRooted.BrandenVecchi.Chow
import RealRooted.Mathlib.Algebra.Polynomial.BasisTransform

/-!
# Chow transforms of resolving rows

This file supplies the algebraic part of Bränden--Vecchi, Lemma 4.15. It
applies the Chow-deranged basis transform to an explicit matrix resolution and
identifies the resulting staircase recurrence. Interlacing and total
nonnegativity enter only in later modules.
-/

open Polynomial BigOperators

namespace RealRooted.BrandenVecchi

noncomputable section

variable {R : Type*} [CommRing R]

/-- The linear basis transform sending `X ^ n` to the Chow-derangement
polynomial in row `n`. -/
def chowDerangedTransform (A : LowerTriangularMatrix R) : R[X] →ₗ[R] R[X] where
  toFun := basisTransform (chowDerangement A)
  map_add' := basisTransform_add (chowDerangement A)
  map_smul' a p := by
    simpa [Polynomial.smul_eq_C_mul] using
      basisTransform_smul (chowDerangement A) a p

@[simp]
theorem chowDerangedTransform_X_pow (A : LowerTriangularMatrix R) (n : ℕ) :
    chowDerangedTransform A (X ^ n) = chowDerangement A n := by
  simp [chowDerangedTransform]

@[simp]
theorem chowDerangedTransform_C_mul (A : LowerTriangularMatrix R)
    (a : R) (p : R[X]) :
    chowDerangedTransform A (C a * p) = C a * chowDerangedTransform A p := by
  rw [← Polynomial.smul_eq_C_mul, LinearMap.map_smul,
    Polynomial.smul_eq_C_mul]

/-- Applying the Chow-deranged transform to a matrix row gives its Chow
polynomial. -/
@[simp]
theorem chowDerangedTransform_rowPolynomial
    (A : LowerTriangularMatrix R) (n : ℕ) :
    chowDerangedTransform A (LowerTriangularMatrix.rowPolynomial A n) =
      chowPolynomial A n := by
  simp [LowerTriangularMatrix.rowPolynomial, chowPolynomial]

section Resolution

variable [LE R]

/-- The Chow-deranged image of one polynomial in an explicit resolving row. -/
def resolvedChowDerangement {A : LowerTriangularMatrix R}
    (resolution : BrandenLeite.Resolution A) (n k : ℕ) : R[X] :=
  chowDerangedTransform A (resolution.polynomial n k)

/-- The bottom member of a transformed resolving row is the Chow polynomial. -/
@[simp]
theorem resolvedChowDerangement_zero {A : LowerTriangularMatrix R}
    (resolution : BrandenLeite.Resolution A) (n : ℕ) :
    resolvedChowDerangement resolution n 0 = chowPolynomial A n := by
  rw [resolvedChowDerangement, resolution.row_zero,
    chowDerangedTransform_rowPolynomial]

/-- The diagonal member of a transformed resolving row is the
Chow-derangement polynomial. -/
@[simp]
theorem resolvedChowDerangement_diagonal {A : LowerTriangularMatrix R}
    (resolution : BrandenLeite.Resolution A) (n : ℕ) :
    resolvedChowDerangement resolution n n = chowDerangement A n := by
  rw [resolvedChowDerangement, resolution.diagonal,
    chowDerangedTransform_X_pow]

/-- The weighted predecessor row appearing in the transformed resolution
recurrence. -/
def resolvedChowWeightSum {A : LowerTriangularMatrix R}
    (resolution : BrandenLeite.Resolution A) (n : ℕ) : R[X] :=
  ∑ j ∈ Finset.range (n + 1),
    C (resolution.lambda n j) * resolvedChowDerangement resolution n j

private theorem chowInput_eq_resolvedChowWeightSum
    {A : LowerTriangularMatrix R}
    (resolution : BrandenLeite.Resolution A) (n : ℕ) :
    (∑ k : Fin (n + 1),
        C (A (n + 1) k) * chowDerangement A k) =
      resolvedChowWeightSum resolution n := by
  have hrow := resolution.rowPolynomial_eq_pow_add_sum n
  have hmap := congrArg (chowDerangedTransform A) hrow
  simp only [LinearMap.map_add, map_sum,
    chowDerangedTransform_rowPolynomial, chowDerangedTransform_X_pow,
    chowDerangedTransform_C_mul] at hmap
  change chowPolynomial A (n + 1) =
    chowDerangement A (n + 1) + resolvedChowWeightSum resolution n at hmap
  have hsplit :
      chowPolynomial A (n + 1) =
        (∑ k : Fin (n + 1),
          C (A (n + 1) k) * chowDerangement A k) +
            chowDerangement A (n + 1) := by
    rw [chowPolynomial_eq]
    exact LowerTriangularMatrix.sum_C_mul_range_succ_eq_fin_sum_add A
      (resolution.lowerUnitriangular.diagonal (n + 1)) (chowDerangement A)
  rw [hsplit] at hmap
  linear_combination hmap

/-- The Chow-derangement successor is the `chowS` image of the weighted
transformed resolving row. -/
theorem chowDerangement_succ_eq_resolvedChowWeightSum
    {A : LowerTriangularMatrix R}
    (resolution : BrandenLeite.Resolution A) (n : ℕ) :
    chowDerangement A (n + 1) =
      X * chowS n (resolvedChowWeightSum resolution n) := by
  rw [chowDerangement_succ,
    chowInput_eq_resolvedChowWeightSum resolution n]

/-- Applying the Chow-deranged transform to the resolution recurrence gives
the staircase recurrence of Bränden--Vecchi, Lemma 4.15. -/
theorem resolvedChowDerangement_succ
    {A : LowerTriangularMatrix R}
    (resolution : BrandenLeite.Resolution A)
    {n k : ℕ} (hk : k ≤ n + 1) :
    resolvedChowDerangement resolution (n + 1) k =
      X * chowS n (resolvedChowWeightSum resolution n) +
        ∑ j ∈ Finset.Ico k (n + 1),
          C (resolution.lambda n j) *
            resolvedChowDerangement resolution n j := by
  rw [resolvedChowDerangement,
    resolution.polynomial_eq_pow_add_sum hk, LinearMap.map_add,
    chowDerangedTransform_X_pow, map_sum]
  simp only [chowDerangedTransform_C_mul, resolvedChowDerangement]
  rw [chowDerangement_succ_eq_resolvedChowWeightSum resolution n]

end Resolution

end

end RealRooted.BrandenVecchi
