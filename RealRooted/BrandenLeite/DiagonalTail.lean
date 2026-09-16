import RealRooted.BrandenLeite.ConstantDiagonal
import RealRooted.BrandenLeite.SourceBorderKernel
import RealRooted.Mathlib.LinearAlgebra.Matrix.TotallyNonneg.DiagonalTail

/-!
# Finite chain polynomials through a positive diagonal tail

A finite totally nonnegative lower-triangular matrix with positive constant
diagonal can be extended by an isolated constant diagonal tail.  Chain
polynomials inside the original block are unchanged, so the Nat-indexed chain
theorems apply to those finite rows.
-/

open Matrix

namespace RealRooted.BrandenLeite

/-- The diagonal-tail extension of a finite lower-triangular matrix is lower
triangular. -/
theorem diagonalTail_isLowerTriangular
    {R : Type*} [Zero R] {N : ℕ} {δ : R}
    {A : Matrix (Fin N) (Fin N) R}
    (hA : ∀ i j, i < j → A i j = 0) :
    LowerTriangularMatrix.IsLowerTriangular (Matrix.diagonalTail δ A) := by
  intro i j hij
  exact Matrix.diagonalTail_apply_eq_zero_of_lt (δ := δ) hA i j hij

/-- Inside the finite block, adjoining a diagonal tail does not change chain
polynomials. -/
theorem chainPolynomial_diagonalTail_eq_toLowerTriangularMatrix
    {R : Type*} [Semiring R] {N n : ℕ} (δ : R)
    (A : Matrix (Fin N) (Fin N) R) (hn : n < N) :
    chainPolynomial (Matrix.diagonalTail δ A) n =
      chainPolynomial (Matrix.toLowerTriangularMatrix A) n := by
  apply chainPolynomial_congr_le
  intro i hi j hji
  have hiN : i < N := hi.trans_lt hn
  have hjN : j < N := (hji.trans hi).trans_lt hn
  rw [Matrix.diagonalTail_apply_of_lt δ A hiN hjN]
  rw [Matrix.toLowerTriangularMatrix_apply_of_lt A hiN hjN]

/-- A finite totally nonnegative lower-triangular matrix with positive
constant diagonal has PF chain polynomials throughout its finite block. -/
theorem chainPolynomial_toLowerTriangularMatrix_isPFPolynomial
    {N n : ℕ} {δ : ℝ} {A : Matrix (Fin N) (Fin N) ℝ}
    (hδ : 0 < δ) (hA : A.IsTotallyNonneg)
    (hlower : ∀ i j, i < j → A i j = 0)
    (hdiag : ∀ i, A i i = δ) (hn : n < N) :
    IsPFPolynomial (chainPolynomial (Matrix.toLowerTriangularMatrix A) n) := by
  rw [← chainPolynomial_diagonalTail_eq_toLowerTriangularMatrix δ A hn]
  exact chainPolynomial_isPFPolynomial_of_pos_constantDiagonal hδ
    (diagonalTail_isLowerTriangular hlower)
    (fun i => Matrix.diagonalTail_apply_diagonal δ A hdiag)
    (hA.diagonalTail hδ.le) n

/-- Consecutive finite chain polynomials are in zero-aware proper position. -/
theorem prec0_chainPolynomial_toLowerTriangularMatrix_succ
    {N n : ℕ} {δ : ℝ} {A : Matrix (Fin N) (Fin N) ℝ}
    (hδ : 0 < δ) (hA : A.IsTotallyNonneg)
    (hlower : ∀ i j, i < j → A i j = 0)
    (hdiag : ∀ i, A i i = δ) (hn : n + 1 < N) :
    Prec0 (chainPolynomial (Matrix.toLowerTriangularMatrix A) n)
      (chainPolynomial (Matrix.toLowerTriangularMatrix A) (n + 1)) := by
  rw [← chainPolynomial_diagonalTail_eq_toLowerTriangularMatrix δ A
      (lt_trans (Nat.lt_succ_self n) hn),
    ← chainPolynomial_diagonalTail_eq_toLowerTriangularMatrix δ A hn]
  exact prec0_chainPolynomial_succ_of_pos_constantDiagonal hδ
    (diagonalTail_isLowerTriangular hlower)
    (fun i => Matrix.diagonalTail_apply_diagonal δ A hdiag)
    (hA.diagonalTail hδ.le) n

end RealRooted.BrandenLeite
