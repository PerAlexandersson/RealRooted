import RealRooted.AissenSchoenbergWhitneyBase
import RealRooted.HermiteBiehler.OddEven
import RealRooted.Mathlib.LinearAlgebra.Matrix.Hurwitz

/-!
# Classical and Lace-oriented Hurwitz matrices

This module connects `Matrix.hurwitz`, the upper-triangular classical Hurwitz
matrix, to the odd/even polynomial API. The historical
`RealRooted.hurwitz` matrix instead packages a two-row Lace matrix. Both
conventions remain available under distinct namespace-qualified names.
-/

open Polynomial

namespace Matrix

open RealRooted

/-- Even rows of the classical Hurwitz matrix of `q(X²) + X p(X²)` contain the
coefficients of `q`. -/
@[simp]
theorem hurwitz_oddEvenPolynomial_even_row (p q : ℝ[X]) (i j : ℕ) :
    hurwitz (oddEvenPolynomial p q).coeff (2 * i) j =
      if i ≤ j then q.coeff (j - i) else 0 := by
  simpa only [coeff_oddEvenPolynomial_even] using
    hurwitz_even_row_apply (oddEvenPolynomial p q).coeff i j

/-- Odd rows of the classical Hurwitz matrix of `q(X²) + X p(X²)` contain the
coefficients of `p`, shifted one column farther to the right. -/
@[simp]
theorem hurwitz_oddEvenPolynomial_odd_row (p q : ℝ[X]) (i j : ℕ) :
    hurwitz (oddEvenPolynomial p q).coeff (2 * i + 1) j =
      if i < j then p.coeff (j - (i + 1)) else 0 := by
  simpa only [coeff_oddEvenPolynomial_odd] using
    hurwitz_odd_row_apply (oddEvenPolynomial p q).coeff i j

/-- The even rows of the classical Hurwitz matrix are the transpose of the
Toeplitz matrix of the even polynomial part. -/
theorem hurwitz_oddEvenPolynomial_even_submatrix (p q : ℝ[X]) :
    (hurwitz (oddEvenPolynomial p q).coeff).submatrix (fun i => 2 * i) id =
      (toeplitz q.coeff).transpose := by
  ext i j
  change hurwitz (oddEvenPolynomial p q).coeff (2 * i) j =
    toeplitz q.coeff j i
  rw [hurwitz_oddEvenPolynomial_even_row, toeplitz_apply]

/-- The odd rows of the classical Hurwitz matrix are the transpose of the
Toeplitz matrix of the odd polynomial part, with its initial zero row
removed. -/
theorem hurwitz_oddEvenPolynomial_odd_submatrix (p q : ℝ[X]) :
    (hurwitz (oddEvenPolynomial p q).coeff).submatrix
        (fun i => 2 * i + 1) id =
      ((toeplitz p.coeff).transpose).submatrix Nat.succ id := by
  ext i j
  change hurwitz (oddEvenPolynomial p q).coeff (2 * i + 1) j =
    toeplitz p.coeff j (i + 1)
  rw [hurwitz_oddEvenPolynomial_odd_row, toeplitz_apply]
  simp only [Nat.lt_iff_add_one_le]

end Matrix
