import RealRooted.BorceaBranden.Applications.UnivariateSymbol
import RealRooted.MultiplierSequence

/-!
# Algebraic symbols of bidiagonal polynomial operators

This module computes the genuine affine Borcea--Branden algebraic symbol of a
bidiagonal polynomial operator. This symbol is distinct from the homogeneous
binary form used by the finite-symbol tactic.
-/

noncomputable section

namespace RealRooted.BorceaBranden

open Polynomial
open scoped BigOperators

/-- The bidiagonal polynomial operator as a linear map. -/
def bidiagonalLinearMap (alpha beta : ℕ → ℝ) : Polynomial ℝ →ₗ[ℝ] Polynomial ℝ where
  toFun := fun p => diagonalOperator alpha p + Polynomial.X * diagonalOperator beta p
  map_add' p q := by
    simp only [diagonalOperator_add, mul_add]
    abel
  map_smul' c p := by
    simp only [smul_eq_C_mul, diagonalOperator_C_mul]
    simp [mul_comm]
    ring

/-- The genuine affine algebraic symbol of a bidiagonal operator on degree at most `d`. -/
def affineBidiagonalSymbol (alpha beta : ℕ → ℝ) (d : ℕ) : MvPolynomial (Fin 2) ℝ :=
  ∑ k ∈ Finset.range (d + 1),
    MvPolynomial.C (d.choose k : ℝ) *
      (MvPolynomial.C (alpha k) * MvPolynomial.X 0 ^ k +
        MvPolynomial.C (beta k) * MvPolynomial.X 0 ^ (k + 1)) *
      MvPolynomial.X 1 ^ (d - k)

/-- The finite algebraic symbol of `bidiagonalLinearMap` is the affine bidiagonal symbol. -/
theorem finiteAlgebraicSymbol_bidiagonalLinearMap (alpha beta : ℕ → ℝ) (d : ℕ) :
    Challenges.BorceaBranden.finiteAlgebraicSymbol d (bidiagonalLinearMap alpha beta) =
      affineBidiagonalSymbol alpha beta d := by
  simp only [Challenges.BorceaBranden.finiteAlgebraicSymbol, affineBidiagonalSymbol]
  apply Finset.sum_congr rfl
  intro k hk
  congr 1
  simp [bidiagonalLinearMap, Polynomial.X_pow_eq_monomial, diagonalOperator_monomial,
    Challenges.BorceaBranden.polynomialInFirstMv]

end RealRooted.BorceaBranden
