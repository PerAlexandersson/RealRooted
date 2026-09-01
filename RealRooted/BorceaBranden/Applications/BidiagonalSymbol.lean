import RealRooted.BorceaBranden.Applications.ComplexUnivariateSymbol
import RealRooted.BorceaBranden.Applications.DegreeBoxPolarization
import RealRooted.MultiplierSequence.Bidiagonal

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
  toFun := bidiagonalOperator alpha beta
  map_add' p q := by
    simp only [bidiagonalOperator, diagonalOperator_add, mul_add]
    abel
  map_smul' c p := by
    simp only [bidiagonalOperator, smul_eq_C_mul, diagonalOperator_C_mul]
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
  simp [bidiagonalLinearMap, bidiagonalOperator, Polynomial.X_pow_eq_monomial,
    diagonalOperator_monomial, Challenges.BorceaBranden.polynomialInFirstMv]

/-! ## Complex degree-box application -/

/-- Coefficientwise complex diagonal operator. -/
def complexDiagonalOperator (gamma : ℕ → ℂ) (p : ℂ[X]) : ℂ[X] :=
  p.sum fun n a => Polynomial.monomial n (gamma n * a)

@[simp] theorem coeff_complexDiagonalOperator
    (gamma : ℕ → ℂ) (p : ℂ[X]) (n : ℕ) :
    (complexDiagonalOperator gamma p).coeff n = gamma n * p.coeff n := by
  classical
  rw [complexDiagonalOperator, Polynomial.coeff_sum]
  simp only [Polynomial.coeff_monomial]
  rw [Polynomial.sum_def]
  simp_all

theorem complexDiagonalOperator_add (gamma : ℕ → ℂ) (p q : ℂ[X]) :
    complexDiagonalOperator gamma (p + q) =
      complexDiagonalOperator gamma p + complexDiagonalOperator gamma q := by
  ext n
  simp [mul_add]

theorem complexDiagonalOperator_C_mul
    (gamma : ℕ → ℂ) (a : ℂ) (p : ℂ[X]) :
    complexDiagonalOperator gamma (C a * p) =
      C a * complexDiagonalOperator gamma p := by
  ext n
  simp [mul_comm, mul_left_comm]

theorem complexDiagonalOperator_monomial
    (gamma : ℕ → ℂ) (n : ℕ) (a : ℂ) :
    complexDiagonalOperator gamma (Polynomial.monomial n a) =
      Polynomial.monomial n (gamma n * a) := by
  ext k
  by_cases hk : k = n
  · simp_all
  · simp [Polynomial.coeff_monomial, Ne.symm hk]

/-- Complex-linear extension of the real bidiagonal operator. -/
def complexBidiagonalLinearMap (alpha beta : ℕ → ℝ) :
    Polynomial ℂ →ₗ[ℂ] Polynomial ℂ where
  toFun := fun p =>
    complexDiagonalOperator (fun k => (alpha k : ℂ)) p +
      Polynomial.X * complexDiagonalOperator (fun k => (beta k : ℂ)) p
  map_add' p q := by
    simp only [complexDiagonalOperator_add, mul_add]
    abel
  map_smul' c p := by
    simp only [smul_eq_C_mul, complexDiagonalOperator_C_mul]
    simp only [RingHom.id_apply]
    ring

/-- The complex finite symbol of the complexified bidiagonal operator is the
coefficientwise complexification of the already computed real affine symbol. -/
theorem complexFiniteAlgebraicSymbol_complexBidiagonalLinearMap
    (alpha beta : ℕ → ℝ) (d : ℕ) :
    complexFiniteAlgebraicSymbol d (complexBidiagonalLinearMap alpha beta) =
      complexifyMv
        (Challenges.BorceaBranden.finiteAlgebraicSymbol d
          (bidiagonalLinearMap alpha beta)) := by
  classical
  rw [finiteAlgebraicSymbol_bidiagonalLinearMap]
  simp only [complexFiniteAlgebraicSymbol, affineBidiagonalSymbol,
    complexifyMv, map_sum]
  apply Finset.sum_congr rfl
  intro k _
  simp [complexPolynomialInFirstMv, complexBidiagonalLinearMap,
    Polynomial.X_pow_eq_monomial, complexDiagonalOperator_monomial, pow_succ]

/-- Borcea--Branden, Theorem 1.1, symbol identification for the complexified
bidiagonal operator. The equality uses the affine, not homogeneous, finite
symbol computed by `finiteAlgebraicSymbol_bidiagonalLinearMap`. -/
theorem algebraicSymbol_complexBidiagonalDegreeBoxOperator
    (alpha beta : ℕ → ℝ) (d : ℕ) :
    MvPolynomial.algebraicSymbol (fun _ : Fin 1 => d)
        (complexUnivariateDegreeBoxOperator d
          (complexBidiagonalLinearMap alpha beta)) =
      MvPolynomial.rename finOneSumEquivFinTwo.symm
        (complexifyMv
          (Challenges.BorceaBranden.finiteAlgebraicSymbol d
            (bidiagonalLinearMap alpha beta))) := by
  have h := congrArg (MvPolynomial.rename finOneSumEquivFinTwo.symm)
    (rename_algebraicSymbol_complexUnivariateDegreeBoxOperator d
      (complexBidiagonalLinearMap alpha beta))
  rw [complexFiniteAlgebraicSymbol_complexBidiagonalLinearMap] at h
  have hcomp : finOneSumEquivFinTwo.symm ∘ finOneSumToFinTwo = id := by
    funext i
    exact finOneSumEquivFinTwo.symm_apply_apply i
  rw [MvPolynomial.rename_rename, hcomp, MvPolynomial.rename_id] at h
  exact h

/-- Explicit bidiagonal application of finite degree-box symbol sufficiency.

This is exactly the sufficiency implication in Borcea--Branden, Theorem 1.1,
after equations (2.1)--(2.2). The symbol hypothesis is genuine bivariate
upper-half-plane stability; no Jensen-pencil or PF conclusion is assumed. -/
theorem complexBidiagonalDegreeBox_preserves_stability
    (alpha beta : ℕ → ℝ) (d : ℕ)
    (hSymbol : MvUpperHalfPlaneStable
      (complexifyMv
        (Challenges.BorceaBranden.finiteAlgebraicSymbol d
          (bidiagonalLinearMap alpha beta))))
    (f : MvPolynomial.degreeOfLE (Fin 1) ℂ (fun _ => d))
    (hf : MvUpperHalfPlaneStable f.1) :
    MvUpperHalfPlaneStableOrZero
      (complexUnivariateDegreeBoxOperator d
        (complexBidiagonalLinearMap alpha beta) f) := by
  apply finiteSymbol_finOne_preserves_stability d _ ?_ f hf
  rw [algebraicSymbol_complexBidiagonalDegreeBoxOperator]
  exact hSymbol.rename

end RealRooted.BorceaBranden
