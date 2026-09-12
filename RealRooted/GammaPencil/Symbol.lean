/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
import RealRooted.BorceaBranden.UnivariateFiniteSymbol
import RealRooted.GammaPencil.Basic

/-!
# Finite algebraic symbol of the gamma operator

This module computes the degree-box Borcea--Branden symbol of the gamma-pencil
operator.  The two explicit univariate factors are retained for the subsequent
proper-position and stability argument.
-/

open Polynomial
open scoped BigOperators

noncomputable section

namespace RealRooted

/-- The coefficient of the second symbol variable in the gamma symbol. -/
def gammaSymbolQ (n : ℕ) : ℝ[X] :=
  1 + C ((2 : ℝ) * (n : ℝ)) * X

/-- The first-variable residual factor in the degree-`m` gamma symbol. -/
def gammaSymbolP (n m : ℕ) : ℝ[X] :=
  X * (C ((m : ℝ) + 1) +
    C ((2 : ℝ) * (n : ℝ) - (4 : ℝ) * (m : ℝ)) * X)

private theorem polynomialInFirstMv_gammaOperator_X_pow
    (n k : ℕ) :
    BorceaBranden.polynomialInFirstMv (gammaOperator n ((X : ℝ[X]) ^ k)) =
      MvPolynomial.C ((k : ℝ) + 1) * MvPolynomial.X 0 ^ k +
        MvPolynomial.C ((2 : ℝ) * (n : ℝ) - (4 : ℝ) * (k : ℝ)) *
          MvPolynomial.X 0 ^ (k + 1) := by
  cases k with
  | zero =>
      simp [gammaOperator_apply, BorceaBranden.polynomialInFirstMv]
  | succ k =>
      simp only [gammaOperator_apply, derivative_pow, derivative_X,
        Nat.cast_add, Nat.cast_one, map_add, map_sub, map_one,
        BorceaBranden.polynomialInFirstMv, Polynomial.eval₂_add,
        Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_C,
        Polynomial.eval₂_X, Polynomial.eval₂_pow]
      simp
      ring

/-- The degree-zero gamma symbol is the coefficient factor alone.  The
positive-degree factorization has a genuine `(z + w) ^ (m - 1)` factor, so
this boundary is recorded separately. -/
theorem finiteAlgebraicSymbol_gammaOperator_zero (n : ℕ) :
    BorceaBranden.finiteAlgebraicSymbol 0 (gammaOperator n) =
      BorceaBranden.polynomialInFirstMv (gammaSymbolQ n) := by
  simp [BorceaBranden.finiteAlgebraicSymbol, gammaSymbolQ, gammaOperator_apply,
    BorceaBranden.polynomialInFirstMv]

/-- The finite algebraic symbol of the gamma operator in a positive degree
box.  It is `(z + w) ^ (m - 1) * (p_{n,m}(z) + w * q_n(z))`. -/
theorem finiteAlgebraicSymbol_gammaOperator_factorization
    (n m : ℕ) (hm : 1 ≤ m) :
    BorceaBranden.finiteAlgebraicSymbol m (gammaOperator n) =
      (MvPolynomial.X 0 + MvPolynomial.X 1) ^ (m - 1) *
        (BorceaBranden.polynomialInFirstMv (gammaSymbolP n m) +
          MvPolynomial.X 1 * BorceaBranden.polynomialInFirstMv (gammaSymbolQ n)) := by
  let x : MvPolynomial (Fin 2) ℝ := MvPolynomial.X 0
  let y : MvPolynomial (Fin 2) ℝ := MvPolynomial.X 1
  let S : MvPolynomial (Fin 2) ℝ := (x + y) ^ m
  have hS : S = ∑ k ∈ Finset.range (m + 1),
      MvPolynomial.C (m.choose k : ℝ) * x ^ k * y ^ (m - k) := by
    dsimp [S]
    rw [add_pow]
    apply Finset.sum_congr rfl
    intro k hk
    simp
    ring
  have hder : MvPolynomial.pderiv 0 S =
      MvPolynomial.C (m : ℝ) * (x + y) ^ (m - 1) := by
    dsimp [S]
    rw [MvPolynomial.pderiv_pow]
    simp [x, y]
  have hxder : x * MvPolynomial.pderiv 0 S =
      ∑ k ∈ Finset.range (m + 1),
        MvPolynomial.C (m.choose k : ℝ) *
          (MvPolynomial.C (k : ℝ) * x ^ k) * y ^ (m - k) := by
    rw [hS]
    simp only [map_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_mul,
      MvPolynomial.pderiv_C, MvPolynomial.pderiv_pow,
      MvPolynomial.pderiv_pow]
    simp only [Fin.isValue, zero_mul, map_natCast, MvPolynomial.pderiv_X,
      Pi.single_eq_same, mul_one, zero_add, ne_eq, one_ne_zero,
      not_false_eq_true, Pi.single_eq_of_ne, mul_zero, add_zero, x, y]
    cases k with
    | zero => simp
    | succ k =>
        rw [show k + 1 - 1 = k by lia, pow_succ]
        push_cast
        ring
  rw [BorceaBranden.finiteAlgebraicSymbol]
  simp only [polynomialInFirstMv_gammaOperator_X_pow]
  rw [show (∑ k ∈ Finset.range (m + 1),
      MvPolynomial.C (m.choose k : ℝ) *
        (MvPolynomial.C ((k : ℝ) + 1) * x ^ k +
          MvPolynomial.C ((2 : ℝ) * (n : ℝ) - (4 : ℝ) * (k : ℝ)) *
            x ^ (k + 1)) * y ^ (m - k)) =
      (1 + MvPolynomial.C ((2 : ℝ) * (n : ℝ)) * x) * S +
        (x - MvPolynomial.C (4 : ℝ) * x * x) * MvPolynomial.pderiv 0 S by
    rw [show (x - MvPolynomial.C (4 : ℝ) * x * x) *
        MvPolynomial.pderiv 0 S =
        (1 - MvPolynomial.C (4 : ℝ) * x) *
          (x * MvPolynomial.pderiv 0 S) by ring]
    rw [hxder, hS, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    simp only [map_add, map_sub, map_mul, map_one]
    ring]
  rw [hder]
  dsimp [S, x, y]
  have hpow :
      (MvPolynomial.X 0 + MvPolynomial.X 1 : MvPolynomial (Fin 2) ℝ) ^ m =
        (MvPolynomial.X 0 + MvPolynomial.X 1) ^ (m - 1) *
          (MvPolynomial.X 0 + MvPolynomial.X 1) := by
    conv_lhs => rw [show m = (m - 1) + 1 by lia, pow_succ]
  rw [hpow]
  simp only [gammaSymbolP, gammaSymbolQ, BorceaBranden.polynomialInFirstMv,
    Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_C,
    Polynomial.eval₂_X, Polynomial.eval₂_one]
  simp only [map_add, map_sub, map_mul, map_one]
  ring

end RealRooted
