/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import RealRooted.Mathlib.RingTheory.Polynomial.Jacobi.DifferentialOperator
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

/-!
# Recognition for polynomial solutions of the Jacobi equation

The highest coefficient restricts the degree even at exceptional parameters.
Source: unpublished proof notes in RealRooted issue #2343, equation (9), and
issue #2341, proof of Proposition 7.
-/

public section

namespace Polynomial

/-- A nonzero polynomial solution of the shifted Jacobi equation has one of
the two degrees dictated by its leading coefficient. -/
theorem natDegree_eq_or_add_eq_zero_of_jacobi_equation
    (n : ℕ) (α β : ℝ) {p : ℝ[X]} (hp : p ≠ 0)
    (hode : jacobiDifferentialOperator (α + 1) (α + β + 2) p +
      C (n * (n + α + β + 1)) * p = 0) :
    p.natDegree = n ∨ (p.natDegree : ℝ) + n + α + β + 1 = 0 := by
  have hc := congrArg (fun q : ℝ[X] => q.coeff p.natDegree) hode
  rw [coeff_jacobiDifferentialOperator_add_C_mul,
    coeff_eq_zero_of_natDegree_lt (Nat.lt_succ_self _), mul_zero, zero_add,
    coeff_natDegree, coeff_zero, mul_eq_zero] at hc
  have hc' := hc.resolve_right (leadingCoeff_ne_zero.mpr hp)
  have hfactor : ((p.natDegree : ℝ) - n) *
      ((p.natDegree : ℝ) + n + α + β + 1) = 0 := by
    linear_combination -hc'
  rcases mul_eq_zero.mp hfactor with h | h
  · exact Or.inl (Nat.cast_injective (R := ℝ) (sub_eq_zero.mp h))
  · exact Or.inr h

/-- When the second candidate degree is absent, the degree of every nonzero
polynomial solution is exactly `n`; no endpoint regularity is assumed. -/
theorem natDegree_eq_of_jacobi_equation
    (n : ℕ) (α β : ℝ)
    (hsecond : ∀ k : ℕ, (k : ℝ) + n + α + β + 1 ≠ 0)
    {p : ℝ[X]} (hp : p ≠ 0)
    (hode : jacobiDifferentialOperator (α + 1) (α + β + 2) p +
      C (n * (n + α + β + 1)) * p = 0) : p.natDegree = n := by
  exact (natDegree_eq_or_add_eq_zero_of_jacobi_equation n α β hp hode).resolve_right
    (hsecond p.natDegree)

/-- Leading-coefficient recognition for a Jacobi equation with a single possible degree. -/
theorem eq_of_jacobi_equation_of_coeff_eq
    (n : ℕ) (α β : ℝ)
    (hsecond : ∀ k : ℕ, (k : ℝ) + n + α + β + 1 ≠ 0)
    {p q : ℝ[X]}
    (hp : jacobiDifferentialOperator (α + 1) (α + β + 2) p +
      C (n * (n + α + β + 1)) * p = 0)
    (hq : jacobiDifferentialOperator (α + 1) (α + β + 2) q +
      C (n * (n + α + β + 1)) * q = 0)
    (hc : p.coeff n = q.coeff n) : p = q := by
  by_contra hne
  have hsub : p - q ≠ 0 := sub_ne_zero.mpr hne
  have hode : jacobiDifferentialOperator (α + 1) (α + β + 2) (p - q) +
      C (n * (n + α + β + 1)) * (p - q) = 0 := by
    simp only [sub_eq_add_neg, jacobiDifferentialOperator_add, jacobiDifferentialOperator_neg]
    linear_combination hp - hq
  have hdeg := natDegree_eq_of_jacobi_equation n α β hsecond hsub hode
  exact (leadingCoeff_ne_zero.mpr hsub) (by
    rw [leadingCoeff, hdeg, coeff_sub, hc, sub_self])

/-- Conjugation by a left endpoint power changes a negative parameter to a positive one. -/
theorem jacobiDifferentialOperator_X_pow_mul
    (p : ℕ) (c D : ℝ) (R : ℝ[X]) :
    jacobiDifferentialOperator (1 - (p : ℝ)) c (X ^ p * R) + C D * (X ^ p * R) =
      X ^ p * (jacobiDifferentialOperator ((p : ℝ) + 1) (c + 2 * p) R +
        C (D - p * (p + c - 1)) * R) := by
  cases p with
  | zero => simp [jacobiDifferentialOperator]
  | succ p =>
      cases p with
      | zero =>
          simp only [jacobiDifferentialOperator, Nat.cast_one, pow_one, derivative_mul,
            derivative_X, map_add, map_sub, map_mul,
            map_one, zero_add, one_mul]
          simp only [map_ofNat]
          ring
      | succ p =>
          simp only [jacobiDifferentialOperator, derivative_mul, derivative_pow,
            derivative_X, derivative_C, map_add, map_sub, map_mul, map_one, zero_mul,
            zero_add, mul_one, Nat.succ_sub_one]
          push_cast
          simp only [map_add, map_one, map_ofNat]
          rw [pow_succ X (p + 1), pow_succ X p]
          ring

/-- Conjugation by a right endpoint power changes a negative parameter to a positive one. -/
theorem jacobiDifferentialOperator_one_sub_X_pow_mul
    (q : ℕ) (b D : ℝ) (R : ℝ[X]) :
    jacobiDifferentialOperator b (b - q + 1) ((1 - X) ^ q * R) +
        C D * ((1 - X) ^ q * R) =
      (1 - X) ^ q * (jacobiDifferentialOperator b (b + q + 1) R +
        C (D - q * b) * R) := by
  cases q with
  | zero => simp
  | succ q =>
      cases q with
      | zero =>
          simp only [jacobiDifferentialOperator, Nat.cast_one, pow_one, derivative_mul,
            derivative_X, derivative_one, derivative_zero, map_add,
            map_sub, map_one, zero_add, one_mul]
          ring
      | succ q =>
          simp only [jacobiDifferentialOperator, derivative_mul, derivative_pow,
            derivative_X, derivative_one, derivative_zero, derivative_C, map_add,
            map_sub, map_mul, map_one, zero_mul, zero_add,
            Nat.succ_sub_one]
          push_cast
          simp only [map_add, map_one]
          rw [pow_succ (1 - X) (q + 1), pow_succ (1 - X) q]
          ring

end Polynomial
