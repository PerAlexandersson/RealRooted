module

public import RealRooted.ExponentialRows.SubstitutionKernel
public import RealRooted.Hermite.Poulain
public import RealRooted.ExponentialRows.ProductInsertion
import Mathlib.Tactic

/-!
# Polynomial symbols for exponential substitution

The kernel operator associated with `P - P(0)` intertwines the constant
coefficient operator `P(D)` with the parameter derivative plus `P(0)`.
Multiplication by the input variable is intertwined with `t P'(D)`.
These identities are algebraic and impose no root or sign hypotheses.

Source: unpublished manuscript, degree-raising substitutions, RealRooted #2415:
https://github.com/PerAlexandersson/RealRooted/issues/2415#issuecomment-7141592218.
-/

public section

open Polynomial Finset
open RealRooted.HermitePoulain

namespace RealRooted.ExponentialRows

/-- The kernel basis transform sends a monomial to its factorial kernel row. -/
theorem exponentialSubstitution_X_pow (B : PowerSeries ℝ) (n : ℕ) :
    exponentialSubstitution B (X ^ n) = exponentialKernelRow B n := by
  exact basisTransform_X_pow _ _

/-- A constant-coefficient differential operator commutes with differentiation. -/
private theorem applyDifferential_derivative (q p : ℝ[X]) :
    applyAsDifferentialOperator q p.derivative =
      (applyAsDifferentialOperator q p).derivative := by
  have hX (p : ℝ[X]) : applyAsDifferentialOperator X p = p.derivative := by
    simpa only [mul_one, applyAsDifferentialOperator_one] using
      applyAsDifferentialOperator_X_mul 1 p
  rw [← hX p, ← applyAsDifferentialOperator_mul, mul_comm q X,
    applyAsDifferentialOperator_X_mul]

/-- A differential operator is additive in its input. -/
private theorem applyDifferential_add_right (q p r : ℝ[X]) :
    applyAsDifferentialOperator q (p + r) =
      applyAsDifferentialOperator q p + applyAsDifferentialOperator q r := by
  simp only [applyAsDifferentialOperator, ← pow_apply_eq_iterate, map_add, mul_add,
    sum_add_distrib]

/-- A constant factor in the input pulls out of a differential operator. -/
private theorem applyDifferential_C_mul_right (q p : ℝ[X]) (a : ℝ) :
    applyAsDifferentialOperator q (C a * p) = C a * applyAsDifferentialOperator q p := by
  simp only [applyAsDifferentialOperator, iterate_derivative_C_mul, mul_sum]
  apply sum_congr rfl
  intro j _
  ring

/-- Kernel coefficient extraction is dual to the finite differential operator
on a monomial. -/
theorem exponentialSubstitution_applyDifferential_X_pow {B : PowerSeries ℝ}
    (q : ℝ[X]) (n : ℕ) :
    exponentialSubstitution B (applyAsDifferentialOperator q (X ^ n)) =
      polynomialBracket q (exponentialKernel B) n := by
  induction q using Polynomial.induction_on' with
  | add q r hq hr =>
    rw [applyAsDifferentialOperator_add, map_add, hq, hr, polynomialBracket_add]
  | monomial k a =>
    induction k generalizing n with
    | zero =>
      rw [monomial_zero_left, applyAsDifferentialOperator_C, Polynomial.linearMap_C_mul]
      rw [exponentialSubstitution_X_pow]
      simpa only [mul_one, polynomialBracket_one, exponentialKernelRow] using
        (polynomialBracket_C_mul a 1 (exponentialKernel B) n).symm
    | succ k ih =>
      rw [← X_mul_monomial, applyAsDifferentialOperator_mul]
      have hX (p : ℝ[X]) : applyAsDifferentialOperator X p = p.derivative := by
        simpa only [mul_one, applyAsDifferentialOperator_one] using
          applyAsDifferentialOperator_X_mul 1 p
      rw [hX, ← applyDifferential_derivative]
      cases n with
      | zero =>
        simp only [pow_zero, derivative_one, applyAsDifferentialOperator_zero_right, map_zero]
        exact (polynomialBracket_zero_of_coeff_zero (by simp) _).symm
      | succ n =>
        rw [derivative_X_pow_succ, applyDifferential_C_mul_right,
          Polynomial.linearMap_C_mul, ih]
        simpa only [map_zero, add_zero, zero_mul, zero_add] using
          (polynomialBracket_linear_mul 0 (monomial k a) (exponentialKernel B) n).symm

/-- Parameter differentiation of a polynomial exponential kernel is the
constant-coefficient symbol operator on its input. -/
theorem exponentialSubstitution_applyDifferential {P : ℝ[X]}
    (p : ℝ[X]) :
    exponentialSubstitution ((P - C (P.coeff 0) : ℝ[X]) : PowerSeries ℝ)
        (applyAsDifferentialOperator P p) =
      (exponentialSubstitution ((P - C (P.coeff 0) : ℝ[X]) : PowerSeries ℝ) p).derivative +
        C (P.coeff 0) *
          exponentialSubstitution ((P - C (P.coeff 0) : ℝ[X]) : PowerSeries ℝ) p := by
  let B : PowerSeries ℝ := (P - C (P.coeff 0) : ℝ[X])
  have hB : PowerSeries.constantCoeff B = 0 := by
    simp only [B, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_coe,
      coeff_sub, coeff_C_zero, sub_self]
  have hseries : Polynomial.coeToPowerSeries.algHom ℝ[X] P =
      B.map C + PowerSeries.C (C (P.coeff 0)) := by
    apply PowerSeries.ext
    intro n
    simp only [coeff_polynomialSeries, map_add, PowerSeries.coeff_map,
      PowerSeries.coeff_C, B, coeff_coe, coeff_sub, coeff_C, map_sub]
    split_ifs <;> simp only [map_zero, sub_zero, add_zero, sub_add_cancel]
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [applyDifferential_add_right, map_add, hp, hq]
    ring
  | monomial n a =>
    rw [← C_mul_X_pow_eq_monomial, applyDifferential_C_mul_right,
      Polynomial.linearMap_C_mul, Polynomial.linearMap_C_mul, derivative_C_mul]
    rw [exponentialSubstitution_X_pow, exponentialSubstitution_applyDifferential_X_pow]
    have h := congrArg (fun H => factorialCoeff H n) (parameterDerivative_exponentialKernel hB)
    simp only [factorialCoeff, PowerSeries.coeff_mapDerivation,
      Polynomial.derivative'_apply] at h
    have h' : (exponentialKernelRow B n).derivative =
        factorialCoeff (B.map C * exponentialKernel B) n := by
      simpa only [exponentialKernelRow, factorialCoeff, derivative_C_mul] using h
    rw [polynomialBracket, hseries, add_mul, factorialCoeff_add, factorialCoeff_C_mul]
    rw [← h']
    change C a * ((exponentialKernelRow B n).derivative +
      C (P.coeff 0) * exponentialKernelRow B n) = _
    ring

/-- Multiplication by the input variable is intertwined with `t P'(D)` for
an arbitrary polynomial outer symbol, after subtracting its constant term. -/
theorem exponentialSubstitution_X_mul_polynomial {P : ℝ[X]} (p : ℝ[X]) :
    exponentialSubstitution ((P - C (P.coeff 0) : ℝ[X]) : PowerSeries ℝ) (X * p) =
      X * exponentialSubstitution ((P - C (P.coeff 0) : ℝ[X]) : PowerSeries ℝ)
        (applyAsDifferentialOperator P.derivative p) := by
  let B : PowerSeries ℝ := (P - C (P.coeff 0) : ℝ[X])
  have hB : PowerSeries.constantCoeff B = 0 := by
    simp only [B, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_coe,
      coeff_sub, coeff_C_zero, sub_self]
  have hder : PowerSeries.derivative (B.map C) =
      Polynomial.coeToPowerSeries.algHom ℝ[X] P.derivative := by
    change PowerSeries.derivative
      (Polynomial.coeToPowerSeries.algHom ℝ[X] (P - C (P.coeff 0))) = _
    rw [derivative_polynomialSeries, map_sub, derivative_C, sub_zero]
  have hkernel : PowerSeries.derivative (exponentialKernel B) =
      PowerSeries.C X *
        (Polynomial.coeToPowerSeries.algHom ℝ[X] P.derivative * exponentialKernel B) := by
    rw [exponentialKernel, PowerSeries.derivative_subst
      (PowerSeries.HasSubst.of_constantCoeff_zero' (constantCoeff_kernelArgument hB)),
      PowerSeries.derivative_exp]
    simp only [PowerSeries.derivative.leibniz, PowerSeries.derivative_C,
      smul_eq_mul, hder]
    ring
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [mul_add, map_add, hp, hq, applyDifferential_add_right, map_add, mul_add]
  | monomial n a =>
    rw [← C_mul_X_pow_eq_monomial, mul_left_comm X, Polynomial.linearMap_C_mul,
      applyDifferential_C_mul_right, Polynomial.linearMap_C_mul, mul_left_comm X]
    congr 1
    rw [← pow_succ', exponentialSubstitution_applyDifferential_X_pow]
    rw [exponentialSubstitution_X_pow]
    change exponentialKernelRow B (n + 1) = _
    rw [exponentialKernelRow, ← factorialCoeff_derivative, hkernel, factorialCoeff_C_mul]
    rfl

end RealRooted.ExponentialRows
