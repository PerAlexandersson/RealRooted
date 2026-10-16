/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.Algebra.Polynomial.Derivation
public import Mathlib.Algebra.Polynomial.Module.AEval
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Ring

/-!
# The centered zigzag differential operator

The operator here is the finite algebraic part of Appendix A.3 of
`alternating_eulerian_shorter_proof.md`. Its polynomial functional calculus
uses `Polynomial.aeval` in the real linear endomorphism algebra.
-/

@[expose] public noncomputable section

open Finset Polynomial

namespace RealRooted.IntervalDifferential

/-- The centered zigzag operator `L F = (X² - 1) F' + 3 X F`. -/
def zigzagOperator : ℝ[X] →ₗ[ℝ] ℝ[X] where
  toFun F := (X ^ 2 - 1) * F.derivative + C 3 * X * F
  map_add' F G := by
    simp only [derivative_add, mul_add]
    ring
  map_smul' c F := by
    simp only [smul_eq_C_mul, derivative_C_mul, RingHom.id_apply]
    ring

@[simp] theorem zigzagOperator_apply (F : ℝ[X]) :
    zigzagOperator F = (X ^ 2 - 1) * F.derivative + C 3 * X * F := rfl

/-- Evaluate a real polynomial at the zigzag operator in the endomorphism algebra. -/
def zigzagFunctionalCalculus (Q : ℝ[X]) : Module.End ℝ ℝ[X] :=
  aeval zigzagOperator Q

/-- The centered zigzag transform of `Q`, namely `Q(L) 1`. -/
def zigzagTransform (Q : ℝ[X]) : ℝ[X] :=
  zigzagFunctionalCalculus Q 1

@[simp] theorem zigzagTransform_one : zigzagTransform 1 = 1 := by
  simp [zigzagTransform, zigzagFunctionalCalculus]

theorem zigzagTransform_add (Q R : ℝ[X]) :
    zigzagTransform (Q + R) = zigzagTransform Q + zigzagTransform R := by
  simp only [zigzagTransform, zigzagFunctionalCalculus, map_add, LinearMap.add_apply]

theorem zigzagTransform_C_mul (c : ℝ) (Q : ℝ[X]) :
    zigzagTransform (C c * Q) = C c * zigzagTransform Q := by
  simp only [zigzagTransform, zigzagFunctionalCalculus, map_mul, aeval_C,
    Module.End.mul_apply, Module.algebraMap_end_apply, smul_eq_C_mul]

theorem zigzagTransform_X_pow (n : ℕ) :
    zigzagTransform (X ^ n) = (zigzagOperator ^ n) 1 := by
  simp only [zigzagTransform, zigzagFunctionalCalculus, map_pow, aeval_X]

/-- Inserting a linear factor into the functional calculus. -/
theorem zigzagTransform_linear_mul (t : ℝ) (Q : ℝ[X]) :
    zigzagTransform ((X - C t) * Q) =
      zigzagOperator (zigzagTransform Q) - C t * zigzagTransform Q := by
  simp only [zigzagTransform, zigzagFunctionalCalculus, map_mul, map_sub,
    aeval_X, aeval_C, LinearMap.sub_apply, Module.End.mul_apply]
  simp only [Module.algebraMap_end_apply, smul_eq_C_mul]

/-- The two families of centered linear factors in Appendix A.3. -/
def zigzagBasis (a b : ℕ) : ℝ[X] :=
  (∏ j ∈ range a, (X - C (2 * (j : ℝ) + 3))) *
    (∏ j ∈ range b, (X + C (2 * (j : ℝ) + 3)))

@[simp] theorem zigzagBasis_zero_zero : zigzagBasis 0 0 = 1 := by
  simp [zigzagBasis]

theorem zigzagBasis_succ_left (a b : ℕ) :
    zigzagBasis (a + 1) b =
      (X - C (2 * (a : ℝ) + 3)) * zigzagBasis a b := by
  simp only [zigzagBasis, prod_range_succ]
  ring

theorem zigzagBasis_succ_right (a b : ℕ) :
    zigzagBasis a (b + 1) =
      (X + C (2 * (b : ℝ) + 3)) * zigzagBasis a b := by
  simp only [zigzagBasis, prod_range_succ]
  ring

private theorem linear_pow_mul_derivative (p : ℝ[X]) (hp : p.derivative = 1)
    (n : ℕ) : p * (p ^ n).derivative = C (n : ℝ) * p ^ n := by
  cases n with
  | zero => simp
  | succ n =>
    rw [derivative_pow_succ, hp]
    simp only [mul_one, Nat.cast_add, Nat.cast_one]
    ring

private theorem zigzagOperator_factor (a b : ℕ) :
    zigzagOperator ((X - 1) ^ a * (X + 1) ^ b) =
      (C (a : ℝ) * (X + 1) + C (b : ℝ) * (X - 1) + C 3 * X) *
        ((X - 1) ^ a * (X + 1) ^ b) := by
  have ha : (X - 1 : ℝ[X]) * (((X - 1 : ℝ[X]) ^ a).derivative) =
      C (a : ℝ) * (X - 1) ^ a :=
    linear_pow_mul_derivative (X - 1) (by simp) a
  have hb : (X + 1 : ℝ[X]) * (((X + 1 : ℝ[X]) ^ b).derivative) =
      C (b : ℝ) * (X + 1) ^ b :=
    linear_pow_mul_derivative (X + 1) (by simp) b
  change ((X : ℝ[X]) ^ 2 - 1) *
      (((X : ℝ[X]) - 1) ^ a * ((X : ℝ[X]) + 1) ^ b).derivative +
    C 3 * X * (((X : ℝ[X]) - 1) ^ a * ((X : ℝ[X]) + 1) ^ b) = _
  rw [derivative_mul]
  calc
    ((X : ℝ[X]) ^ 2 - 1) *
        ((((X : ℝ[X]) - 1) ^ a).derivative * ((X : ℝ[X]) + 1) ^ b +
          ((X : ℝ[X]) - 1) ^ a * (((X : ℝ[X]) + 1) ^ b).derivative) +
        C 3 * X * (((X : ℝ[X]) - 1) ^ a * ((X : ℝ[X]) + 1) ^ b) =
      ((X : ℝ[X]) + 1) *
          (((X : ℝ[X]) - 1) * (((X : ℝ[X]) - 1) ^ a).derivative) *
          ((X : ℝ[X]) + 1) ^ b +
        ((X : ℝ[X]) - 1) * ((X : ℝ[X]) - 1) ^ a *
          (((X : ℝ[X]) + 1) * (((X : ℝ[X]) + 1) ^ b).derivative) +
        C 3 * X * (((X : ℝ[X]) - 1) ^ a * ((X : ℝ[X]) + 1) ^ b) := by ring
    _ = _ := by rw [ha, hb]; ring

/-- The left factor raises the exponent of `X - 1`, Appendix A.3. -/
theorem zigzagOperator_sub_left (a b : ℕ) :
    zigzagOperator ((X - 1) ^ a * (X + 1) ^ b) -
      C (2 * (a : ℝ) + 3) * ((X - 1) ^ a * (X + 1) ^ b) =
      C ((a + b + 3 : ℕ) : ℝ) * ((X - 1) ^ (a + 1) * (X + 1) ^ b) := by
  rw [zigzagOperator_factor, pow_succ]
  push_cast
  simp only [map_add, map_mul, map_ofNat]
  ring

/-- The right factor raises the exponent of `X + 1`, Appendix A.3. -/
theorem zigzagOperator_add_right (a b : ℕ) :
    zigzagOperator ((X - 1) ^ a * (X + 1) ^ b) +
      C (2 * (b : ℝ) + 3) * ((X - 1) ^ a * (X + 1) ^ b) =
      C ((a + b + 3 : ℕ) : ℝ) * ((X - 1) ^ a * (X + 1) ^ (b + 1)) := by
  rw [zigzagOperator_factor, pow_succ]
  push_cast
  simp only [map_add, map_mul, map_ofNat]
  ring

private theorem zigzagOperator_C_mul (c : ℝ) (F : ℝ[X]) :
    zigzagOperator (C c * F) = C c * zigzagOperator F := by
  simpa only [smul_eq_C_mul] using zigzagOperator.map_smul c F

/-- Appendix A.3: the finite product of linear operator factors acts on `1`
as a scalar multiple of the two boundary powers. -/
theorem zigzagBasis_transform (a b : ℕ) :
    C 2 * zigzagTransform (zigzagBasis a b) =
      C (((a + b + 2).factorial : ℕ) : ℝ) *
        ((X - 1) ^ a * (X + 1) ^ b) := by
  induction a generalizing b with
  | zero =>
    induction b with
    | zero =>
      simp [zigzagBasis_zero_zero, zigzagTransform_one]
    | succ b ih =>
      have hplus :
          zigzagTransform ((X + C (2 * (b : ℝ) + 3)) * zigzagBasis 0 b) =
            zigzagOperator (zigzagTransform (zigzagBasis 0 b)) +
              C (2 * (b : ℝ) + 3) * zigzagTransform (zigzagBasis 0 b) := by
        simpa only [map_neg, sub_neg_eq_add, neg_mul, sub_neg_eq_add] using
          zigzagTransform_linear_mul (-(2 * (b : ℝ) + 3)) (zigzagBasis 0 b)
      rw [zigzagBasis_succ_right, hplus]
      have hstep := zigzagOperator_add_right 0 b
      simp only [pow_zero, one_mul, zero_add] at hstep
      have hfac :
          (((0 + (b + 1) + 2).factorial : ℕ) : ℝ) =
            (((0 + b + 2).factorial : ℕ) : ℝ) * (b + 3 : ℝ) := by
        simp only [Nat.zero_add]
        rw [show b + 1 + 2 = (b + 2) + 1 by lia, Nat.factorial_succ, Nat.cast_mul]
        push_cast
        ring
      calc
        C 2 * (zigzagOperator (zigzagTransform (zigzagBasis 0 b)) +
            C (2 * (b : ℝ) + 3) * zigzagTransform (zigzagBasis 0 b)) =
          zigzagOperator (C 2 * zigzagTransform (zigzagBasis 0 b)) +
            C (2 * (b : ℝ) + 3) *
              (C 2 * zigzagTransform (zigzagBasis 0 b)) := by
                rw [zigzagOperator_C_mul]
                ring
        _ = zigzagOperator
              (C (((0 + b + 2).factorial : ℕ) : ℝ) * (X + 1) ^ b) +
              C (2 * (b : ℝ) + 3) *
                (C (((0 + b + 2).factorial : ℕ) : ℝ) * (X + 1) ^ b) := by
                  simpa only [pow_zero, one_mul] using congrArg
                    (fun F : ℝ[X] => zigzagOperator F + C (2 * (b : ℝ) + 3) * F) ih
        _ = C (((0 + b + 2).factorial : ℕ) : ℝ) *
              (zigzagOperator ((X + 1) ^ b) +
                C (2 * (b : ℝ) + 3) * (X + 1) ^ b) := by
                  rw [zigzagOperator_C_mul]
                  ring
        _ = _ := by rw [hstep, hfac, map_mul]; push_cast; ring
  | succ a ih =>
    rw [zigzagBasis_succ_left, zigzagTransform_linear_mul]
    have hfac :
        (((a + 1 + b + 2).factorial : ℕ) : ℝ) =
          (((a + b + 2).factorial : ℕ) : ℝ) * (a + b + 3 : ℝ) := by
      rw [show a + 1 + b + 2 = (a + b + 2) + 1 by lia,
        Nat.factorial_succ, Nat.cast_mul]
      push_cast
      ring
    calc
      C 2 * (zigzagOperator (zigzagTransform (zigzagBasis a b)) -
          C (2 * (a : ℝ) + 3) * zigzagTransform (zigzagBasis a b)) =
        zigzagOperator (C 2 * zigzagTransform (zigzagBasis a b)) -
          C (2 * (a : ℝ) + 3) *
            (C 2 * zigzagTransform (zigzagBasis a b)) := by
              rw [zigzagOperator_C_mul]
              ring
      _ = zigzagOperator
            (C (((a + b + 2).factorial : ℕ) : ℝ) *
              ((X - 1) ^ a * (X + 1) ^ b)) -
            C (2 * (a : ℝ) + 3) *
              (C (((a + b + 2).factorial : ℕ) : ℝ) *
                ((X - 1) ^ a * (X + 1) ^ b)) := by
                exact congrArg
                  (fun F : ℝ[X] => zigzagOperator F - C (2 * (a : ℝ) + 3) * F)
                  (ih b)
      _ = C (((a + b + 2).factorial : ℕ) : ℝ) *
            (zigzagOperator ((X - 1) ^ a * (X + 1) ^ b) -
              C (2 * (a : ℝ) + 3) * ((X - 1) ^ a * (X + 1) ^ b)) := by
                rw [zigzagOperator_C_mul]
                ring
      _ = _ := by rw [zigzagOperator_sub_left, hfac, map_mul]; push_cast; ring

end RealRooted.IntervalDifferential
