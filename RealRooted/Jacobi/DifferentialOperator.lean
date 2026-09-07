/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import RealRooted.EulerOperator.Shift
public import RealRooted.Mathlib.Algebra.Polynomial.DifferentialEquation.SecondOrder
public import RealRooted.Mathlib.RingTheory.Polynomial.Jacobi.DifferentialOperator

import Mathlib.Tactic

/-!
# Differential identities for shifted Jacobi operators

This file combines the coefficient-ring Jacobi operator with shifted Euler
operators and generic second-order ODE infrastructure. No root-order or
orthogonality imports are used here.
-/

@[expose] public section

open Polynomial

noncomputable section

namespace RealRooted

/-- The first shifted-Euler inverse identity for an arbitrary beta-one Jacobi
solution. The scalar relation replaces the packet-specific constants in the
original application. -/
theorem eulerShift_first_offset_of_jacobi_differential
    {R : Type*} [CommRing R]
    (T : R[X]) (b A D c t : R)
    (hode : jacobiDifferentialOperator b (b + 2) T + C D * T = 0)
    (hrel : D * c = A * (b - t)) :
    eulerShift b
        (C A * ((1 - X) * T) + C c * ((1 - X) ^ 2 * T.derivative)) =
      eulerShift t (C A * ((1 - X) * T)) := by
  have hrelC : C D * C c = C (A * (b - t)) := by
    rw [← C_mul, hrel]
  have hC2 : C (2 : R) = (2 : R[X]) := Polynomial.C_ofNat 2
  unfold jacobiDifferentialOperator at hode
  unfold eulerShift
  simp only [derivative_add, derivative_mul, derivative_C, derivative_sub,
    derivative_one, derivative_X, zero_mul, zero_add, pow_two] at hode ⊢
  simp only [map_add, map_sub, map_mul] at hode hrelC ⊢
  simp only [hC2] at hode hrelC ⊢
  linear_combination (1 - X) * C c * hode + (X - 1) * T * hrelC

/-- Eliminate a second derivative from a shifted Jacobi ODE after multiplying
by the left endpoint variable. -/
theorem jacobi_second_derivative_reduce
    {R : Type*} [CommRing R]
    (T : R[X]) (b c D c₀ c₁ c₂ : R)
    (hode : jacobiDifferentialOperator b c T + C D * T = 0) :
    X * (C c₀ * T + C c₁ * ((1 - X) * T.derivative) +
        C c₂ * ((1 - X) ^ 2 * T.derivative.derivative)) =
      (C c₀ * X - C (c₂ * D) * (1 - X)) * T +
        (C c₁ * X * (1 - X) -
          C c₂ * (1 - X) * (C b - C c * X)) * T.derivative := by
  have hode' :
      X * (1 - X) * T.derivative.derivative +
        (C b - C c * X) * T.derivative + C D * T = 0 := by
    simpa [jacobiDifferentialOperator] using hode
  have h := Polynomial.second_derivative_reduce_of_second_order_ode
    T (1 - X) X (C b - C c * X) (C D) c₀ c₁ c₂ hode'
  calc
    _ = (C c₀ * X - C c₂ * (1 - X) * C D) * T +
        (C c₁ * X * (1 - X) -
          C c₂ * (1 - X) * (C b - C c * X)) * T.derivative := h
    _ = _ := by
      simp only [map_mul]
      ring

end RealRooted
