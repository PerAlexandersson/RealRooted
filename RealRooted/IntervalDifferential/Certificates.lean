/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import RealRooted.IntervalDifferential.Basic
public import Mathlib.Tactic.Ring

/-!
# Polynomial certificates for the centered zigzag operator

This file formalizes the algebraic certificate and seed calculations from
Appendices C.2--C.3 of `alternating_eulerian_shorter_proof.md`.
-/

@[expose] public section

noncomputable section

namespace RealRooted.IntervalDifferential

open Polynomial

/-- The factor obtained by applying `L - a` to `F`. -/
def zigzagLinearFactor (a : ℝ) (F : ℝ[X]) : ℝ[X] :=
  zigzagOperator F - C a * F

/-- The factor obtained by applying `((L-a)^2+b^2)` to `F`. -/
def zigzagQuadraticFactor (a b : ℝ) (F : ℝ[X]) : ℝ[X] :=
  zigzagLinearFactor a (zigzagLinearFactor a F) + C (b ^ 2) * F

/-- Multiplication by a conjugate-pair factor becomes quadratic operator insertion. -/
theorem zigzagTransform_quadratic_mul (a b : ℝ) (Q : ℝ[X]) :
    zigzagTransform (((X - C a) ^ 2 + C (b ^ 2)) * Q) =
      zigzagQuadraticFactor a b (zigzagTransform Q) := by
  rw [add_mul, zigzagTransform_add, pow_two, mul_assoc,
    zigzagTransform_linear_mul, zigzagTransform_linear_mul, zigzagTransform_C_mul]
  rfl

/-- The polynomial `J` in the Appendix C.2 sign certificate. -/
def zigzagJ (d : ℕ) (F : ℝ[X]) : ℝ[X] :=
  (1 - X ^ 2) * (F.derivative ^ 2 - F * F.derivative.derivative) +
    C 2 * X * F * F.derivative - C (d : ℝ) * F ^ 2

/-- The polynomial `K` in the Appendix C.2 sign certificate. -/
def zigzagK (d : ℕ) (F : ℝ[X]) : ℝ[X] :=
  C ((d : ℝ) - 1) * F.derivative ^ 2 -
    C (d : ℝ) * F * F.derivative.derivative

/-- Appendix C.2's polynomial identity. Evaluating it at a zero of
`zigzagLinearFactor a F` removes the two correction terms on the left and
gives the sign certificate for `zigzagQuadraticFactor a b F`. -/
theorem zigzag_quadratic_certificate (d : ℕ) (a b : ℝ) (F : ℝ[X]) :
    -C ((d + 2 : ℕ) : ℝ) * F * zigzagQuadraticFactor a b F +
        C ((d + 1 : ℕ) : ℝ) * zigzagLinearFactor a F ^ 2 +
        C 2 * (C ((d + 3 : ℕ) : ℝ) * X - C a) * F *
          zigzagLinearFactor a F =
      C 2 * (1 - X ^ 2) * zigzagJ d F +
        (1 - X ^ 2) ^ 2 * zigzagK d F +
        (C ((d + 3 : ℕ) : ℝ) * (C a - X) ^ 2 +
          C ((5 * d + 6 : ℕ) : ℝ) -
          C ((d + 2 : ℕ) : ℝ) * C (a ^ 2 + b ^ 2)) * F ^ 2 := by
  simp only [zigzagLinearFactor, zigzagQuadraticFactor, zigzagJ, zigzagK,
    zigzagOperator_apply, derivative_sub, derivative_add, derivative_mul,
    derivative_pow, derivative_C, derivative_X, derivative_one, zero_mul]
  simp only [map_add, map_sub, map_mul, map_pow, map_one, map_natCast, map_ofNat,
    Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  ring

/-- The certificate makes the quadratic insertion have the opposite sign to
`F` at every zero of the linear insertion. The hypotheses package the two
Appendix C.2 inequalities and the disk-bound coefficient estimate. -/
theorem zigzag_quadratic_eval_mul_neg (d : ℕ) (a b s : ℝ) (F : ℝ[X])
    (h : 0 < 1 - s ^ 2)
    (hJ : 0 < (zigzagJ d F).eval s)
    (hK : 0 ≤ (zigzagK d F).eval s)
    (hcoef : 0 ≤ (d + 3) * (a - s) ^ 2 + 5 * d + 6 -
      (d + 2) * (a ^ 2 + b ^ 2))
    (hroot : (zigzagLinearFactor a F).eval s = 0) :
    F.eval s * (zigzagQuadraticFactor a b F).eval s < 0 := by
  have hcert := congrArg (fun p : ℝ[X] => p.eval s)
    (zigzag_quadratic_certificate d a b F)
  simp only [eval_add, eval_mul, eval_neg, eval_C, eval_sub, eval_pow, eval_X]
    at hcert
  simp only [eval_one] at hcert
  norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hcert
  rw [hroot] at hcert
  have hfirst : 0 < 2 * (1 - s ^ 2) * (zigzagJ d F).eval s := by
    positivity
  have hsecond : 0 ≤ (1 - s ^ 2) ^ 2 * (zigzagK d F).eval s :=
    mul_nonneg (sq_nonneg _) hK
  have hthird : 0 ≤ ((d + 3) * (a - s) ^ 2 + 5 * d + 6 -
      (d + 2) * (a ^ 2 + b ^ 2)) * (F.eval s) ^ 2 :=
    mul_nonneg hcoef (sq_nonneg _)
  have hsum : 0 < 2 * (1 - s ^ 2) * (zigzagJ d F).eval s +
      (1 - s ^ 2) ^ 2 * (zigzagK d F).eval s +
      ((d + 3) * (a - s) ^ 2 + 5 * d + 6 -
        (d + 2) * (a ^ 2 + b ^ 2)) * (F.eval s) ^ 2 := by
    linarith
  have hd : 0 < (d : ℝ) + 2 := by positivity
  have hprod : ((d : ℝ) + 2) *
      (F.eval s * (zigzagQuadraticFactor a b F).eval s) < 0 := by
    nlinarith [hcert, hsum]
  by_contra hnot
  have hnonneg : 0 ≤ F.eval s * (zigzagQuadraticFactor a b F).eval s :=
    le_of_not_gt hnot
  nlinarith [mul_nonneg hd.le hnonneg]

private theorem zigzagOperator_pow_one_three :
    (zigzagOperator ^ 3) 1 = C 60 * X ^ 3 - C 33 * X := by
  change zigzagOperator (zigzagOperator (zigzagOperator 1)) = _
  simp [zigzagOperator_apply]
  norm_num [Polynomial.C_ofNat]
  ring

private theorem zigzagOperator_pow_one_four :
    (zigzagOperator ^ 4) 1 =
      C 360 * X ^ 4 - C 312 * X ^ 2 + C 33 := by
  change zigzagOperator (zigzagOperator (zigzagOperator (zigzagOperator 1))) = _
  simp [zigzagOperator_apply]
  norm_num [Polynomial.C_ofNat]
  ring

private theorem zigzagOperator_pow_one_two :
    (zigzagOperator ^ 2) 1 = C 12 * X ^ 2 - C 3 := by
  change zigzagOperator (zigzagOperator 1) = _
  simp [zigzagOperator_apply]
  norm_num [Polynomial.C_ofNat]
  ring

private theorem zigzagOperator_pow_one_one :
  zigzagOperator 1 = C 3 * X := by
  simp [zigzagOperator_apply]

/-- The cubic seed transform from Appendix C.3. -/
theorem zigzagTransform_cubic (k : ℝ) :
    zigzagTransform (X ^ 3 + C k * X) =
      C 3 * X * (C 20 * X ^ 2 + C (k - 11)) := by
  rw [zigzagTransform_add, zigzagTransform_C_mul]
  rw [zigzagTransform_X_pow 3, zigzagOperator_pow_one_three]
  have hX : zigzagTransform X = C 3 * X := by
    calc
      zigzagTransform X = zigzagOperator 1 := by
        simpa only [pow_one] using zigzagTransform_X_pow 1
      _ = C 3 * X := zigzagOperator_pow_one_one
  rw [hX]
  simp only [map_sub, map_ofNat]
  ring

/-- The quartic seed transform from Appendix C.3. -/
theorem zigzagTransform_quartic (k p : ℝ) :
    zigzagTransform (X ^ 4 + C k * X ^ 2 + C p) =
      C 360 * X ^ 4 + C (12 * k - 312) * X ^ 2 + C (33 - 3 * k + p) := by
  rw [zigzagTransform_add, zigzagTransform_add]
  rw [zigzagTransform_X_pow 4, zigzagTransform_C_mul, zigzagTransform_X_pow 2]
  have hp : zigzagTransform (C p) = C p := by
    rw [show C p = C p * (1 : ℝ[X]) by simp,
      zigzagTransform_C_mul, zigzagTransform_one]
  rw [hp, zigzagOperator_pow_one_four, zigzagOperator_pow_one_two]
  simp only [map_add, map_sub, map_mul]
  ring

end RealRooted.IntervalDifferential
