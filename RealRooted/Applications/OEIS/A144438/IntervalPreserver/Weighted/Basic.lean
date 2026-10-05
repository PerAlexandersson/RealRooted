import RealRooted.Applications.OEIS.A144438.Weighted
import RealRooted.Mathlib.Algebra.Polynomial.BasisTransform

/-!
# The weighted deco Eulerian basis transform

This file defines the transform sending `X ^ n` to `weightedDecoEulerian w n`,
together with the lag and companion transforms used in the interval-preserver
argument.  Only polynomial identities are proved here.
-/

open Polynomial

noncomputable section

namespace RealRooted.Applications.OEIS

/-- The basis transform sending `X ^ n` to `weightedDecoEulerian w n`. -/
def weightedDecoTransform (w : ℝ) (p : ℝ[X]) : ℝ[X] :=
  Polynomial.basisTransform (weightedDecoEulerian w) p

@[simp]
theorem weightedDecoTransform_X_pow (w : ℝ) (n : ℕ) :
    weightedDecoTransform w (X ^ n) = weightedDecoEulerian w n :=
  Polynomial.basisTransform_X_pow (weightedDecoEulerian w) n

theorem weightedDecoTransform_add (w : ℝ) (p q : ℝ[X]) :
    weightedDecoTransform w (p + q) =
      weightedDecoTransform w p + weightedDecoTransform w q :=
  Polynomial.basisTransform_add (weightedDecoEulerian w) p q

theorem weightedDecoTransform_C_mul (w a : ℝ) (p : ℝ[X]) :
    weightedDecoTransform w (C a * p) = C a * weightedDecoTransform w p := by
  rw [show C a * p = a • p by rw [Polynomial.smul_eq_C_mul],
    weightedDecoTransform, Polynomial.basisTransform_smul]
  rfl

theorem weightedDecoTransform_neg (w : ℝ) (p : ℝ[X]) :
    weightedDecoTransform w (-p) = -weightedDecoTransform w p := by
  change Polynomial.basisTransform (weightedDecoEulerian w) (-p) =
    -Polynomial.basisTransform (weightedDecoEulerian w) p
  rw [show -p = (-1 : ℝ) • p by simp, Polynomial.basisTransform_smul]
  simp

@[simp]
theorem weightedDecoTransform_C (w a : ℝ) :
    weightedDecoTransform w (C a) = C a := by
  simp [weightedDecoTransform]

/-- The weighted lag basis sends `X ^ (n + 1)` to rank `n`. -/
def weightedDecoLagBasis (w : ℝ) : ℕ → ℝ[X]
  | 0 => 0
  | n + 1 => weightedDecoEulerian w n

/-- The lag transform associated with `weightedDecoTransform`. -/
def weightedDecoLagTransform (w : ℝ) (p : ℝ[X]) : ℝ[X] :=
  Polynomial.basisTransform (weightedDecoLagBasis w) p

@[simp]
theorem weightedDecoLagTransform_X_pow (w : ℝ) (n : ℕ) :
    weightedDecoLagTransform w (X ^ n) = weightedDecoLagBasis w n :=
  Polynomial.basisTransform_X_pow (weightedDecoLagBasis w) n

theorem weightedDecoLagTransform_add (w : ℝ) (p q : ℝ[X]) :
    weightedDecoLagTransform w (p + q) =
      weightedDecoLagTransform w p + weightedDecoLagTransform w q :=
  Polynomial.basisTransform_add (weightedDecoLagBasis w) p q

theorem weightedDecoLagTransform_C_mul (w a : ℝ) (p : ℝ[X]) :
    weightedDecoLagTransform w (C a * p) =
      C a * weightedDecoLagTransform w p := by
  rw [show C a * p = a • p by rw [Polynomial.smul_eq_C_mul],
    weightedDecoLagTransform, Polynomial.basisTransform_smul]
  rfl

@[simp]
theorem weightedDecoLagTransform_C (w a : ℝ) :
    weightedDecoLagTransform w (C a) = 0 := by
  simp [weightedDecoLagTransform, weightedDecoLagBasis]

/-- The weighted companion basis at rank `n`. -/
def weightedDecoCompanionBasis (w : ℝ) (n : ℕ) : ℝ[X] :=
  (1 - X) * (weightedDecoEulerian w n).derivative +
    C (n : ℝ) * weightedDecoEulerian w n +
      C w * weightedDecoLagBasis w n

/-- The weighted residue companion transform. -/
def weightedDecoCompanionTransform (w : ℝ) (p : ℝ[X]) : ℝ[X] :=
  Polynomial.basisTransform (weightedDecoCompanionBasis w) p

@[simp]
theorem weightedDecoCompanionTransform_X_pow (w : ℝ) (n : ℕ) :
    weightedDecoCompanionTransform w (X ^ n) =
      weightedDecoCompanionBasis w n :=
  Polynomial.basisTransform_X_pow (weightedDecoCompanionBasis w) n

theorem weightedDecoCompanionTransform_add (w : ℝ) (p q : ℝ[X]) :
    weightedDecoCompanionTransform w (p + q) =
      weightedDecoCompanionTransform w p + weightedDecoCompanionTransform w q :=
  Polynomial.basisTransform_add (weightedDecoCompanionBasis w) p q

theorem weightedDecoCompanionTransform_C_mul (w a : ℝ) (p : ℝ[X]) :
    weightedDecoCompanionTransform w (C a * p) =
      C a * weightedDecoCompanionTransform w p := by
  rw [show C a * p = a • p by rw [Polynomial.smul_eq_C_mul],
    weightedDecoCompanionTransform, Polynomial.basisTransform_smul]
  rfl

@[simp]
theorem weightedDecoCompanionTransform_C (w a : ℝ) :
    weightedDecoCompanionTransform w (C a) = 0 := by
  simp [weightedDecoCompanionTransform, weightedDecoCompanionBasis,
    weightedDecoLagBasis]

/-- The weighted companion transform in derivative-and-lag form. -/
theorem weightedDecoCompanionTransform_eq (w : ℝ) (p : ℝ[X]) :
    weightedDecoCompanionTransform w p =
      (1 - X) * (weightedDecoTransform w p).derivative +
        weightedDecoTransform w (X * p.derivative) +
          C w * weightedDecoLagTransform w p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simp only [weightedDecoCompanionTransform_add, derivative_add, mul_add,
        weightedDecoTransform_add, weightedDecoLagTransform_add, hp, hq]
      ring
  | monomial n a =>
      simp only [weightedDecoCompanionTransform,
        Polynomial.basisTransform_monomial, weightedDecoCompanionBasis,
        weightedDecoTransform, weightedDecoLagTransform, derivative_mul,
        derivative_C, zero_mul, zero_add, Polynomial.derivative_monomial]
      cases n with
      | zero => simp [weightedDecoLagBasis]
      | succ n =>
          simp only [Nat.cast_add, Nat.cast_one, Nat.succ_sub_one,
            Polynomial.X_mul_monomial, Polynomial.basisTransform_monomial,
            weightedDecoLagBasis]
          simp only [map_add, map_one, map_mul]
          ring

/-- The weighted recurrence in the one-step companion form. -/
theorem weightedDecoEulerian_succ_companion (w : ℝ) (n : ℕ) :
    weightedDecoEulerian w (n + 1) =
      (1 + X) * weightedDecoEulerian w n +
        X * weightedDecoCompanionBasis w n := by
  cases n with
  | zero => simp [weightedDecoEulerian, weightedDecoCompanionBasis,
      weightedDecoLagBasis]
  | succ n =>
      rw [weightedDecoEulerian_recurrence]
      simp only [weightedDecoCompanionBasis, weightedDecoLagBasis, map_add,
        map_one, Nat.cast_add, Nat.cast_one]
      rw [show C (2 : ℝ) = 2 by norm_num [map_ofNat]]
      ring

/-- Multiplication by `X` under the weighted transform. -/
theorem weightedDecoTransform_X_mul (w : ℝ) (p : ℝ[X]) :
    weightedDecoTransform w (X * p) =
      (1 + X) * weightedDecoTransform w p +
        X * weightedDecoCompanionTransform w p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simp only [mul_add, weightedDecoTransform_add,
        weightedDecoCompanionTransform_add, hp, hq]
      ring
  | monomial n a =>
      rw [Polynomial.X_mul_monomial]
      simp only [weightedDecoTransform, Polynomial.basisTransform_monomial,
        weightedDecoCompanionTransform]
      rw [weightedDecoEulerian_succ_companion]
      ring

/-- Multiplication by `X` removes one unit of weighted lag. -/
theorem weightedDecoLagTransform_X_mul (w : ℝ) (p : ℝ[X]) :
    weightedDecoLagTransform w (X * p) = weightedDecoTransform w p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simp only [mul_add, weightedDecoLagTransform_add,
        weightedDecoTransform_add, hp, hq]
  | monomial n a =>
      rw [Polynomial.X_mul_monomial]
      simp [weightedDecoLagTransform, weightedDecoTransform,
        weightedDecoLagBasis]

/-- Inserting an affine input factor under the weighted transform. -/
theorem weightedDecoTransform_mul_X_add_C (w a : ℝ) (p : ℝ[X]) :
    weightedDecoTransform w ((X + C a) * p) =
      (1 + X + C a) * weightedDecoTransform w p +
        X * weightedDecoCompanionTransform w p := by
  rw [add_mul, weightedDecoTransform_add, weightedDecoTransform_X_mul,
    weightedDecoTransform_C_mul]
  ring

/-- Inserting an affine input factor under the weighted lag transform. -/
theorem weightedDecoLagTransform_mul_X_add_C (w a : ℝ) (p : ℝ[X]) :
    weightedDecoLagTransform w ((X + C a) * p) =
      weightedDecoTransform w p + C a * weightedDecoLagTransform w p := by
  rw [add_mul, weightedDecoLagTransform_add,
    weightedDecoLagTransform_X_mul, weightedDecoLagTransform_C_mul]

/-- The weighted image of the repeated-root input `(X + a) ^ n`. -/
def weightedDecoDiagonal (w : ℝ) (n : ℕ) (a : ℝ) : ℝ[X] :=
  weightedDecoTransform w ((X + C a) ^ n)

/-- The weighted lag companion of `(X + a) ^ n`. -/
def weightedDecoDiagonalLag (w : ℝ) (n : ℕ) (a : ℝ) : ℝ[X] :=
  weightedDecoLagTransform w ((X + C a) ^ n)

/-- The weighted residue companion of `(X + a) ^ n`. -/
def weightedDecoDiagonalCompanion (w : ℝ) (n : ℕ) (a : ℝ) : ℝ[X] :=
  weightedDecoCompanionTransform w ((X + C a) ^ n)

@[simp]
theorem weightedDecoDiagonal_zero (w a : ℝ) :
    weightedDecoDiagonal w 0 a = 1 := by
  simpa [weightedDecoDiagonal] using weightedDecoTransform_X_pow w 0

@[simp]
theorem weightedDecoDiagonal_one (w a : ℝ) :
    weightedDecoDiagonal w 1 a = X + C (1 + a) := by
  rw [weightedDecoDiagonal, pow_one, weightedDecoTransform_add]
  rw [show X = X ^ 1 by simp, weightedDecoTransform_X_pow]
  simp [weightedDecoEulerian]
  ring

@[simp]
theorem weightedDecoDiagonalLag_one (w a : ℝ) :
    weightedDecoDiagonalLag w 1 a = 1 := by
  rw [weightedDecoDiagonalLag, pow_one, weightedDecoLagTransform_add]
  rw [show X = X ^ 1 by simp, weightedDecoLagTransform_X_pow]
  simp [weightedDecoLagBasis]

@[simp]
theorem weightedDecoDiagonalCompanion_one (w a : ℝ) :
    weightedDecoDiagonalCompanion w 1 a = C (2 + w) := by
  rw [weightedDecoDiagonalCompanion, pow_one,
    weightedDecoCompanionTransform_add]
  rw [show X = X ^ 1 by simp, weightedDecoCompanionTransform_X_pow]
  rw [weightedDecoCompanionTransform_C, add_zero]
  simp only [weightedDecoCompanionBasis, weightedDecoEulerian_one,
    weightedDecoLagBasis, weightedDecoEulerian_zero, derivative_one,
    derivative_X, zero_add, mul_one, Nat.cast_one, map_one, map_add, map_ofNat]
  ring

/-- The weighted diagonal transform recurrence. -/
theorem weightedDecoDiagonal_succ (w : ℝ) (n : ℕ) (a : ℝ) :
    weightedDecoDiagonal w (n + 1) a =
      (1 + X + C a) * weightedDecoDiagonal w n a +
        X * weightedDecoDiagonalCompanion w n a := by
  rw [weightedDecoDiagonal, pow_succ']
  exact weightedDecoTransform_mul_X_add_C w a ((X + C a) ^ n)

/-- The weighted diagonal lag recurrence. -/
theorem weightedDecoDiagonalLag_succ (w : ℝ) (n : ℕ) (a : ℝ) :
    weightedDecoDiagonalLag w (n + 1) a =
      weightedDecoDiagonal w n a + C a * weightedDecoDiagonalLag w n a := by
  rw [weightedDecoDiagonalLag, pow_succ']
  exact weightedDecoLagTransform_mul_X_add_C w a ((X + C a) ^ n)

/-- The positive-rank weighted diagonal companion formula. -/
theorem weightedDecoDiagonalCompanion_succ_eq (w : ℝ) (n : ℕ) (a : ℝ) :
    weightedDecoDiagonalCompanion w (n + 1) a =
      (1 - X) * (weightedDecoDiagonal w (n + 1) a).derivative +
        C ((n : ℝ) + 1) * weightedDecoDiagonal w (n + 1) a -
          C (((n : ℝ) + 1) * a) * weightedDecoDiagonal w n a +
            C w * weightedDecoDiagonalLag w (n + 1) a := by
  rw [weightedDecoDiagonalCompanion, weightedDecoCompanionTransform_eq]
  rw [Polynomial.derivative_pow]
  simp only [Nat.cast_add, Nat.cast_one, Nat.succ_sub_one, derivative_add,
    derivative_X, derivative_C, add_zero, mul_one]
  have hinput :
      X * (C ((n : ℝ) + 1) * (X + C a) ^ n) =
        C ((n : ℝ) + 1) * (X + C a) ^ (n + 1) -
          C (((n : ℝ) + 1) * a) * (X + C a) ^ n := by
    rw [pow_succ']
    simp only [map_add, map_one, map_mul]
    ring
  rw [hinput]
  simp only [sub_eq_add_neg, weightedDecoTransform_add,
    weightedDecoTransform_C_mul, weightedDecoTransform_neg,
    weightedDecoDiagonal, weightedDecoDiagonalLag]
  ring

end RealRooted.Applications.OEIS
