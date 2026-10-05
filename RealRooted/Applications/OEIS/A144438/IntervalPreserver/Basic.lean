import RealRooted.Applications.OEIS.A144438
import RealRooted.Mathlib.Algebra.Polynomial.BasisTransform

/-!
# The A144438 basis transform and its companion operators

This file defines the linear transform sending `X ^ n` to the `n`th deco
Eulerian polynomial.  It also defines the lag and residue companion transforms
used by the interval-preserver argument and proves their exact insertion and
diagonal recurrences.

Only polynomial identities are established here.  The residue-energy and
first-contact arguments belong to later modules.
-/

open Polynomial

noncomputable section

namespace RealRooted.Applications.OEIS

/-- The linear basis transform sending `X ^ n` to `decoEulerian n`. -/
def a144438Transform (p : ℝ[X]) : ℝ[X] :=
  Polynomial.basisTransform decoEulerian p

@[simp]
theorem a144438Transform_X_pow (n : ℕ) :
    a144438Transform (X ^ n) = decoEulerian n :=
  Polynomial.basisTransform_X_pow decoEulerian n

theorem a144438Transform_add (p q : ℝ[X]) :
    a144438Transform (p + q) = a144438Transform p + a144438Transform q :=
  Polynomial.basisTransform_add decoEulerian p q

theorem a144438Transform_C_mul (a : ℝ) (p : ℝ[X]) :
    a144438Transform (C a * p) = C a * a144438Transform p := by
  rw [show C a * p = a • p by rw [Polynomial.smul_eq_C_mul],
    a144438Transform, Polynomial.basisTransform_smul]
  rfl

theorem a144438Transform_neg (p : ℝ[X]) :
    a144438Transform (-p) = -a144438Transform p := by
  change Polynomial.basisTransform decoEulerian (-p) =
    -Polynomial.basisTransform decoEulerian p
  rw [show -p = (-1 : ℝ) • p by simp,
    Polynomial.basisTransform_smul]
  simp

@[simp]
theorem a144438Transform_C (a : ℝ) :
    a144438Transform (C a) = C a := by
  simp [a144438Transform, decoEulerian]

/-- The lag basis sends the constant monomial to zero and `X ^ (n + 1)` to
the `n`th deco Eulerian polynomial. -/
def a144438LagBasis : ℕ → ℝ[X]
  | 0 => 0
  | n + 1 => decoEulerian n

/-- The coefficientwise lag transform associated with `a144438Transform`. -/
def a144438LagTransform (p : ℝ[X]) : ℝ[X] :=
  Polynomial.basisTransform a144438LagBasis p

@[simp]
theorem a144438LagTransform_X_pow (n : ℕ) :
    a144438LagTransform (X ^ n) = a144438LagBasis n :=
  Polynomial.basisTransform_X_pow a144438LagBasis n

theorem a144438LagTransform_add (p q : ℝ[X]) :
    a144438LagTransform (p + q) =
      a144438LagTransform p + a144438LagTransform q :=
  Polynomial.basisTransform_add a144438LagBasis p q

theorem a144438LagTransform_C_mul (a : ℝ) (p : ℝ[X]) :
    a144438LagTransform (C a * p) = C a * a144438LagTransform p := by
  rw [show C a * p = a • p by rw [Polynomial.smul_eq_C_mul],
    a144438LagTransform, Polynomial.basisTransform_smul]
  rfl

@[simp]
theorem a144438LagTransform_C (a : ℝ) :
    a144438LagTransform (C a) = 0 := by
  simp [a144438LagTransform, a144438LagBasis]

/-- The companion basis at rank `n`. -/
def a144438CompanionBasis (n : ℕ) : ℝ[X] :=
  (1 - X) * (decoEulerian n).derivative +
    C (n : ℝ) * decoEulerian n + a144438LagBasis n

/-- The companion transform appearing in the A144438 insertion identity. -/
def a144438CompanionTransform (p : ℝ[X]) : ℝ[X] :=
  Polynomial.basisTransform a144438CompanionBasis p

@[simp]
theorem a144438CompanionTransform_X_pow (n : ℕ) :
    a144438CompanionTransform (X ^ n) = a144438CompanionBasis n :=
  Polynomial.basisTransform_X_pow a144438CompanionBasis n

theorem a144438CompanionTransform_add (p q : ℝ[X]) :
    a144438CompanionTransform (p + q) =
      a144438CompanionTransform p + a144438CompanionTransform q := by
  exact Polynomial.basisTransform_add a144438CompanionBasis p q

theorem a144438CompanionTransform_C_mul (a : ℝ) (p : ℝ[X]) :
    a144438CompanionTransform (C a * p) =
      C a * a144438CompanionTransform p := by
  rw [show C a * p = a • p by rw [Polynomial.smul_eq_C_mul],
    a144438CompanionTransform, Polynomial.basisTransform_smul]
  rfl

@[simp]
theorem a144438CompanionTransform_C (a : ℝ) :
    a144438CompanionTransform (C a) = 0 := by
  simp [a144438CompanionTransform, a144438CompanionBasis,
    a144438LagBasis, decoEulerian]

/-- The companion transform in derivative-and-lag form. -/
theorem a144438CompanionTransform_eq (p : ℝ[X]) :
    a144438CompanionTransform p =
      (1 - X) * (a144438Transform p).derivative +
        a144438Transform (X * p.derivative) + a144438LagTransform p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simp only [a144438CompanionTransform_add, derivative_add, mul_add,
        a144438Transform_add, a144438LagTransform_add, hp, hq]
      ring
  | monomial n a =>
      simp only [a144438CompanionTransform,
        Polynomial.basisTransform_monomial, a144438CompanionBasis,
        a144438Transform, a144438LagTransform,
        derivative_mul, derivative_C, zero_mul, zero_add,
        Polynomial.derivative_monomial]
      cases n with
      | zero => simp [a144438LagBasis]
      | succ n =>
          simp only [Nat.cast_add, Nat.cast_one, Nat.succ_sub_one,
            Polynomial.X_mul_monomial,
            Polynomial.basisTransform_monomial, a144438LagBasis]
          simp only [map_add, map_one, map_mul]
          ring

/-- The deco Eulerian recurrence in the one-step form used by the basis
transform. -/
theorem decoEulerian_succ_companion (n : ℕ) :
    decoEulerian (n + 1) =
      (1 + X) * decoEulerian n + X * (C (n : ℝ) * decoEulerian n) +
        X * (1 - X) * (decoEulerian n).derivative +
          X * a144438LagBasis n := by
  cases n with
  | zero => simp [decoEulerian, a144438LagBasis]
  | succ n =>
      rw [decoEulerian_recurrence]
      push_cast
      simp only [a144438LagBasis, map_add, map_one]
      rw [show C (2 : ℝ) = 2 by norm_num [map_ofNat]]
      ring

/-- Multiplication by `X` under the A144438 transform. -/
theorem a144438Transform_X_mul (p : ℝ[X]) :
    a144438Transform (X * p) =
      (1 + X) * a144438Transform p +
        X * a144438CompanionTransform p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simp only [mul_add, a144438Transform_add,
        a144438CompanionTransform_add, hp, hq]
      ring
  | monomial n a =>
      rw [Polynomial.X_mul_monomial]
      simp only [a144438Transform, Polynomial.basisTransform_monomial,
        a144438CompanionTransform, a144438CompanionBasis]
      rw [decoEulerian_succ_companion]
      ring

/-- Multiplication by `X` under the lag transform removes one unit of lag. -/
theorem a144438LagTransform_X_mul (p : ℝ[X]) :
    a144438LagTransform (X * p) = a144438Transform p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simp only [mul_add, a144438LagTransform_add,
        a144438Transform_add, hp, hq]
  | monomial n a =>
      rw [Polynomial.X_mul_monomial]
      simp [a144438LagTransform, a144438Transform, a144438LagBasis]

/-- Inserting an affine factor in the input gives the fundamental A144438
transform identity. -/
theorem a144438Transform_mul_X_add_C (a : ℝ) (p : ℝ[X]) :
    a144438Transform ((X + C a) * p) =
      (1 + X + C a) * a144438Transform p +
        X * a144438CompanionTransform p := by
  rw [add_mul, a144438Transform_add, a144438Transform_X_mul,
    a144438Transform_C_mul]
  ring

/-- Inserting an affine factor in the input gives the lag recurrence. -/
theorem a144438LagTransform_mul_X_add_C (a : ℝ) (p : ℝ[X]) :
    a144438LagTransform ((X + C a) * p) =
      a144438Transform p + C a * a144438LagTransform p := by
  rw [add_mul, a144438LagTransform_add, a144438LagTransform_X_mul,
    a144438LagTransform_C_mul]

/-- The image of the repeated-root input `(X + a) ^ n`. -/
def a144438Diagonal (n : ℕ) (a : ℝ) : ℝ[X] :=
  a144438Transform ((X + C a) ^ n)

/-- The lag companion of the repeated-root input `(X + a) ^ n`. -/
def a144438DiagonalLag (n : ℕ) (a : ℝ) : ℝ[X] :=
  a144438LagTransform ((X + C a) ^ n)

/-- The residue companion of the repeated-root input `(X + a) ^ n`. -/
def a144438DiagonalCompanion (n : ℕ) (a : ℝ) : ℝ[X] :=
  a144438CompanionTransform ((X + C a) ^ n)

@[simp]
theorem a144438Diagonal_zero (a : ℝ) : a144438Diagonal 0 a = 1 := by
  simpa [a144438Diagonal] using a144438Transform_X_pow 0

@[simp]
theorem a144438Diagonal_one (a : ℝ) :
    a144438Diagonal 1 a = X + C (1 + a) := by
  rw [a144438Diagonal, pow_one, a144438Transform_add]
  rw [show X = X ^ 1 by simp, a144438Transform_X_pow]
  simp [decoEulerian]
  ring

@[simp]
theorem a144438DiagonalLag_one (a : ℝ) :
    a144438DiagonalLag 1 a = 1 := by
  rw [a144438DiagonalLag, pow_one, a144438LagTransform_add]
  rw [show X = X ^ 1 by simp, a144438LagTransform_X_pow]
  simp [a144438LagBasis]

@[simp]
theorem a144438DiagonalCompanion_one (a : ℝ) :
    a144438DiagonalCompanion 1 a = 3 := by
  rw [a144438DiagonalCompanion, pow_one,
    a144438CompanionTransform_add]
  rw [show X = X ^ 1 by simp, a144438CompanionTransform_X_pow]
  simp [a144438CompanionBasis, a144438LagBasis, decoEulerian]
  norm_num

/-- The diagonal transform recurrence. -/
theorem a144438Diagonal_succ (n : ℕ) (a : ℝ) :
    a144438Diagonal (n + 1) a =
      (1 + X + C a) * a144438Diagonal n a +
        X * a144438DiagonalCompanion n a := by
  rw [a144438Diagonal, pow_succ']
  exact a144438Transform_mul_X_add_C a ((X + C a) ^ n)

/-- The diagonal lag recurrence. -/
theorem a144438DiagonalLag_succ (n : ℕ) (a : ℝ) :
    a144438DiagonalLag (n + 1) a =
      a144438Diagonal n a + C a * a144438DiagonalLag n a := by
  rw [a144438DiagonalLag, pow_succ']
  exact a144438LagTransform_mul_X_add_C a ((X + C a) ^ n)

/-- The positive-rank diagonal companion written in terms of the diagonal
transform and its lag. -/
theorem a144438DiagonalCompanion_succ_eq (n : ℕ) (a : ℝ) :
    a144438DiagonalCompanion (n + 1) a =
      (1 - X) * (a144438Diagonal (n + 1) a).derivative +
        C ((n : ℝ) + 1) * a144438Diagonal (n + 1) a -
          C (((n : ℝ) + 1) * a) * a144438Diagonal n a +
            a144438DiagonalLag (n + 1) a := by
  rw [a144438DiagonalCompanion, a144438CompanionTransform_eq]
  rw [Polynomial.derivative_pow]
  simp only [Nat.cast_add, Nat.cast_one, Nat.succ_sub_one,
    derivative_add, derivative_X, derivative_C, add_zero, mul_one]
  have hinput :
      X * (C ((n : ℝ) + 1) * (X + C a) ^ n) =
        C ((n : ℝ) + 1) * (X + C a) ^ (n + 1) -
          C (((n : ℝ) + 1) * a) * (X + C a) ^ n := by
    rw [pow_succ']
    simp only [map_add, map_one, map_mul]
    ring
  rw [hinput]
  simp only [sub_eq_add_neg, a144438Transform_add,
    a144438Transform_C_mul, a144438Transform_neg, a144438Diagonal,
    a144438DiagonalLag]
  ring

end RealRooted.Applications.OEIS
