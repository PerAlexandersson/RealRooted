import RealRooted.Mathlib.Algebra.Polynomial.BasisTransform

/-!
# The reverse-Hermite basis transform

This module defines the reverse-Hermite polynomials with positive recurrence
and the coefficientwise transform that sends `X ^ n` to the `n`th basis
polynomial. These are distinct from Mathlib's probabilists' Hermite
polynomials, whose recurrence has a negative derivative term.
-/

open Polynomial

noncomputable section

namespace RealRooted

universe u

variable {R : Type u}

section Semiring

variable [Semiring R]

/-- The reverse-Hermite basis with recurrence
`B_(n+2) = X * (B_(n+1) + (n+1) * B_n)`. -/
def reverseHermiteBasis : ℕ → R[X]
  | 0 => 1
  | 1 => X
  | n + 2 =>
      X * (reverseHermiteBasis (n + 1) +
        C ((n : R) + 1) * reverseHermiteBasis n)

@[simp] theorem reverseHermiteBasis_zero :
    reverseHermiteBasis (R := R) 0 = 1 := rfl

@[simp] theorem reverseHermiteBasis_one :
    reverseHermiteBasis (R := R) 1 = X := rfl

@[simp] theorem reverseHermiteBasis_succ_succ (n : ℕ) :
    reverseHermiteBasis (R := R) (n + 2) =
      X * (reverseHermiteBasis (n + 1) +
        C ((n : R) + 1) * reverseHermiteBasis n) := rfl

/-- The linear transform sending `X ^ n` to `reverseHermiteBasis n`. -/
def reverseHermiteTransform (p : R[X]) : R[X] :=
  basisTransform reverseHermiteBasis p

@[simp] theorem reverseHermiteTransform_zero :
    reverseHermiteTransform (0 : R[X]) = 0 := by
  simp [reverseHermiteTransform]

theorem reverseHermiteTransform_add (p q : R[X]) :
    reverseHermiteTransform (p + q) =
      reverseHermiteTransform p + reverseHermiteTransform q := by
  exact basisTransform_add reverseHermiteBasis p q

theorem reverseHermiteTransform_smul (a : R) (p : R[X]) :
    reverseHermiteTransform (a • p) =
      C a * reverseHermiteTransform p := by
  exact basisTransform_smul reverseHermiteBasis a p

theorem reverseHermiteTransform_C_mul (a : R) (p : R[X]) :
    reverseHermiteTransform (C a * p) =
      C a * reverseHermiteTransform p := by
  rw [show C a * p = a • p by rw [Polynomial.smul_eq_C_mul],
    reverseHermiteTransform, basisTransform_smul]
  change C a * basisTransform reverseHermiteBasis p =
    C a * basisTransform reverseHermiteBasis p
  rfl

@[simp] theorem reverseHermiteTransform_C (a : R) :
    reverseHermiteTransform (C a) = C a := by
  rw [reverseHermiteTransform, basisTransform_C]
  simp only [reverseHermiteBasis_zero, mul_one]

@[simp] theorem reverseHermiteTransform_X_pow (n : ℕ) :
    reverseHermiteTransform (X ^ n : R[X]) = reverseHermiteBasis n := by
  exact basisTransform_X_pow reverseHermiteBasis n

@[simp] theorem reverseHermiteTransform_monomial (n : ℕ) (a : R) :
    reverseHermiteTransform (monomial n a) =
      C a * reverseHermiteBasis n := by
  exact basisTransform_monomial reverseHermiteBasis n a

@[simp] theorem reverseHermiteTransform_one :
    reverseHermiteTransform (1 : R[X]) = 1 := by
  simpa using reverseHermiteTransform_C (R := R) 1

@[simp] theorem reverseHermiteTransform_X :
    reverseHermiteTransform (X : R[X]) = X := by
  rw [show (X : R[X]) = X ^ 1 by simp,
    reverseHermiteTransform_X_pow]
  simp only [reverseHermiteBasis_one, pow_one]

end Semiring

section CommSemiring

variable [CommSemiring R]

/-- Multiplication by `X` before the reverse-Hermite transform becomes the
corresponding first-order input-derivative step afterwards. -/
theorem reverseHermiteTransform_X_mul (p : R[X]) :
    reverseHermiteTransform (X * p) =
      X * (reverseHermiteTransform p +
        reverseHermiteTransform p.derivative) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [mul_add, reverseHermiteTransform_add,
        reverseHermiteTransform_add, derivative_add,
        reverseHermiteTransform_add, hp, hq]
      ring
  | monomial n a =>
      rw [← C_mul_X_pow_eq_monomial]
      rw [show X * (C a * X ^ n) = C a * X ^ (n + 1) by ring,
        reverseHermiteTransform_C_mul,
        reverseHermiteTransform_X_pow,
        reverseHermiteTransform_C_mul,
        reverseHermiteTransform_X_pow]
      cases n with
      | zero =>
          simp
      | succ n =>
          have hder :
              (C a * X ^ (n + 1)).derivative =
                C (a * ((n : R) + 1)) * X ^ n := by
            simp only [derivative_mul, derivative_C, zero_mul, zero_add,
              derivative_pow, derivative_X]
            push_cast
            simp only [map_add, map_one, map_mul]
            ring
          rw [hder, reverseHermiteTransform_C_mul,
            reverseHermiteTransform_X_pow]
          simp only [reverseHermiteBasis_succ_succ]
          simp only [map_add, map_one, map_mul]
          ring

/-- The affine-factor form of `reverseHermiteTransform_X_mul`. -/
theorem reverseHermiteTransform_mul_X_add_C (r : R) (p : R[X]) :
    reverseHermiteTransform ((X + C r) * p) =
      (X + C r) * reverseHermiteTransform p +
        X * reverseHermiteTransform p.derivative := by
  rw [add_mul, reverseHermiteTransform_add,
    reverseHermiteTransform_X_mul, reverseHermiteTransform_C_mul]
  ring

end CommSemiring

end RealRooted
