module

import RealRooted.CombinatorialExamples.Touchard
import RealRooted.DegreeDropReversal
import RealRooted.Interlacing.WindowInduction
import RealRooted.ObreschkoffConverse.Derivative
import RealRooted.Recurrence.RowModel
import RealRooted.Recurrence.Uniqueness
public import RealRooted.EulerOperator
public import RealRooted.Touchard
import RealRooted.WagnerX.ListInterlacing
import RealRooted.Mathlib.Analysis.Calculus.LocalExtr.Polynomial

@[expose] public section

open Polynomial

noncomputable section

namespace RealRooted

/-- The derivative image of the positive-index Touchard rows. -/
def touchardDerivativeRow (n : ℕ) : ℝ[X] :=
  (touchard (n + 1)).derivative

@[simp] theorem touchardDerivativeRow_zero :
    touchardDerivativeRow 0 = 1 := by
  simp only [touchardDerivativeRow, Nat.zero_add, touchard_one, derivative_X]

@[simp] theorem touchardDerivativeRow_one :
    touchardDerivativeRow 1 = 1 + 2 * X := by
  norm_num [touchardDerivativeRow, touchard, derivative_add, derivative_mul]
  ring

/-- The derivative Touchard rows satisfy an order-two recurrence with derivatives of both
preceding rows. -/
theorem touchardDerivativeRow_add_two (n : ℕ) :
    touchardDerivativeRow (n + 2) =
      X * (touchardDerivativeRow (n + 1)).derivative +
        (1 + 2 * X) * touchardDerivativeRow (n + 1) -
        X ^ 2 * (touchardDerivativeRow n).derivative -
        X ^ 2 * touchardDerivativeRow n := by
  simp only [touchardDerivativeRow]
  rw [touchard_succ (n + 2), touchard_succ (n + 1)]
  simp only [derivative_add, derivative_mul, derivative_X, one_mul]
  ring

/-- The derivative Touchard rows split over the reals. -/
theorem touchardDerivativeRow_splits (n : ℕ) :
    (touchardDerivativeRow n).Splits := by
  exact (isRealRooted_touchard (n + 1)).2.derivative

/-- Consecutive derivative Touchard rows strictly interlace. -/
theorem touchardDerivativeRow_strictInterl_succ (n : ℕ) :
    StrictInterl (touchardDerivativeRow n) (touchardDerivativeRow (n + 1)) := by
  apply derivative_strictInterl_of_strictInterl_succDegree
    (strictInterl_touchard_succ (n + 1))
  · rw [natDegree_touchard, natDegree_touchard]
  · rw [natDegree_touchard]
    lia

/-- Consecutive derivative Touchard rows interlace. -/
theorem touchardDerivativeRow_interlaces (n : ℕ) :
    Interlaces (touchardDerivativeRow n) (touchardDerivativeRow (n + 1)) := by
  apply (touchardDerivativeRow_strictInterl_succ n).toInterlaces
  simp only [touchardDerivativeRow, natDegree_derivative, natDegree_touchard]
  lia

/-- A sequence with the derivative-Touchard initial rows and recurrence has interlacing
consecutive rows. -/
@[rr_row_model]
theorem interlaces_of_touchardDerivativeRow_recurrence
    {P : ℕ → ℝ[X]}
    (hzero : P 0 = 1)
    (hone : P 1 = 1 + 2 * X)
    (hrec : ∀ n : ℕ, P (n + 2) =
      X * (P (n + 1)).derivative + (1 + 2 * X) * P (n + 1) -
        X ^ 2 * (P n).derivative - X ^ 2 * P n)
    (n : ℕ) :
    Interlaces (P n) (P (n + 1)) := by
  let nextRow : ℕ → ℝ[X] → ℝ[X] → ℝ[X] := fun _ f g ↦
    X * f.derivative + (1 + 2 * X) * f - X ^ 2 * g.derivative - X ^ 2 * g
  have heq := sequence_eq_of_same_lag_two_recurrence nextRow
    (hzero.trans touchardDerivativeRow_zero.symm)
    (hone.trans touchardDerivativeRow_one.symm)
    hrec touchardDerivativeRow_add_two
  rw [heq n, heq (n + 1)]
  exact touchardDerivativeRow_interlaces n

/-- The quotient by `X` of the Euler image of a positive-index Touchard row. -/
def touchardEulerQuotientRow (n : ℕ) : ℝ[X] :=
  (thetaPlusOne (touchard (n + 1))).divX

private theorem coeff_zero_thetaPlusOne_touchard_succ (n : ℕ) :
    (thetaPlusOne (touchard (n + 1))).coeff 0 = 0 := by
  rw [coeff_thetaPlusOne, coeff_touchard_eq_stirlingSecond]
  simp

/-- Multiplication by `X` recovers the Euler image of the Touchard row. -/
theorem X_mul_touchardEulerQuotientRow (n : ℕ) :
    X * touchardEulerQuotientRow n = thetaPlusOne (touchard (n + 1)) := by
  rw [touchardEulerQuotientRow]
  simpa only [coeff_zero_thetaPlusOne_touchard_succ, map_zero, add_zero] using
    Polynomial.X_mul_divX_add (thetaPlusOne (touchard (n + 1)))

@[simp] theorem touchardEulerQuotientRow_zero :
    touchardEulerQuotientRow 0 = 2 := by
  apply mul_left_cancel₀ X_ne_zero
  rw [X_mul_touchardEulerQuotientRow]
  norm_num [touchard_one, thetaPlusOne, theta]
  ring

@[simp] theorem touchardEulerQuotientRow_one :
    touchardEulerQuotientRow 1 = 2 + 3 * X := by
  apply mul_left_cancel₀ X_ne_zero
  rw [X_mul_touchardEulerQuotientRow]
  rw [touchard_two]
  norm_num [thetaPlusOne, theta, derivative_add, derivative_pow]
  simp only [map_ofNat]
  ring

/-- The Euler-quotient Touchard rows satisfy an order-two recurrence with derivatives of
both preceding rows. -/
theorem touchardEulerQuotientRow_add_two (n : ℕ) :
    touchardEulerQuotientRow (n + 2) =
      2 * X * touchardEulerQuotientRow (n + 1) +
        X * (touchardEulerQuotientRow (n + 1)).derivative +
        X * (1 - X) * (touchardEulerQuotientRow n).derivative +
        (1 + X - X ^ 2) * touchardEulerQuotientRow n := by
  apply mul_left_cancel₀ X_ne_zero
  calc
    X * touchardEulerQuotientRow (n + 2) =
        thetaPlusOne (touchard (n + 3)) := by
      rw [X_mul_touchardEulerQuotientRow]
    _ = (2 * X - 1) * thetaPlusOne (touchard (n + 2)) +
          X * (thetaPlusOne (touchard (n + 2))).derivative +
          X * (1 - X) * (thetaPlusOne (touchard (n + 1))).derivative +
          (2 * X - X ^ 2) * thetaPlusOne (touchard (n + 1)) := by
      simp only [thetaPlusOne, theta, touchard_succ, derivative_add,
        derivative_mul, derivative_X, one_mul]
      ring
    _ = X * (2 * X * touchardEulerQuotientRow (n + 1) +
          X * (touchardEulerQuotientRow (n + 1)).derivative +
          X * (1 - X) * (touchardEulerQuotientRow n).derivative +
          (1 + X - X ^ 2) * touchardEulerQuotientRow n) := by
      rw [← X_mul_touchardEulerQuotientRow (n + 1),
        ← X_mul_touchardEulerQuotientRow n]
      simp only [derivative_mul, derivative_X, one_mul]
      ring

/-- The Euler-quotient Touchard rows split over the reals. -/
theorem touchardEulerQuotientRow_splits (n : ℕ) :
    (touchardEulerQuotientRow n).Splits := by
  rw [← DegreeDropReversal.splits_X_mul_iff]
  rw [X_mul_touchardEulerQuotientRow]
  have hpf := thetaPlusOne_preserves_pf
    (IsPFPolynomial.of_realRooted_nonneg
      (touchard_nonnegCoeffs (n + 1)) (isRealRooted_touchard (n + 1)).2)
  exact (hpf.ne_zero_and_splits
    (thetaPlusOne_ne_zero_of_ne_zero (touchard_ne_zero (n + 1)))).2

/-- Consecutive Euler-quotient Touchard rows strictly interlace. -/
theorem touchardEulerQuotientRow_strictInterl_succ (n : ℕ) :
    StrictInterl (touchardEulerQuotientRow n)
      (touchardEulerQuotientRow (n + 1)) := by
  have hstrict := (strictInterl_touchard_succ (n + 1)).thetaPlusOne
  rw [← X_mul_touchardEulerQuotientRow,
    ← X_mul_touchardEulerQuotientRow] at hstrict
  exact StrictInterl.of_mul_X_sub_C_both (r := 0) (by simpa using hstrict)

/-- Consecutive Euler-quotient Touchard rows interlace. -/
theorem touchardEulerQuotientRow_interlaces (n : ℕ) :
    Interlaces (touchardEulerQuotientRow n)
      (touchardEulerQuotientRow (n + 1)) := by
  have hstrict := touchardEulerQuotientRow_strictInterl_succ n
  apply hstrict.toInterlaces
  have hleft := hstrict.1.1
  have hright := hstrict.2.1.1
  have hdegree :
      (X * touchardEulerQuotientRow n).natDegree + 1 =
        (X * touchardEulerQuotientRow (n + 1)).natDegree := by
    rw [X_mul_touchardEulerQuotientRow, X_mul_touchardEulerQuotientRow,
      natDegree_thetaPlusOne_of_ne_zero (touchard_ne_zero (n + 1)),
      natDegree_thetaPlusOne_of_ne_zero (touchard_ne_zero (n + 2)),
      natDegree_touchard, natDegree_touchard]
  rw [natDegree_mul X_ne_zero hleft, natDegree_mul X_ne_zero hright,
    natDegree_X] at hdegree
  lia

/-- A sequence with the Euler-quotient Touchard initial rows and recurrence has interlacing
consecutive rows. -/
@[rr_row_model]
theorem interlaces_of_touchardEulerQuotientRow_recurrence
    {P : ℕ → ℝ[X]}
    (hzero : P 0 = 2)
    (hone : P 1 = 2 + 3 * X)
    (hrec : ∀ n : ℕ, P (n + 2) =
      2 * X * P (n + 1) + X * (P (n + 1)).derivative +
        X * (1 - X) * (P n).derivative + (1 + X - X ^ 2) * P n)
    (n : ℕ) :
    Interlaces (P n) (P (n + 1)) := by
  let nextRow : ℕ → ℝ[X] → ℝ[X] → ℝ[X] := fun _ f g ↦
    2 * X * f + X * f.derivative + X * (1 - X) * g.derivative +
      (1 + X - X ^ 2) * g
  have heq := sequence_eq_of_same_lag_two_recurrence nextRow
    (hzero.trans touchardEulerQuotientRow_zero.symm)
    (hone.trans touchardEulerQuotientRow_one.symm)
    hrec touchardEulerQuotientRow_add_two
  rw [heq n, heq (n + 1)]
  exact touchardEulerQuotientRow_interlaces n

end RealRooted
