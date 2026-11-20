module

public import RealRooted.TuranHurwitz.ScaledRecurrence
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Algebra of the fractional-linear normalization

The scale is `a(1-t q)` and the argument is
`(a+(b+a t)q)/(a(1-t q))`. We work in complex formal series and require
only that the scale has nonzero constant coefficient.
-/

public section

namespace RealRooted.TuranHurwitz

/-- The linear scale in the fractional-linear recurrence transport. -/
@[expose] noncomputable def linearScale (a t : ℂ) (q : PowerSeries ℂ) : PowerSeries ℂ :=
  PowerSeries.C a * (1 - PowerSeries.C t * q)

/-- The linear numerator of the normalized argument. -/
@[expose] noncomputable def linearNumerator (a b t : ℂ) (q : PowerSeries ℂ) :
    PowerSeries ℂ := PowerSeries.C a + PowerSeries.C (b + a * t) * q

/-- The fractional-linear normalized argument as a formal series. -/
@[expose] noncomputable def linearArgument (a b t : ℂ) (q : PowerSeries ℂ) :
    PowerSeries ℂ := linearNumerator a b t q * (linearScale a t q)⁻¹

/-- The derivative of the linear scale when the input has derivative one. -/
theorem derivative_linearScale (a t : ℂ) (q : PowerSeries ℂ)
    (hq : PowerSeries.derivative q = 1) :
    PowerSeries.derivative (linearScale a t q) = -PowerSeries.C (a * t) := by
  simp only [linearScale, PowerSeries.derivative.leibniz, PowerSeries.derivative_C,
    map_sub, PowerSeries.derivative_one, hq, smul_eq_mul, map_mul]
  ring

/-- The derivative of the linear numerator when the input has derivative one. -/
theorem derivative_linearNumerator (a b t : ℂ) (q : PowerSeries ℂ)
    (hq : PowerSeries.derivative q = 1) :
    PowerSeries.derivative (linearNumerator a b t q) = PowerSeries.C (b + a * t) := by
  simp only [linearNumerator, map_add, PowerSeries.derivative.leibniz,
    PowerSeries.derivative_C, hq, smul_eq_mul]
  ring

/-- The numerator-scale Wronskian is the constant determinant. -/
theorem linearNormalization_determinant (a b t : ℂ) (q : PowerSeries ℂ) :
    PowerSeries.C (b + a * t) * linearScale a t q +
      linearNumerator a b t q * PowerSeries.C (a * t) =
        PowerSeries.C (a * (b + 2 * a * t)) := by
  simp only [linearScale, linearNumerator, map_mul, map_add, map_ofNat]
  ring

/-- The formal derivative of the fractional-linear normalized argument. -/
theorem derivative_linearArgument (a b t : ℂ) (q : PowerSeries ℂ)
    (hq : PowerSeries.derivative q = 1)
    (hF : PowerSeries.constantCoeff (linearScale a t q) ≠ 0) :
    PowerSeries.derivative (linearArgument a b t q) =
      PowerSeries.C (a * (b + 2 * a * t)) * (linearScale a t q)⁻¹ ^ 2 := by
  have hcancel := PowerSeries.mul_inv_cancel (linearScale a t q) hF
  have hdet := linearNormalization_determinant a b t q
  rw [linearArgument, PowerSeries.derivative.leibniz, derivative_linearNumerator _ _ _ _ hq,
    PowerSeries.derivative_inv', derivative_linearScale _ _ _ hq]
  simp only [smul_eq_mul]
  linear_combination
    -(PowerSeries.C (b + a * t) * (linearScale a t q)⁻¹) * hcancel +
    ((linearScale a t q)⁻¹ ^ 2) * hdet

/-- The numerator and scale squares differ by the original quadratic vector field. -/
theorem linearNormalization_quadratic (a b t : ℂ) (q : PowerSeries ℂ) :
    linearNumerator a b t q ^ 2 - linearScale a t q ^ 2 =
      q * PowerSeries.C (b + 2 * a * t) *
        (PowerSeries.C (2 * a) + PowerSeries.C b * q) := by
  simp only [linearNumerator, linearScale, map_add, map_mul, map_ofNat]
  ring

/-- The transformed argument satisfies the vector-field transport identity. -/
theorem linearNormalization_vectorField (a b t : ℂ) (q : PowerSeries ℂ)
    (hq : PowerSeries.derivative q = 1)
    (hF : PowerSeries.constantCoeff (linearScale a t q) ≠ 0) :
    linearScale a t q * (linearArgument a b t q ^ 2 - 1) =
      (q * (1 - PowerSeries.C t * q) *
        (PowerSeries.C (2 * a) + PowerSeries.C b * q)) *
          PowerSeries.derivative (linearArgument a b t q) := by
  have hcancel := PowerSeries.mul_inv_cancel (linearScale a t q) hF
  have hsquare : linearScale a t q ^ 2 * (linearScale a t q)⁻¹ ^ 2 = 1 := by
    rw [← mul_pow, hcancel, one_pow]
  calc
    _ = linearScale a t q *
        (linearNumerator a b t q ^ 2 - linearScale a t q ^ 2) *
          (linearScale a t q)⁻¹ ^ 2 := by
      simp only [linearArgument]
      linear_combination linearScale a t q * hsquare
    _ = _ := by
      rw [linearNormalization_quadratic, derivative_linearArgument _ _ _ _ hq hF]
      simp only [linearScale, map_mul]
      ring

/-- The row-index term cancels against differentiating the scale. -/
theorem linearNormalization_cancellation (a b t : ℂ) (q : PowerSeries ℂ)
    (hq : PowerSeries.derivative q = 1) :
    linearScale a t q *
        (PowerSeries.C t * q * (PowerSeries.C (2 * a) + PowerSeries.C b * q)) +
      (q * (1 - PowerSeries.C t * q) *
        (PowerSeries.C (2 * a) + PowerSeries.C b * q)) *
          PowerSeries.derivative (linearScale a t q) = 0 := by
  rw [derivative_linearScale _ _ _ hq]
  simp only [linearScale, map_mul]
  ring

/-- Two scalar coefficient identities give the affine part of the recurrence transport. -/
theorem linearNormalization_affine (a b t d h e B : ℂ) (q : PowerSeries ℂ)
    (hF : PowerSeries.constantCoeff (linearScale a t q) ≠ 0)
    (hzero : a * (d + h) = e)
    (hone : d * (b + a * t) - h * a * t = B) :
    linearScale a t q *
        (PowerSeries.C d * linearArgument a b t q + PowerSeries.C h) =
      PowerSeries.C e + PowerSeries.C B * q := by
  have hcancel := PowerSeries.mul_inv_cancel (linearScale a t q) hF
  have hz := congrArg (PowerSeries.C (R := ℂ)) hzero
  have ho := congrArg (PowerSeries.C (R := ℂ)) hone
  simp only [map_mul, map_add, map_sub] at hz ho
  have hcoef : PowerSeries.C d * linearNumerator a b t q +
      PowerSeries.C h * linearScale a t q = PowerSeries.C e + PowerSeries.C B * q := by
    simp only [linearNumerator, linearScale, map_add, map_mul]
    linear_combination hz + q * ho
  rw [linearArgument]
  linear_combination
    (PowerSeries.C d * linearNumerator a b t q) * hcancel + hcoef

end RealRooted.TuranHurwitz
