module

public import Mathlib.RingTheory.PowerSeries.Exp
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Algebra.Rat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Formal hyperbolic functions

We define sinh, cosh and tanh as formal power series over the reals.
Differential and unit identities require no analytic convergence.
-/

public section

namespace RealRooted.TuranHurwitz

/-- The hyperbolic sine series, defined from the exponential series. -/
@[expose] noncomputable def sinhSeries : PowerSeries ℝ :=
  PowerSeries.C (1 / 2 : ℝ) *
    (PowerSeries.exp ℝ - PowerSeries.rescale (-1) (PowerSeries.exp ℝ))

/-- The hyperbolic cosine series, defined from the exponential series. -/
@[expose] noncomputable def coshSeries : PowerSeries ℝ :=
  PowerSeries.C (1 / 2 : ℝ) *
    (PowerSeries.exp ℝ + PowerSeries.rescale (-1) (PowerSeries.exp ℝ))

/-- The formal hyperbolic tangent; the denominator has constant coefficient one. -/
@[expose] noncomputable def tanhSeries : PowerSeries ℝ := sinhSeries * coshSeries⁻¹

/-- The exponential at a scalar multiple of the formal variable satisfies its
differential equation. -/
theorem derivative_rescale_exp (a : ℝ) :
    PowerSeries.derivative (PowerSeries.rescale a (PowerSeries.exp ℝ)) =
      PowerSeries.C a * PowerSeries.rescale a (PowerSeries.exp ℝ) := by
  ext n
  rw [PowerSeries.coeff_derivative, PowerSeries.coeff_rescale, PowerSeries.coeff_exp,
    PowerSeries.coeff_C_mul, PowerSeries.coeff_rescale, PowerSeries.coeff_exp]
  have hfac : algebraMap ℚ ℝ (1 / ((n + 1).factorial : ℚ)) * (n + 1 : ℝ) =
      algebraMap ℚ ℝ (1 / (n.factorial : ℚ)) := by
    rw [show (n + 1 : ℝ) = algebraMap ℚ ℝ (n + 1 : ℚ) by simp, ← map_mul]
    congr 1
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    field_simp
  calc
    _ = a ^ n * a *
        (algebraMap ℚ ℝ (1 / ((n + 1).factorial : ℚ)) * (n + 1 : ℝ)) := by
          rw [pow_succ]
          ring
    _ = _ := by rw [hfac]; ring

/-- Rescaling the formal variable leaves the constant coefficient unchanged. -/
theorem constantCoeff_rescale (a : ℝ) (f : PowerSeries ℝ) :
    PowerSeries.constantCoeff (PowerSeries.rescale a f) = PowerSeries.constantCoeff f := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.coeff_rescale]
  simp

/-- The sinh series has zero constant coefficient. -/
@[simp] theorem constantCoeff_sinhSeries : PowerSeries.constantCoeff sinhSeries = 0 := by
  simp [sinhSeries, constantCoeff_rescale]

/-- The cosh series has constant coefficient one. -/
@[simp] theorem constantCoeff_coshSeries : PowerSeries.constantCoeff coshSeries = 1 := by
  norm_num [coshSeries, constantCoeff_rescale]

/-- The tanh series has zero constant coefficient, so formal substitution is permitted. -/
@[simp] theorem constantCoeff_tanhSeries : PowerSeries.constantCoeff tanhSeries = 0 := by
  simp [tanhSeries]

/-- Formal differentiation exchanges sinh and cosh. -/
theorem derivative_sinhSeries : PowerSeries.derivative sinhSeries = coshSeries := by
  simp only [sinhSeries, coshSeries, PowerSeries.derivative.leibniz,
    PowerSeries.derivative_C, map_sub, PowerSeries.derivative_exp, derivative_rescale_exp,
    map_neg, map_one]
  ring

/-- Formal differentiation exchanges cosh and sinh. -/
theorem derivative_coshSeries : PowerSeries.derivative coshSeries = sinhSeries := by
  simp only [sinhSeries, coshSeries, PowerSeries.derivative.leibniz,
    PowerSeries.derivative_C, map_add, PowerSeries.derivative_exp, derivative_rescale_exp,
    map_neg, map_one]
  ring

/-- The fundamental hyperbolic identity holds coefficientwise. -/
theorem coshSeries_sq_sub_sinhSeries_sq : coshSeries ^ 2 - sinhSeries ^ 2 = 1 := by
  have hpair : PowerSeries.exp ℝ * PowerSeries.rescale (-1) (PowerSeries.exp ℝ) = 1 := by
    simpa only [PowerSeries.evalNegHom] using PowerSeries.exp_mul_exp_neg_eq_one (A := ℝ)
  have hhalf : (PowerSeries.C (1 / 2 : ℝ) : PowerSeries ℝ) +
      PowerSeries.C (1 / 2 : ℝ) = 1 := by
    rw [← map_add]
    norm_num
  calc
    _ = (PowerSeries.C (1 / 2 : ℝ) + PowerSeries.C (1 / 2 : ℝ)) ^ 2 *
        (PowerSeries.exp ℝ * PowerSeries.rescale (-1) (PowerSeries.exp ℝ)) := by
          dsimp [sinhSeries, coshSeries]
          ring
    _ = 1 := by rw [hhalf, hpair]; ring

/-- The Riccati equation for tanh holds as a formal-series identity. -/
theorem derivative_tanhSeries : PowerSeries.derivative tanhSeries = 1 - tanhSeries ^ 2 := by
  rw [tanhSeries, PowerSeries.derivative.leibniz, derivative_sinhSeries,
    PowerSeries.derivative_inv', derivative_coshSeries]
  have hcancel := PowerSeries.mul_inv_cancel coshSeries (by simp)
  calc
    _ = coshSeries * coshSeries⁻¹ - tanhSeries ^ 2 := by dsimp [tanhSeries]; ring
    _ = _ := by rw [hcancel]; rfl

/-- The first formal derivative of the square of sinh. -/
theorem derivative_sinhSeries_sq :
    PowerSeries.derivative (sinhSeries ^ 2) = 2 * sinhSeries * coshSeries := by
  rw [pow_two, PowerSeries.derivative.leibniz, derivative_sinhSeries]
  ring

/-- The squared first derivative of `sinh²` satisfies a polynomial identity. -/
theorem derivative_sinhSeries_sq_sq :
    PowerSeries.derivative (sinhSeries ^ 2) ^ 2 =
      4 * sinhSeries ^ 2 * (1 + sinhSeries ^ 2) := by
  rw [derivative_sinhSeries_sq]
  have hc : coshSeries ^ 2 = 1 + sinhSeries ^ 2 := by
    linear_combination coshSeries_sq_sub_sinhSeries_sq
  calc
    _ = 4 * sinhSeries ^ 2 * coshSeries ^ 2 := by ring
    _ = _ := by rw [hc]

/-- The second formal derivative of `sinh²`; this is the input to EPDE. -/
theorem derivative_derivative_sinhSeries_sq :
    PowerSeries.derivative (PowerSeries.derivative (sinhSeries ^ 2)) =
      2 + 4 * sinhSeries ^ 2 := by
  rw [derivative_sinhSeries_sq, PowerSeries.derivative.leibniz,
    PowerSeries.derivative.leibniz, derivative_sinhSeries, derivative_coshSeries]
  rw [show PowerSeries.derivative (2 : PowerSeries ℝ) = 0 from
    PowerSeries.derivative.map_natCast 2]
  linear_combination 2 * coshSeries_sq_sub_sinhSeries_sq

end RealRooted.TuranHurwitz
