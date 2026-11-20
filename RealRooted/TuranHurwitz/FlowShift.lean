module

public import RealRooted.TuranHurwitz.FormalFlow
public import RealRooted.TuranHurwitz.NormalizedRecurrence
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# The formal shift identity

The flow and weight differential equations convert the polynomial recurrence
into differentiation of a formal series. Its coefficients give the shifted
exponential generating series at every complex parameter.
-/

public section

open Polynomial

namespace RealRooted.TuranHurwitz

/-- The weighted normalized row evaluated along the formal tanh flow. -/
@[expose] noncomputable def flowRow (d h : ℝ) (u : ℂ) (m : ℕ) : PowerSeries ℂ :=
  flowWeight d h u * Polynomial.aeval (formalFlow u) (normalized d h m)

/-- Formal differentiation in a real polynomial evaluated at a complex formal series. -/
theorem derivative_aeval_series (p : ℝ[X]) (g : PowerSeries ℂ) :
    PowerSeries.derivative (Polynomial.aeval g p) =
      Polynomial.aeval g p.derivative * PowerSeries.derivative g := by
  have h := Derivation.comp_aeval_eq (a := g)
    ((PowerSeries.derivative (R := ℂ)).restrictScalars ℝ) p
  simpa only [Derivation.restrictScalars_apply, smul_eq_mul] using h

/-- The constant coefficient of polynomial evaluation is evaluation at the constant coefficient. -/
theorem constantCoeff_aeval_series (p : ℝ[X]) (g : PowerSeries ℂ) :
    PowerSeries.constantCoeff (Polynomial.aeval g p) =
      Polynomial.aeval (PowerSeries.constantCoeff g) p := by
  rw [Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.hom_eval₂]
  congr 1

/-- Differentiation shifts the row index by one. -/
theorem derivative_flowRow (d h : ℝ) (u : ℂ) (m : ℕ) :
    PowerSeries.derivative (flowRow d h u m) = flowRow d h u (m + 1) := by
  rw [flowRow, PowerSeries.derivative.leibniz, derivative_flowWeight,
    derivative_aeval_series, derivative_formalFlow, flowRow, normalized_succ]
  simp only [map_add, map_mul, map_sub, map_pow, map_one, Polynomial.aeval_X,
    Polynomial.aeval_C, PowerSeries.algebraMap_apply, smul_eq_mul]
  have hd : algebraMap ℝ ℂ d = (d : ℂ) := rfl
  have hh : algebraMap ℝ ℂ h = (h : ℂ) := rfl
  rw [hd, hh]
  ring

/-- The weighted row starts at the normalized polynomial's value at `u`. -/
@[simp] theorem constantCoeff_flowRow (d h : ℝ) (u : ℂ) (m : ℕ) :
    PowerSeries.constantCoeff (flowRow d h u m) = Polynomial.aeval u (normalized d h m) := by
  rw [flowRow, map_mul, constantCoeff_flowWeight, one_mul,
    constantCoeff_aeval_series, constantCoeff_formalFlow]

/-- The formal flow identity with factorial normalization, valid at every index. -/
theorem factorial_mul_coeff_flowRow (d h : ℝ) (u : ℂ) (m k : ℕ) :
    (k.factorial : ℂ) * PowerSeries.coeff k (flowRow d h u m) =
      Polynomial.aeval u (normalized d h (m + k)) := by
  induction k generalizing m with
  | zero => simp [PowerSeries.coeff_zero_eq_constantCoeff]
  | succ k ih =>
      have hstep := congrArg (PowerSeries.coeff k) (derivative_flowRow d h u m)
      rw [PowerSeries.coeff_derivative] at hstep
      have hi := ih (m + 1)
      rw [show m + 1 + k = m + (k + 1) by lia] at hi
      rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      linear_combination (k.factorial : ℂ) * hstep + hi

/-- The exact coefficient formula for the shifted exponential generating series. -/
theorem coeff_flowRow (d h : ℝ) (u : ℂ) (m k : ℕ) :
    PowerSeries.coeff k (flowRow d h u m) =
      Polynomial.aeval u (normalized d h (m + k)) / (k.factorial : ℂ) := by
  have hfac : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  apply (eq_div_iff hfac).mpr
  rw [mul_comm]
  exact factorial_mul_coeff_flowRow d h u m k

end RealRooted.TuranHurwitz
