module

public import RealRooted.Hermite.FormalDifferential.Basic
public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Operator
public import Mathlib.RingTheory.PowerSeries.Expand
public import Mathlib.RingTheory.PowerSeries.Exp
public import Mathlib.Analysis.Complex.Exponential
import RealRooted.Hermite.FormalDifferential.Taylor
import RealRooted.Mathlib.RingTheory.PowerSeries.ExpCoefficient
import RealRooted.Hermite.GaussianOperator
import RealRooted.Hermite.GaussianCoefficients
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Formal exponential symbols and the checked Taylor operators

The linear formal exponential translates polynomial inputs. The quadratic
formal exponential agrees exactly with the Gaussian Taylor operator.
-/

public section

open Polynomial Complex

namespace RealRooted.HermitePoulain

/-- A linear formal exponential acts by translation. -/
theorem formalDifferentialOperator_exp_linear (a : ℝ) (P : ℝ[X]) :
    formalDifferentialOperator (PowerSeries.rescale a (PowerSeries.exp ℝ)) P =
      P.comp (X + C a) := by
  rw [formalDifferentialOperator_eq_taylor _ (fun z ↦ Complex.exp ((a : ℂ) * z))]
  · exact taylor_exp_linear_eq_comp a P
  · intro k
    rw [PowerSeries.coeff_rescale_exp]
    simp only [iteratedDeriv_cexp_const_mul, mul_zero, exp_zero, mul_one,
      ← ofReal_pow, ← ofReal_natCast, ← ofReal_div, ofReal_re]

/-- The Gaussian formal coefficient is the actual ordinary Taylor coefficient. -/
private theorem coeff_exp_quadratic (s : ℝ) (k : ℕ) :
    PowerSeries.coeff k (PowerSeries.expand 2 (by decide)
      (PowerSeries.rescale s (PowerSeries.exp ℝ))) =
      (iteratedDeriv k (fun z : ℂ ↦ Complex.exp ((s : ℂ) * z ^ 2)) 0 / k.factorial).re := by
  obtain ⟨n, rfl | rfl⟩ := Nat.even_or_odd' k
  · rw [PowerSeries.coeff_expand_mul, PowerSeries.coeff_rescale_exp,
      iteratedDeriv_exp_mul_sq_zero_even]
    have hfac : ((2 * n).factorial : ℂ) ≠ 0 := by exact_mod_cast (2 * n).factorial_ne_zero
    have heq : (((2 * n).factorial : ℂ) * (s : ℂ) ^ n / n.factorial) /
        (2 * n).factorial = ((s : ℂ) ^ n / n.factorial) := by
      field_simp [hfac]
    rw [heq]
    simp only [← ofReal_pow, ← ofReal_natCast, ← ofReal_div, ofReal_re]
  · have hn : ¬ 2 ∣ 2 * n + 1 := by
      rintro ⟨j, hj⟩
      lia
    rw [PowerSeries.coeff_expand_of_not_dvd _ _ _ hn,
      iteratedDeriv_exp_mul_sq_zero_odd]
    simp

/-- The quadratic formal exponential agrees with the actual Gaussian Taylor operator. -/
theorem formalDifferentialOperator_exp_quadratic (s : ℝ) (P : ℝ[X]) :
    formalDifferentialOperator (PowerSeries.expand 2 (by decide)
      (PowerSeries.rescale s (PowerSeries.exp ℝ))) P =
      taylorDifferentialOperator (fun z ↦ Complex.exp ((s : ℂ) * z ^ 2)) P :=
  formalDifferentialOperator_eq_taylor _ _ (coeff_exp_quadratic s) P

end RealRooted.HermitePoulain
