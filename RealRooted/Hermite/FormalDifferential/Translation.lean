module

public import RealRooted.Hermite.FormalDifferential.Basic
public import Mathlib.RingTheory.PowerSeries.Exp
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Algebra.Rat
import RealRooted.Hermite.FormalDifferential.Exponential
import RealRooted.Hermite.FormalDifferential.Composition

/-!
# Linear exponential factors in iterated formal symbols
-/

public section

open Polynomial

namespace RealRooted.HermitePoulain

/-- A linear exponential factor translates the iterated polynomial output
by the iteration count times its parameter. -/
theorem formalDifferentialOperator_linear_exp_mul_pow
    (φ : PowerSeries ℝ) (a : ℝ) (m : ℕ) (P : ℝ[X]) :
    formalDifferentialOperator ((PowerSeries.rescale a (PowerSeries.exp ℝ) * φ) ^ m) P =
      (formalDifferentialOperator (φ ^ m) P).comp (X + C ((m : ℝ) * a)) := by
  rw [mul_pow, ← map_pow, PowerSeries.exp_pow_eq_rescale_exp,
    PowerSeries.rescale_rescale, formalDifferentialOperator_mul,
    formalDifferentialOperator_exp_linear]

end RealRooted.HermitePoulain
