module

public import RealRooted.Hermite.FormalDifferential.Basic
public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Operator

/-!
# Formal symbols and finite Taylor differential operators
-/

public section

open Polynomial Complex

namespace RealRooted.HermitePoulain

/-- Matching ordinary coefficients identifies formal and Taylor differential operators. -/
theorem formalDifferentialOperator_eq_taylor (φ : PowerSeries ℝ) (f : ℂ → ℂ)
    (hcoeff : ∀ k, PowerSeries.coeff k φ = (iteratedDeriv k f 0 / k.factorial).re)
    (P : ℝ[X]) : formalDifferentialOperator φ P = taylorDifferentialOperator f P := by
  rw [formalDifferentialOperator_eq_sum, taylorDifferentialOperator]
  apply Finset.sum_congr rfl
  intro k _
  rw [hcoeff]

end RealRooted.HermitePoulain
