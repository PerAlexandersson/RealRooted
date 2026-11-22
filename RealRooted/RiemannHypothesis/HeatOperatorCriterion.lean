module

public import RealRooted.RiemannHypothesis
public import RealRooted.Mathlib.Analysis.Complex.HeatOperator.Basic
public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.HeatOperatorCriterion
import RealRooted.RiemannHypothesis.HeatOperator

/-!
# RH criteria from positive-time xi heat images

Mathlib's RH is equivalent to LP membership of the normalized square-variable
xi heat images at all positive times, or just at arbitrarily small positive
times. The criterion also admits all derivative shifts. These are consequences
of the existing RH equivalence and the general heat-limit criterion.
-/

public section

open Complex

namespace RealRooted

/-- RH is equivalent to LP membership of every positive-time heat image of
the normalized square-variable xi function. -/
theorem riemannHypothesis_iff_heatOperator_pos :
    RiemannHypothesis ↔ ∀ t : ℝ, 0 < t →
      IsLaguerrePolya (heatOperator (t : ℂ) riemannXiTheta) := by
  rw [riemannHypothesis_iff_isLaguerrePolya_riemannXiTheta]
  exact isLaguerrePolya_iff_heatOperator_pos differentiable_riemannXiTheta
    orderLE_half_riemannXiTheta (by norm_num)

/-- It suffices to test LP membership of xi heat images at arbitrarily small
positive times. No simplicity assertion is made at time zero. -/
theorem riemannHypothesis_iff_heatOperator_near_zero :
    RiemannHypothesis ↔ ∀ ε : ℝ, 0 < ε → ∃ t : ℝ, 0 < t ∧ t < ε ∧
      IsLaguerrePolya (heatOperator (t : ℂ) riemannXiTheta) := by
  rw [riemannHypothesis_iff_isLaguerrePolya_riemannXiTheta]
  exact isLaguerrePolya_iff_heatOperator_near_zero differentiable_riemannXiTheta
    orderLE_half_riemannXiTheta (by norm_num)

/-- RH is equivalent to LP membership of all derivative shifts of the xi
heat images at every positive time. -/
theorem riemannHypothesis_iff_iteratedDeriv_heatOperator_pos :
    RiemannHypothesis ↔ ∀ n : ℕ, ∀ t : ℝ, 0 < t →
      IsLaguerrePolya (heatOperator (t : ℂ) (iteratedDeriv n riemannXiTheta)) := by
  constructor
  · exact fun hRH n _ ht => (heatOperator_riemannXiTheta_simple_zeros hRH n ht).1
  · intro h
    exact riemannHypothesis_iff_heatOperator_pos.mpr (by simpa using h 0)

end RealRooted
