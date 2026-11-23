module

public import RealRooted.Hermite.FormalDifferential.Basic
import RealRooted.Hermite.FormalDifferential.NegativeVariance
import RealRooted.Hermite.FormalDifferential.QuadraticObstruction
import RealRooted.Hermite.FormalDifferential.Composition
import RealRooted.Hermite.FormalDifferential.Structure

/-!
# The polynomial criterion for eventual splitting of formal iterates

The zero constant term branch is finite annihilation. With nonzero constant
term, the exact condition is strict negativity of the second cumulant.
The nonzero-input sufficiency is stronger: the eventual roots are simple.
-/

public section

open Polynomial Filter

namespace RealRooted.HermitePoulain

/-- Every real polynomial eventually splits under iteration exactly when the
formal symbol has zero constant coefficient or negative second cumulant.
The iteration threshold may depend on the polynomial. -/
theorem forall_eventually_splits_iterate_iff (φ : PowerSeries ℝ) :
    (∀ P : ℝ[X], ∀ᶠ m : ℕ in atTop, ((formalDifferentialOperator φ)^[m] P).Splits) ↔
      PowerSeries.constantCoeff φ = 0 ∨
        2 * PowerSeries.constantCoeff φ * PowerSeries.coeff 2 φ -
          PowerSeries.coeff 1 φ ^ 2 < 0 := by
  constructor
  · intro h
    by_cases h0 : PowerSeries.constantCoeff φ = 0
    · exact Or.inl h0
    · right
      by_contra hv
      obtain ⟨m, hm⟩ := (h (X ^ 2 + 1)).exists
      exact not_splits_iterate_formalDifferentialOperator_X_sq_add_one
        h0 (le_of_not_gt hv) m hm
  · rintro (h0 | hv) P
    · filter_upwards [eventually_gt_atTop P.natDegree] with m hm
      rw [iterate_formalDifferentialOperator_eq_zero h0 P hm]
      exact Splits.zero
    · by_cases h0 : PowerSeries.constantCoeff φ = 0
      · filter_upwards [eventually_gt_atTop P.natDegree] with m hm
        rw [iterate_formalDifferentialOperator_eq_zero h0 P hm]
        exact Splits.zero
      · by_cases hP : P = 0
        · subst P
          exact Eventually.of_forall fun m ↦ by
            rw [← formalDifferentialOperator_pow, formalDifferentialOperator_zero]
            exact Splits.zero
        · exact (eventually_simple_iterate_formalDifferentialOperator h0 hv hP).mono
            fun _ hm ↦ hm.2.1

end RealRooted.HermitePoulain
