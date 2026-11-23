module

public import RealRooted.Hermite.FormalDifferential.Basic
public import Mathlib.RingTheory.Polynomial.ScaleRoots
import RealRooted.Hermite.FormalDifferential.OperatorLimits
import RealRooted.Hermite.FormalDifferential.Structure
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Root scaling covariance of formal differential operators

The constant coefficient hypothesis prevents a change of degree. The root
scale itself may be zero; this endpoint records leading coefficient preservation.
-/

public section

open Polynomial

namespace RealRooted.HermitePoulain

/-- Rescaling the roots of a differential image rescales the formal symbol
by the same factor. The scale zero is included. -/
theorem scaleRoots_formalDifferentialOperator {φ : PowerSeries ℝ}
    (hφ : PowerSeries.constantCoeff φ ≠ 0) (P : ℝ[X]) (r : ℝ) :
    (formalDifferentialOperator φ P).scaleRoots r =
      formalDifferentialOperator (PowerSeries.rescale r φ) (P.scaleRoots r) := by
  by_cases hP : P = 0
  · simp [hP]
  ext j
  rw [coeff_scaleRoots, natDegree_formalDifferentialOperator hφ hP,
    coeff_formalDifferentialOperator_of_natDegree_le φ le_rfl,
    coeff_formalDifferentialOperator_of_natDegree_le _
      (le_of_eq (natDegree_scaleRoots P r)), Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  rw [PowerSeries.coeff_rescale, coeff_scaleRoots]
  by_cases hjk : j + k ≤ P.natDegree
  · have hexp : k + (P.natDegree - (j + k)) = P.natDegree - j := by lia
    rw [← hexp, pow_add]
    ring
  · rw [coeff_eq_zero_of_natDegree_lt (Nat.lt_of_not_ge hjk)]
    ring

end RealRooted.HermitePoulain
