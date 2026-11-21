module

public import RealRooted.EffectiveBKW.Tail
public import RealRooted.EffectiveBKW.QuadraticInverse
import Mathlib.Tactic.NormNum

/-!
# Effective BKW tail regressions

Small exact checks exercise the reusable majorant and quadratic-inverse APIs.
-/

public section

namespace RealRooted.EffectiveBKW.TailExamples

/-- A constant cofactor has no tail after the numerator has been included. -/
example : tail (1 / 2) [1] 0 0 = 0 := by
  rw [tail_eq_closedForm (by norm_num) (by norm_num)]
  norm_num [majorantCoeff, Finset.sum_range_succ, List.getD]

/-- Natural subtraction keeps all terms when a numerator index exceeds the cutoff. -/
example : tail (1 / 2) [1, 0, 0, 2] 0 0 = 2 := by
  rw [tail_eq_closedForm (by norm_num) (by norm_num)]
  norm_num [majorantCoeff, Finset.sum_range_succ, List.getD]

/-- The first nontrivial inverse coefficient agrees with the quadratic recurrence. -/
example (a b : ℝ) : PowerSeries.coeff 2 (quadraticInverse a b) = 4 * a ^ 2 - b := by
  rw [coeff_quadraticInverse_add_two a b 0]
  simp
  ring

end RealRooted.EffectiveBKW.TailExamples
