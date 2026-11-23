module

public import RealRooted.Mathlib.RingTheory.Polynomial.Laguerre.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Polynomial.Splits
import RealRooted.Mathlib.RingTheory.Polynomial.Laguerre.Differential
import RealRooted.Laguerre.Roots
import RealRooted.ObreschkoffConverse.Forward

/-!
# Real Laguerre roots beyond the orthogonality range

Every generalized Laguerre polynomial splits for parameters at least `-2`.
The parameter-shift identity expresses it as a linear combination of an
interlacing pair in the classical range. This includes both endpoints and
allows mixed-sign roots when the parameter lies strictly between `-2` and `-1`.
-/

public section

open Polynomial

namespace RealRooted

/-- Generalized Laguerre polynomials split throughout the extended range
`-2 ≤ α`, including the degenerate parameter endpoints. -/
theorem generalizedLaguerre_splits_of_neg_two_le (n : ℕ) {α : ℝ}
    (hα : -2 ≤ α) : (generalizedLaguerre n α).Splits := by
  cases n with
  | zero => simp
  | succ n =>
      rw [generalizedLaguerre_succ_eq_sub]
      have hpair := generalizedLaguerre_strictInterl_succ n
        (show -1 ≤ α + 1 by linarith)
      simpa only [map_neg, map_one, one_mul, neg_mul, sub_eq_add_neg, add_comm] using
        (allComboRealRooted_of_strictInterl hpair) (-(n + 1 : ℝ)) 1

end RealRooted
