import RealRooted.JacobiDeformation.JacobiMoment
import RealRooted.JacobiDeformation.VandermondeIdentity

/-!
# Finite-sum bridge for normalized Jacobi moments

This module gives the exact Chu--Vandermonde orientation needed after the
explicit coefficient expansion of `normalizedShiftedJacobi`.
-/

open Finset
open scoped BigOperators

noncomputable section

namespace RealRooted.JacobiDeformation

/-- The finite coefficient sum required by the `j ≤ k` normalized Jacobi
moment calculation. No relation between `j` and `k` is assumed. -/
theorem normalizedJacobiMoment_vandermonde_sum
    (j k : ℕ) (s : ℝ) (hs : 0 < s) :
    ∑ i ∈ Finset.range (j + 1), (-1 : ℝ) ^ i * (j.choose i : ℝ) *
        FiniteVandermonde.rising ((j : ℝ) + s - 1) i /
          FiniteVandermonde.rising (s + (k : ℝ)) i =
      FiniteVandermonde.falling (k : ℝ) j /
        FiniteVandermonde.rising (s + (k : ℝ)) j := by
  exact FiniteVandermonde.chu_vandermonde_terminating j k s hs

/-- The finite sum above is zero in the strict `j > k` boundary. -/
theorem normalizedJacobiMoment_vandermonde_sum_eq_zero
    (j k : ℕ) (s : ℝ) (hs : 0 < s) (hkj : k < j) :
    ∑ i ∈ Finset.range (j + 1), (-1 : ℝ) ^ i * (j.choose i : ℝ) *
        FiniteVandermonde.rising ((j : ℝ) + s - 1) i /
          FiniteVandermonde.rising (s + (k : ℝ)) i = 0 := by
  exact FiniteVandermonde.chu_vandermonde_terminating_eq_zero j k s hs hkj

end RealRooted.JacobiDeformation
