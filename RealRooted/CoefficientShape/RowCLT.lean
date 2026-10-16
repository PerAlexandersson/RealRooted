module

public import RealRooted.ThreeTermRecurrence.CoeffMoments

/-!
# Row CLTs from coefficient moments

This module connects the existing moment calculations for product and
constant-coefficient three-term recurrences to Harper's coefficient-distribution CLT.
-/

public section

open Filter Topology ProbabilityTheory
open scoped BigOperators Polynomial

namespace Polynomial

/-- A product recurrence has asymptotically normal coefficient distributions when every row is
real-rooted with nonnegative coefficients and the summed factor variances diverge. -/
theorem tendsto_standardizedCoeffDistribution_of_succ_eq_mul
    {P L : ℕ → ℝ[X]} (hrec : ∀ n, P (n + 1) = L n * P n)
    (hP : ∀ n, (P n).eval 1 ≠ 0) (hL : ∀ n, (L n).eval 1 ≠ 0)
    (hs : ∀ n, (P n).Splits) (hnn : ∀ n k, 0 ≤ (P n).coeff k)
    (hvar : Tendsto (fun n => ∑ i ∈ Finset.range n, (L i).coeffVariance) atTop atTop) :
    Tendsto (fun n => (P n).standardizedCoeffDistribution) atTop
      (𝓝 ⟨gaussianReal 0 1, inferInstance⟩) := by
  apply tendsto_standardizedCoeffDistribution hs hnn
  have hsum : Tendsto
      (fun n => (P 0).coeffVariance + ∑ i ∈ Finset.range n, (L i).coeffVariance) atTop atTop :=
    tendsto_atTop_add_const_left _ _ hvar
  refine hsum.congr' ?_
  filter_upwards with n
  exact (coeffVariance_eq_add_sum_range_of_succ_eq_mul hrec hP hL n).symm

end Polynomial

namespace RealRooted.ThreeTermRecurrence

/-- A constant-coefficient three-term recurrence has asymptotically normal coefficient
distributions when its dominant-root variance slope is positive and every row is real-rooted
with nonnegative coefficients. -/
theorem tendsto_standardizedCoeffDistribution_of_dominant_root
    {P : ℕ → ℝ[X]} {a b : ℝ[X]} {lam nu : ℝ}
    (hrec : ∀ n, P (n + 2) = a * P (n + 1) + b * P n)
    (hLam : lam ^ 2 = a.eval 1 * lam + b.eval 1)
    (hNu : nu ^ 2 = a.eval 1 * nu + b.eval 1)
    (hDistinct : lam ≠ nu) (hDominant : 0 < lam) (hModulus : |nu| < lam)
    (hNuNe : nu ≠ 0)
    (hA : ((P 1).eval 1 - nu * (P 0).eval 1) / (lam - nu) ≠ 0)
    (hSlope : 0 < varianceSlope a b lam) (hs : ∀ n, (P n).Splits)
    (hnn : ∀ n k, 0 ≤ (P n).coeff k) :
    Tendsto (fun n => (P n).standardizedCoeffDistribution) atTop
      (𝓝 ⟨gaussianReal 0 1, inferInstance⟩) :=
  Polynomial.tendsto_standardizedCoeffDistribution hs hnn
    (tendsto_coeffVariance_atTop hrec hLam hNu hDistinct hDominant hModulus hNuNe hA hSlope)

end RealRooted.ThreeTermRecurrence
