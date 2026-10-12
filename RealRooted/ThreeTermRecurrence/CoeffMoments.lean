import RealRooted.Mathlib.Probability.CoeffDistribution
import RealRooted.ThreeTermRecurrence.Moments

/-!
# Row moments from polynomial recurrences

This file supplies recurrence-facing wrappers around the product-moment and
constant-coefficient three-term-recurrence APIs.  A product recurrence gives exact finite sums
for the coefficient mean and variance.  For a three-term recurrence, the existing dominant-root
limits are restated using `Polynomial.coeffMean` and `Polynomial.coeffVariance`; a positive
variance slope then implies divergence of the variance, as required by Harper's central limit
theorem.
-/

open Filter Topology
open scoped BigOperators Polynomial

namespace Polynomial

/-- Along a product recurrence `P (n + 1) = L n * P n`, the coefficient mean at row `n` is
the initial mean plus the sum of the means of the first `n` factors. -/
theorem coeffMean_eq_add_sum_range_of_succ_eq_mul
    {P L : ℕ → ℝ[X]} (hrec : ∀ n, P (n + 1) = L n * P n)
    (hP : ∀ n, (P n).eval 1 ≠ 0) (hL : ∀ n, (L n).eval 1 ≠ 0) (n : ℕ) :
    (P n).coeffMean = (P 0).coeffMean +
      ∑ i ∈ Finset.range n, (L i).coeffMean := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [hrec n, coeffMean_mul (hL n) (hP n), ih, Finset.sum_range_succ]
    ring

/-- Along a product recurrence `P (n + 1) = L n * P n`, the coefficient variance at row `n`
is the initial variance plus the sum of the variances of the first `n` factors. -/
theorem coeffVariance_eq_add_sum_range_of_succ_eq_mul
    {P L : ℕ → ℝ[X]} (hrec : ∀ n, P (n + 1) = L n * P n)
    (hP : ∀ n, (P n).eval 1 ≠ 0) (hL : ∀ n, (L n).eval 1 ≠ 0) (n : ℕ) :
    (P n).coeffVariance = (P 0).coeffVariance +
      ∑ i ∈ Finset.range n, (L i).coeffVariance := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [hrec n, coeffVariance_mul (hL n) (hP n), ih, Finset.sum_range_succ]
    ring

end Polynomial

namespace RealRooted.ThreeTermRecurrence

/-- Under the dominant-root hypotheses for a constant-coefficient polynomial three-term
recurrence, the coefficient mean divided by the row index tends to `meanSlope`. -/
theorem tendsto_coeffMean_div_nat
    {P : ℕ → ℝ[X]} {a b : ℝ[X]} {lam nu : ℝ}
    (hP : ∀ n, P (n + 2) = a * P (n + 1) + b * P n)
    (hLam : lam ^ 2 = a.eval 1 * lam + b.eval 1)
    (hNu : nu ^ 2 = a.eval 1 * nu + b.eval 1)
    (hDistinct : lam ≠ nu) (hDominant : 0 < lam) (hModulus : |nu| < lam)
    (hNuNe : nu ≠ 0)
    (hA : ((P 1).eval 1 - nu * (P 0).eval 1) / (lam - nu) ≠ 0) :
    Tendsto (fun n ↦ (P n).coeffMean / (n : ℝ)) atTop
      (nhds (meanSlope a b lam)) := by
  simpa only [Polynomial.coeffMean, div_div, mul_comm] using
    tendsto_derivative_eval_div_nat_mul_eval hP hLam hNu hDistinct hDominant hModulus hNuNe hA

/-- Under the dominant-root hypotheses for a constant-coefficient polynomial three-term
recurrence, the coefficient variance divided by the row index tends to `varianceSlope`. -/
theorem tendsto_coeffVariance_div_nat
    {P : ℕ → ℝ[X]} {a b : ℝ[X]} {lam nu : ℝ}
    (hP : ∀ n, P (n + 2) = a * P (n + 1) + b * P n)
    (hLam : lam ^ 2 = a.eval 1 * lam + b.eval 1)
    (hNu : nu ^ 2 = a.eval 1 * nu + b.eval 1)
    (hDistinct : lam ≠ nu) (hDominant : 0 < lam) (hModulus : |nu| < lam)
    (hNuNe : nu ≠ 0)
    (hA : ((P 1).eval 1 - nu * (P 0).eval 1) / (lam - nu) ≠ 0) :
    Tendsto (fun n ↦ (P n).coeffVariance / (n : ℝ)) atTop
      (nhds (varianceSlope a b lam)) := by
  simpa only [Polynomial.coeffVariance, Polynomial.coeffMean] using
    tendsto_variance_eval_div_nat hP hLam hNu hDistinct hDominant hModulus hNuNe hA

/-- If the dominant-root variance slope is positive, the coefficient variance of the rows tends
to positive infinity.  This is the variance hypothesis required by Harper's central limit
theorem. -/
theorem tendsto_coeffVariance_atTop
    {P : ℕ → ℝ[X]} {a b : ℝ[X]} {lam nu : ℝ}
    (hP : ∀ n, P (n + 2) = a * P (n + 1) + b * P n)
    (hLam : lam ^ 2 = a.eval 1 * lam + b.eval 1)
    (hNu : nu ^ 2 = a.eval 1 * nu + b.eval 1)
    (hDistinct : lam ≠ nu) (hDominant : 0 < lam) (hModulus : |nu| < lam)
    (hNuNe : nu ≠ 0)
    (hA : ((P 1).eval 1 - nu * (P 0).eval 1) / (lam - nu) ≠ 0)
    (hSlope : 0 < varianceSlope a b lam) :
    Tendsto (fun n ↦ (P n).coeffVariance) atTop atTop := by
  have hratio := tendsto_coeffVariance_div_nat hP hLam hNu hDistinct hDominant hModulus
    hNuNe hA
  have hprod : Tendsto
      (fun n ↦ (P n).coeffVariance / (n : ℝ) * (n : ℝ)) atTop atTop :=
    hratio.pos_mul_atTop hSlope tendsto_natCast_atTop_atTop
  refine hprod.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hn)
  field_simp

end RealRooted.ThreeTermRecurrence
