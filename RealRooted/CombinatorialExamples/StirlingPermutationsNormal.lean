import RealRooted.CombinatorialExamples.StirlingPermutations
import RealRooted.Mathlib.Probability.CoeffDistribution

/-!
# Second-order Eulerian numbers are asymptotically normal

The descent polynomials of Stirling permutations satisfy
`P_{n+1} = (2n + 1) X P_n + X (1 - X) P_n'`, whose coefficients are the second-order Eulerian
numbers.  At `x = 1` the factor `1 - X` vanishes, so the values of `P_n`, `P_n'` and `P_n''` at
`1` satisfy closed scalar recurrences.  For `n ≥ 1` the coefficient distribution of `P_n` has
mean `(2n + 1) / 3` and variance `2 (n² - 1) / (9 (2n - 1))`.  Since the polynomials are
real-rooted (Bóna; Haglund–Visontai), Harper's theorem gives asymptotic normality.
-/

open Polynomial Filter Topology ProbabilityTheory

namespace RealRooted

private theorem eval_one_stirlingPermutations_step (n : ℕ) :
    (stirlingPermutations (n + 1)).eval 1 = (2 * n + 1) * (stirlingPermutations n).eval 1 := by
  simp [stirlingPermutations_succ, stirlingPermutationsCoeffA, stirlingPermutationsCoeffB]

private theorem eval_one_derivative_stirlingPermutations_step (n : ℕ) :
    (stirlingPermutations (n + 1)).derivative.eval 1 =
      (2 * n + 1) * (stirlingPermutations n).eval 1 +
        2 * n * (stirlingPermutations n).derivative.eval 1 := by
  simp [stirlingPermutations_succ, stirlingPermutationsCoeffA, stirlingPermutationsCoeffB,
    derivative_mul]
  ring

private theorem eval_one_derivative_derivative_stirlingPermutations_step (n : ℕ) :
    (stirlingPermutations (n + 1)).derivative.derivative.eval 1 =
      4 * n * (stirlingPermutations n).derivative.eval 1 +
        (2 * n - 1) * (stirlingPermutations n).derivative.derivative.eval 1 := by
  simp [stirlingPermutations_succ, stirlingPermutationsCoeffA, stirlingPermutationsCoeffB,
    derivative_mul]
  ring

theorem eval_one_stirlingPermutations_pos (n : ℕ) : 0 < (stirlingPermutations n).eval 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [eval_one_stirlingPermutations_step]
    positivity

/-- For `n ≥ 1` the coefficient distribution of `stirlingPermutations n` has mean
`(2n + 1) / 3`. -/
theorem eval_one_derivative_stirlingPermutations_succ (n : ℕ) :
    (stirlingPermutations (n + 1)).derivative.eval 1 =
      (2 * n + 3) / 3 * (stirlingPermutations (n + 1)).eval 1 := by
  induction n with
  | zero => simp [stirlingPermutations_one]
  | succ n ih =>
    rw [eval_one_derivative_stirlingPermutations_step (n + 1), ih,
      eval_one_stirlingPermutations_step (n + 1)]
    push_cast
    ring

theorem eval_one_derivative_derivative_stirlingPermutations_succ (n : ℕ) :
    (stirlingPermutations (n + 1)).derivative.derivative.eval 1 =
      2 * (n + 1) * n * (4 * n + 5) / (9 * (2 * n + 1)) *
        (stirlingPermutations (n + 1)).eval 1 := by
  induction n with
  | zero => simp [stirlingPermutations_one]
  | succ n ih =>
    rw [eval_one_derivative_derivative_stirlingPermutations_step (n + 1), ih,
      eval_one_derivative_stirlingPermutations_succ, eval_one_stirlingPermutations_step (n + 1)]
    push_cast
    field_simp
    ring

/-- For `n ≥ 1` the coefficient distribution of `stirlingPermutations n` has variance
`2 (n² - 1) / (9 (2n - 1))`, written here at `n + 1`. -/
theorem coeffVariance_stirlingPermutations_succ (n : ℕ) :
    (stirlingPermutations (n + 1)).coeffVariance = 2 * n * (n + 2) / (9 * (2 * n + 1)) := by
  have hpos := (eval_one_stirlingPermutations_pos (n + 1)).ne'
  rw [Polynomial.coeffVariance, Polynomial.coeffMean,
    eval_one_derivative_stirlingPermutations_succ,
    eval_one_derivative_derivative_stirlingPermutations_succ, mul_div_cancel_right₀ _ hpos,
    mul_div_cancel_right₀ _ hpos]
  field_simp
  ring

/-- **The second-order Eulerian numbers are asymptotically normal**: the standardized
coefficient distributions of the Stirling-permutation descent polynomials converge weakly to
the standard normal law. -/
theorem tendsto_standardizedCoeffDistribution_stirlingPermutations :
    Tendsto (fun n => (stirlingPermutations n).standardizedCoeffDistribution) atTop
      (𝓝 ⟨gaussianReal 0 1, inferInstance⟩) := by
  have h := Polynomial.tendsto_standardizedCoeffDistribution
    (P := fun n => stirlingPermutations (n + 1))
    (fun n => (isRealRooted_stirlingPermutations (n + 1)).2)
    (fun n k => stirlingPermutations_nonnegCoeffs (n + 1) k) ?_
  · exact (tendsto_add_atTop_iff_nat 1).mp h
  simp only [coeffVariance_stirlingPermutations_succ]
  refine tendsto_atTop_mono (fun n => ?_)
    (tendsto_natCast_atTop_atTop.atTop_div_const (by norm_num : (0 : ℝ) < 9))
  rw [div_le_div_iff₀ (by norm_num) (by positivity)]
  nlinarith [n.cast_nonneg (α := ℝ)]

end RealRooted
