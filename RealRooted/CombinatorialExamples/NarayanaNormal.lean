import RealRooted.CombinatorialExamples.Narayana
import RealRooted.Mathlib.Probability.CoeffDistribution

/-!
# Narayana numbers are asymptotically normal

The quotient Narayana polynomials `Q_n = ∑ₖ N(n, k + 1) xᵏ` satisfy the three-term recurrence
`(n + 3) Q_{n+2} = (2n + 3)(1 + X) Q_{n+1} - n (1 - X)² Q_n`.  At `x = 1` the factor `(1 - X)²`
vanishes to second order, so the values of `Q_n`, `Q_n'` and `Q_n''` at `1` satisfy closed
scalar recurrences.  The coefficient distribution of `Q_n` has mean `(n - 1) / 2` and variance
`(n² - 1) / (4 (2n - 1))`.  Since the Narayana polynomials are real-rooted, Harper's theorem gives
asymptotic normality of the Narayana numbers.
-/

open Polynomial Filter Topology ProbabilityTheory

namespace RealRooted

private theorem eval_one_narayanaQuot_succ_succ (n : ℕ) :
    (narayanaQuot (n + 2)).eval 1 = 2 * (2 * n + 3) / (n + 3) * (narayanaQuot (n + 1)).eval 1 := by
  rw [narayanaQuot_succ_succ]
  simp only [narayanaCoeffA, narayanaCoeffB, eval_add, eval_sub, eval_mul, eval_pow, eval_C,
    eval_X, eval_one]
  ring

private theorem eval_one_derivative_narayanaQuot_succ_succ (n : ℕ) :
    (narayanaQuot (n + 2)).derivative.eval 1 =
      (2 * n + 3) / (n + 3) *
        ((narayanaQuot (n + 1)).eval 1 + 2 * (narayanaQuot (n + 1)).derivative.eval 1) := by
  rw [narayanaQuot_succ_succ]
  simp only [narayanaCoeffA, narayanaCoeffB, derivative_mul, derivative_add, derivative_sub,
    derivative_pow, derivative_C, derivative_X, derivative_one, eval_add, eval_sub, eval_mul,
    eval_pow, eval_C, eval_X, eval_one, eval_zero]
  ring

private theorem eval_one_derivative_derivative_narayanaQuot_succ_succ (n : ℕ) :
    (narayanaQuot (n + 2)).derivative.derivative.eval 1 =
      (2 * n + 3) / (n + 3) * (2 * (narayanaQuot (n + 1)).derivative.eval 1 +
        2 * (narayanaQuot (n + 1)).derivative.derivative.eval 1) -
      2 / (n + 3) * (n * (narayanaQuot n).eval 1) := by
  rw [narayanaQuot_succ_succ]
  simp only [narayanaCoeffA, narayanaCoeffB, derivative_mul, derivative_add, derivative_sub,
    derivative_pow, derivative_C, derivative_X, derivative_one, eval_add, eval_sub, eval_mul,
    eval_pow, eval_C, eval_X, eval_one, eval_zero, derivative_zero]
  ring

private theorem natCast_mul_eval_one_narayanaQuot (n : ℕ) :
    n * (narayanaQuot n).eval 1 =
      n * (n + 2) / (2 * (2 * n + 1)) * (narayanaQuot (n + 1)).eval 1 := by
  cases n with
  | zero => simp
  | succ n =>
    rw [eval_one_narayanaQuot_succ_succ]
    push_cast
    field_simp
    ring

theorem eval_one_narayanaQuot_pos {n : ℕ} (hn : n ≠ 0) : 0 < (narayanaQuot n).eval 1 := by
  induction n with
  | zero => exact absurd rfl hn
  | succ n ih =>
    rcases n with _ | n
    · simp
    rw [eval_one_narayanaQuot_succ_succ]
    have := ih (Nat.succ_ne_zero n)
    positivity

/-- The coefficient distribution of `narayanaQuot n` has mean `(n - 1) / 2`. -/
theorem eval_one_derivative_narayanaQuot : ∀ n : ℕ,
    (narayanaQuot n).derivative.eval 1 = ((n : ℝ) - 1) / 2 * (narayanaQuot n).eval 1
  | 0 => by simp
  | 1 => by simp
  | n + 2 => by
    rw [eval_one_derivative_narayanaQuot_succ_succ, eval_one_derivative_narayanaQuot (n + 1),
      eval_one_narayanaQuot_succ_succ]
    push_cast
    field_simp
    ring

theorem eval_one_derivative_derivative_narayanaQuot : ∀ n : ℕ,
    (narayanaQuot n).derivative.derivative.eval 1 =
      ((n : ℝ) - 1) ^ 2 * ((n : ℝ) - 2) / (2 * (2 * n - 1)) * (narayanaQuot n).eval 1
  | 0 => by simp
  | 1 => by simp
  | n + 2 => by
    have h1 : (2 * (n : ℝ) + 1) ≠ 0 := by positivity
    have h3 : (2 * (n : ℝ) + 3) ≠ 0 := by positivity
    rw [eval_one_derivative_derivative_narayanaQuot_succ_succ,
      eval_one_derivative_derivative_narayanaQuot (n + 1), eval_one_derivative_narayanaQuot,
      natCast_mul_eval_one_narayanaQuot, eval_one_narayanaQuot_succ_succ]
    push_cast
    ring_nf
    field_simp
    ring

/-- The coefficient distribution of `narayanaQuot n` has variance `(n² - 1) / (4 (2n - 1))`. -/
theorem coeffVariance_narayanaQuot {n : ℕ} (hn : n ≠ 0) :
    (narayanaQuot n).coeffVariance = ((n : ℝ) ^ 2 - 1) / (4 * (2 * n - 1)) := by
  have hpos := (eval_one_narayanaQuot_pos hn).ne'
  rw [Polynomial.coeffVariance, Polynomial.coeffMean, eval_one_derivative_narayanaQuot,
    eval_one_derivative_derivative_narayanaQuot, mul_div_cancel_right₀ _ hpos,
    mul_div_cancel_right₀ _ hpos]
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  push_cast
  ring_nf
  field_simp
  ring

/-- The Narayana polynomial `narayana n = X * narayanaQuot n` has the same variance. -/
theorem coeffVariance_narayana {n : ℕ} (hn : n ≠ 0) :
    (narayana n).coeffVariance = ((n : ℝ) ^ 2 - 1) / (4 * (2 * n - 1)) := by
  rw [narayana, Polynomial.coeffVariance_mul (by simp) (eval_one_narayanaQuot_pos hn).ne',
    coeffVariance_narayanaQuot hn]
  simp [Polynomial.coeffVariance, Polynomial.coeffMean]

/-- **The Narayana numbers are asymptotically normal**: the standardized coefficient
distributions of the Narayana polynomials converge weakly to the standard normal law. -/
theorem tendsto_standardizedCoeffDistribution_narayana :
    Tendsto (fun n => (narayana n).standardizedCoeffDistribution) atTop
      (𝓝 ⟨gaussianReal 0 1, inferInstance⟩) := by
  have h := Polynomial.tendsto_standardizedCoeffDistribution
    (P := fun n => narayana (n + 1)) (fun n => (isRealRooted_narayana (n + 1) n.succ_ne_zero).2)
    (fun n k => ?_) ?_
  · exact (tendsto_add_atTop_iff_nat 1).mp h
  · rcases k with _ | k
    · simp [narayana]
    · simpa [narayana, coeff_X_mul] using narayanaQuot_hasNonnegCoeffs (n + 1) k
  simp only [coeffVariance_narayana (Nat.succ_ne_zero _)]
  refine tendsto_atTop_mono (fun n => ?_)
    (tendsto_natCast_atTop_atTop.atTop_div_const (by norm_num : (0 : ℝ) < 8))
  push_cast
  rw [div_le_div_iff₀ (by norm_num) (by linarith [n.cast_nonneg (α := ℝ)])]
  nlinarith

end RealRooted
