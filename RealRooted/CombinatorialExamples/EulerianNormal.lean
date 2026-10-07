import RealRooted.CombinatorialExamples.Eulerian
import RealRooted.Mathlib.Probability.CoeffDistribution

/-!
# Eulerian numbers are asymptotically normal

The Eulerian polynomials `eulerianTilde n = ∑ₖ A(n + 1, k) xᵏ` are real-rooted with nonnegative
coefficients.  From the recurrence `E_{n+1} = X (C (n + 2) E_n + (1 - X) E_n')` the values of
`E_n`, `E_n'` and `E_n''` at `1` satisfy closed scalar recurrences, so the coefficient
distribution has mean `(n + 2) / 2` and, for `n ≥ 1`, variance `(n + 2) / 12`.  Harper's theorem
then gives asymptotic normality of the Eulerian numbers (Bender 1973; David–Barton 1962).
-/

open Polynomial Filter Topology ProbabilityTheory

namespace RealRooted

private theorem eval_one_step (E : ℝ[X]) (c : ℝ) :
    (X * (C c * E + (1 - X) * E.derivative)).eval 1 = c * E.eval 1 := by
  simp

private theorem eval_one_derivative_step (E : ℝ[X]) (c : ℝ) :
    (X * (C c * E + (1 - X) * E.derivative)).derivative.eval 1 =
      c * E.eval 1 + (c - 1) * E.derivative.eval 1 := by
  simp [derivative_mul]
  ring

private theorem eval_one_derivative_derivative_step (E : ℝ[X]) (c : ℝ) :
    (X * (C c * E + (1 - X) * E.derivative)).derivative.derivative.eval 1 =
      2 * (c - 1) * E.derivative.eval 1 + (c - 2) * E.derivative.derivative.eval 1 := by
  simp [derivative_mul]
  ring

theorem eval_one_eulerianTilde (n : ℕ) : (eulerianTilde n).eval 1 = (n + 1).factorial := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [eulerianTilde_recurrence, eval_one_step, ih, Nat.factorial_succ (n + 1)]
    push_cast
    ring

theorem eval_one_derivative_eulerianTilde (n : ℕ) :
    (eulerianTilde n).derivative.eval 1 = (n + 2) / 2 * (n + 1).factorial := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [eulerianTilde_recurrence, eval_one_derivative_step, ih, eval_one_eulerianTilde,
      Nat.factorial_succ (n + 1)]
    push_cast
    ring

theorem eval_one_derivative_derivative_eulerianTilde {n : ℕ} (hn : n ≠ 0) :
    (eulerianTilde n).derivative.derivative.eval 1 =
      (n + 2) * (3 * n + 1) / 12 * (n + 1).factorial := by
  induction n with
  | zero => exact absurd rfl hn
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · simp [eulerianTilde_one]
      norm_num
    rw [eulerianTilde_recurrence, eval_one_derivative_derivative_step,
      eval_one_derivative_eulerianTilde, ih hpos.ne', Nat.factorial_succ (n + 1)]
    push_cast
    ring

/-- The coefficient distribution of `eulerianTilde n` has variance `(n + 2) / 12` for
`n ≥ 1`. -/
theorem coeffVariance_eulerianTilde {n : ℕ} (hn : n ≠ 0) :
    (eulerianTilde n).coeffVariance = (n + 2) / 12 := by
  have hf : ((n + 1).factorial : ℝ) ≠ 0 := by positivity
  rw [Polynomial.coeffVariance, Polynomial.coeffMean, eval_one_eulerianTilde,
    eval_one_derivative_eulerianTilde, eval_one_derivative_derivative_eulerianTilde hn]
  field_simp
  ring

/-- **The Eulerian numbers are asymptotically normal**: the standardized coefficient
distributions of the Eulerian polynomials converge weakly to the standard normal law. -/
theorem tendsto_standardizedCoeffDistribution_eulerianTilde :
    Tendsto (fun n => (eulerianTilde n).standardizedCoeffDistribution) atTop
      (𝓝 ⟨gaussianReal 0 1, inferInstance⟩) := by
  have h := Polynomial.tendsto_standardizedCoeffDistribution
    (P := fun n => eulerianTilde (n + 1)) (fun n => (isRealRooted_eulerianTilde (n + 1)).2)
    (fun n k => eulerianTilde_nonnegCoeffs (n + 1) k) ?_
  · exact (tendsto_add_atTop_iff_nat 1).mp h
  simp only [coeffVariance_eulerianTilde (Nat.succ_ne_zero _)]
  refine Tendsto.atTop_div_const (by norm_num) (tendsto_atTop_add_const_right _ _ ?_)
  exact tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)

end RealRooted
