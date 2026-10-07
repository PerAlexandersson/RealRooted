import RealRooted.CombinatorialExamples.SturmDerangementsExc
import RealRooted.Mathlib.Probability.CoeffDistribution

/-!
# Excedances of derangements are asymptotically normal

The derangement excedance polynomials `d_n = ∑_{σ} x^{exc σ}`, summed over the derangements of
`[n]`, satisfy `d_{n+3} = X ((n + 2) d_{n+1} + (n + 2) d_{n+2} + (1 - X) d_{n+2}')`.  At `x = 1`
the factor `1 - X` vanishes, and the values `D_n = d_n(1)` are the derangement numbers, with
`D_{n+2} = (n + 2) D_{n+1} + (-1)ⁿ`.  For `n ≥ 2` the coefficient distribution of `d_n` has mean
`n / 2` and variance `(n - 1) / 12 · (1 - (-1)ⁿ / D_n)`.  Since the polynomials are real-rooted,
Harper's theorem gives asymptotic normality of the excedance statistic on derangements.
-/

open Polynomial Filter Topology ProbabilityTheory

namespace RealRooted

private theorem eval_one_sturmDerangementsExc_step (n : ℕ) :
    (sturmDerangementsExc (n + 3)).eval 1 =
      (n + 2) *
        ((sturmDerangementsExc (n + 1)).eval 1 + (sturmDerangementsExc (n + 2)).eval 1) := by
  rw [sturmDerangementsExc_recurrence]
  simp
  ring

private theorem eval_one_derivative_sturmDerangementsExc_step (n : ℕ) :
    (sturmDerangementsExc (n + 3)).derivative.eval 1 =
      (n + 2) * ((sturmDerangementsExc (n + 1)).eval 1 + (sturmDerangementsExc (n + 2)).eval 1) +
        (n + 2) * (sturmDerangementsExc (n + 1)).derivative.eval 1 +
        (n + 1) * (sturmDerangementsExc (n + 2)).derivative.eval 1 := by
  rw [sturmDerangementsExc_recurrence]
  simp [derivative_mul]
  ring

private theorem eval_one_derivative_derivative_sturmDerangementsExc_step (n : ℕ) :
    (sturmDerangementsExc (n + 3)).derivative.derivative.eval 1 =
      2 * ((n + 2) * (sturmDerangementsExc (n + 1)).derivative.eval 1 +
          (n + 1) * (sturmDerangementsExc (n + 2)).derivative.eval 1) +
        (n + 2) * (sturmDerangementsExc (n + 1)).derivative.derivative.eval 1 +
        n * (sturmDerangementsExc (n + 2)).derivative.derivative.eval 1 := by
  rw [sturmDerangementsExc_recurrence]
  simp [derivative_mul]
  ring

/-- The derangement numbers satisfy `D_{n+2} = (n + 2) D_{n+1} + (-1)ⁿ`. -/
theorem eval_one_sturmDerangementsExc_succ_succ (n : ℕ) :
    (sturmDerangementsExc (n + 2)).eval 1 =
      (n + 2) * (sturmDerangementsExc (n + 1)).eval 1 + (-1) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [eval_one_sturmDerangementsExc_step, ih]
    push_cast
    ring

theorem one_le_eval_one_sturmDerangementsExc (n : ℕ) :
    1 ≤ (sturmDerangementsExc (n + 2)).eval 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [eval_one_sturmDerangementsExc_succ_succ (n + 1)]
    rcases neg_one_pow_eq_or ℝ (n + 1) with h | h <;> rw [h] <;> push_cast <;>
      nlinarith [n.cast_nonneg (α := ℝ)]

/-- The coefficient distribution of `sturmDerangementsExc n` has mean `n / 2`. -/
theorem eval_one_derivative_sturmDerangementsExc : ∀ n : ℕ,
    (sturmDerangementsExc n).derivative.eval 1 = n / 2 * (sturmDerangementsExc n).eval 1
  | 0 => by simp
  | 1 => by simp
  | 2 => by simp
  | n + 3 => by
    rw [eval_one_derivative_sturmDerangementsExc_step, eval_one_derivative_sturmDerangementsExc,
      eval_one_derivative_sturmDerangementsExc (n + 2), eval_one_sturmDerangementsExc_step]
    push_cast
    ring

theorem eval_one_derivative_derivative_sturmDerangementsExc : ∀ n : ℕ,
    (sturmDerangementsExc (n + 1)).derivative.derivative.eval 1 =
      (n / 12 + (n + 1) ^ 2 / 4 - (n + 1) / 2) * (sturmDerangementsExc (n + 1)).eval 1 -
        n * (-1) ^ (n + 1) / 12
  | 0 => by simp
  | 1 => by norm_num
  | n + 2 => by
    rw [eval_one_derivative_derivative_sturmDerangementsExc_step,
      eval_one_derivative_derivative_sturmDerangementsExc n,
      eval_one_derivative_derivative_sturmDerangementsExc (n + 1),
      eval_one_derivative_sturmDerangementsExc (n + 1),
      eval_one_derivative_sturmDerangementsExc (n + 2), eval_one_sturmDerangementsExc_step,
      eval_one_sturmDerangementsExc_succ_succ n]
    push_cast
    ring

/-- For `n ≥ 2` the coefficient distribution of `sturmDerangementsExc n` has variance
`(n - 1) / 12 · (1 - (-1)ⁿ / D_n)`, written here at `n + 2`. -/
theorem coeffVariance_sturmDerangementsExc (n : ℕ) :
    (sturmDerangementsExc (n + 2)).coeffVariance =
      (n + 1) / 12 * (1 - (-1) ^ n / (sturmDerangementsExc (n + 2)).eval 1) := by
  have hpos : (sturmDerangementsExc (n + 2)).eval 1 ≠ 0 :=
    (zero_lt_one.trans_le (one_le_eval_one_sturmDerangementsExc n)).ne'
  rw [Polynomial.coeffVariance, Polynomial.coeffMean, eval_one_derivative_sturmDerangementsExc,
    eval_one_derivative_derivative_sturmDerangementsExc (n + 1), mul_div_cancel_right₀ _ hpos]
  field_simp
  push_cast
  ring

/-- **Excedances of derangements are asymptotically normal**: the standardized coefficient
distributions of the derangement excedance polynomials converge weakly to the standard normal
law. -/
theorem tendsto_standardizedCoeffDistribution_sturmDerangementsExc :
    Tendsto (fun n => (sturmDerangementsExc n).standardizedCoeffDistribution) atTop
      (𝓝 ⟨gaussianReal 0 1, inferInstance⟩) := by
  have h := Polynomial.tendsto_standardizedCoeffDistribution
    (P := fun n => sturmDerangementsExc (n + 3))
    (fun n => (isRealRooted_sturmDerangementsExc (n + 3) (by lia)).2)
    (fun n k => sturmDerangementsExc_nonnegCoeffs (n + 3) k) ?_
  · exact (tendsto_add_atTop_iff_nat 3).mp h
  refine tendsto_atTop_mono (fun n => ?_)
    (tendsto_natCast_atTop_atTop.atTop_div_const (by norm_num : (0 : ℝ) < 24))
  have hv : 2 ≤ (sturmDerangementsExc (n + 3)).eval 1 := by
    rw [eval_one_sturmDerangementsExc_succ_succ (n + 1)]
    have := one_le_eval_one_sturmDerangementsExc n
    rcases neg_one_pow_eq_or ℝ (n + 1) with h | h <;> rw [h] <;> push_cast <;>
      nlinarith [n.cast_nonneg (α := ℝ)]
  have hq : (-1 : ℝ) ^ (n + 1) / (sturmDerangementsExc (n + 3)).eval 1 ≤ 1 / 2 := by
    rw [div_le_iff₀ (by linarith)]
    rcases neg_one_pow_eq_or ℝ (n + 1) with h | h <;> rw [h] <;> linarith
  simp only [coeffVariance_sturmDerangementsExc (n + 1)]
  push_cast
  nlinarith [n.cast_nonneg (α := ℝ)]

end RealRooted
