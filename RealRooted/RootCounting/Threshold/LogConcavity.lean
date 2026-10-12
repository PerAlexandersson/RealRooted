import RealRooted.CoefficientDominance.LogConcavity
import RealRooted.RootCounting.Threshold.Basic

/-!
# Signed evaluation from log-concave coefficient dominance

Positive log-concavity and two small adjacent term ratios make the central
coefficient term dominant. This converts that coefficient certificate into the
signed evaluation needed by thresholded root counting.
-/

namespace RealRooted.RootCounting

open Polynomial

/-- A positive log-concave coefficient sequence fixes the sign at `-s` when
each adjacent coefficient term is less than one third of the central term. -/
theorem sign_of_dominant_logConcave {p : ℝ[X]} {N : ℕ} (hdegree : p.natDegree = N)
    (hpositive : ∀ i, i ≤ N → 0 < p.coeff i)
    (hlog_concave : ∀ i, 0 < i → i < N →
      p.coeff (i - 1) * p.coeff (i + 1) ≤ (p.coeff i) ^ 2)
    {s : ℝ} (hs : 0 < s) (j : ℕ) (hj : 1 ≤ j) (hnext : j + 1 ≤ N)
    (hupper : (p.coeff (j + 1) * s ^ (j + 1)) / (p.coeff j * s ^ j) < 1 / 3)
    (hlower : (p.coeff (j - 1) * s ^ (j - 1)) / (p.coeff j * s ^ j) < 1 / 3) :
    0 < (-1 : ℝ) ^ j * p.eval (-s) := by
  have hpositive_j : 0 < p.coeff j := hpositive j (by lia)
  have hdegree_lt : p.natDegree < N + 1 := by rw [hdegree]; lia
  have hjN : j < N + 1 := by lia
  refine sign_of_dominant hs hdegree_lt hjN hpositive_j ?_
  exact CoefficientDominance.sum_abs_coeff_mul_pow_erase_lt_of_logConcave hpositive
    hlog_concave hs j hj hnext hupper hlower

/-- Division-free adjacent-term bounds imply the hypotheses of
`sign_of_dominant_logConcave`. -/
theorem sign_of_dominant_logConcave_of_adjacent_bounds
    {p : ℝ[X]} {N : ℕ} (hdegree : p.natDegree = N)
    (hpositive : ∀ i, i ≤ N → 0 < p.coeff i)
    (hlog_concave : ∀ i, 0 < i → i < N →
      p.coeff (i - 1) * p.coeff (i + 1) ≤ (p.coeff i) ^ 2)
    (j : ℕ) (hj : 1 ≤ j) (hnext : j + 1 ≤ N)
    {s : ℝ} (hs : 0 < s)
    (hupper : 3 * p.coeff (j + 1) * s < p.coeff j)
    (hlower : 3 * p.coeff (j - 1) < p.coeff j * s) :
    0 < (-1 : ℝ) ^ j * p.eval (-s) := by
  have hpositive_j : 0 < p.coeff j := hpositive j (by lia)
  have hden : (0 : ℝ) < p.coeff j * s ^ j := by positivity
  refine sign_of_dominant_logConcave hdegree hpositive hlog_concave hs j hj hnext ?_ ?_
  · rw [div_lt_div_iff₀ hden (by norm_num)]
    have hpow : s ^ (j + 1) = s ^ j * s := by ring
    rw [hpow]
    nlinarith [hupper, pow_pos hs j, hpositive_j]
  · rw [div_lt_div_iff₀ hden (by norm_num)]
    have hpow : s ^ j = s ^ (j - 1) * s := by
      rw [← pow_succ]
      congr 1
      lia
    rw [hpow]
    nlinarith [hlower, pow_pos hs (j - 1), hpositive_j]

end RealRooted.RootCounting
