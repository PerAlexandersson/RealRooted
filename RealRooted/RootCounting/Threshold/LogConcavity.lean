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
  classical
  have hpositive_j : 0 < p.coeff j := hpositive j (by lia)
  have hdegree_lt : p.natDegree < N + 1 := by rw [hdegree]; lia
  have hjN : j < N + 1 := by lia
  have hnext_t : j + 1 < N + 1 := by lia
  set t : ℕ → ℝ := fun i => p.coeff i * s ^ i with ht
  have hpositive_t : ∀ i, i < N + 1 → 0 < t i := by
    intro i hi
    rw [ht]
    exact mul_pos (hpositive i (Nat.lt_succ_iff.mp hi)) (by positivity)
  have hlog_concave_t : ∀ i, i + 2 < N + 1 →
      t i * t (i + 2) ≤ (t (i + 1)) ^ 2 := by
    intro i hi
    have hlocal := hlog_concave (i + 1) (by lia) (by lia)
    have hsub : i + 1 - 1 = i := by lia
    rw [hsub] at hlocal
    have hsquare : (0 : ℝ) ≤ (s ^ (i + 1)) ^ 2 := by positivity
    calc
      t i * t (i + 2) = (p.coeff i * p.coeff (i + 2)) * (s ^ (i + 1)) ^ 2 := by
        rw [ht]
        simp only
        ring
      _ ≤ (p.coeff (i + 1)) ^ 2 * (s ^ (i + 1)) ^ 2 :=
          mul_le_mul_of_nonneg_right hlocal hsquare
      _ = (t (i + 1)) ^ 2 := by
        rw [ht]
        simp only
        ring
  have hdominates := CoefficientDominance.sum_erase_lt hpositive_t hlog_concave_t hj
    hnext_t hupper hlower
  refine sign_of_dominant hs hdegree_lt hjN hpositive_j ?_
  have habs : ∀ i ∈ (Finset.range (N + 1)).erase j, |p.coeff i| * s ^ i = t i := by
    intro i hi
    have hindex : i < N + 1 :=
      Finset.mem_range.mp (Finset.mem_of_mem_erase hi)
    have hpositive_i : 0 < p.coeff i :=
      hpositive i (Nat.lt_succ_iff.mp hindex)
    rw [abs_of_pos hpositive_i, ht]
  calc
    ∑ k ∈ (Finset.range (N + 1)).erase j, |p.coeff k| * s ^ k
        = ∑ k ∈ (Finset.range (N + 1)).erase j, t k := Finset.sum_congr rfl habs
    _ < t j := hdominates
    _ = |p.coeff j| * s ^ j := by rw [ht, abs_of_pos hpositive_j]

end RealRooted.RootCounting
