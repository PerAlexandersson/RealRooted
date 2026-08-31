import RealRooted.Analysis.PowerTail.Bernoulli

/-!
# Finite telescoping bounds for reciprocal-power tails

This layer turns the positive-spacing one-step inequality into a bound for a
finite reciprocal-power tail.
-/

namespace RealRooted.Analysis.PowerTail

open Finset

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- A finite reciprocal-power tail is bounded by its telescoping first term. -/
theorem sum_le_w (v w : K) (hv : 0 < v) (hw : 0 < w) (r N : ℕ) :
    ∑ k ∈ range N, (v / (v + w * ((k : K) + 1))) ^ (r + 2)
      ≤ v / (w * ((r : K) + 1)) := by
  have hApos : ∀ k : ℕ, (0 : K) < v + w * (k : K) := by
    intro k
    have : (0 : K) ≤ w * (k : K) := by positivity
    linarith
  set f : ℕ → K := fun k => 1 / (v + w * (k : K)) ^ (r + 1) with hf
  have hrpos : (0 : K) < w * ((r : K) + 1) := by positivity
  have hvpow : (0 : K) < v ^ (r + 2) := by positivity
  have hterm : ∀ k ∈ range N,
      (v / (v + w * ((k : K) + 1))) ^ (r + 2)
        ≤ v ^ (r + 2) / (w * ((r : K) + 1)) * (f k - f (k + 1)) := by
    intro k _
    have hA := hApos k
    have hstep' : w * ((r : K) + 1) / (v + w * ((k : K) + 1)) ^ (r + 2)
        ≤ 1 / (v + w * (k : K)) ^ (r + 1)
          - 1 / (v + w * ((k : K) + 1)) ^ (r + 1) := by
      have h := step_ineq_w hA hw r
      rwa [show v + w * (k : K) + w = v + w * ((k : K) + 1) by ring] at h
    have hfk : f k = 1 / (v + w * (k : K)) ^ (r + 1) := rfl
    have hfk1 : f (k + 1) = 1 / (v + w * ((k : K) + 1)) ^ (r + 1) := by
      simp only [hf, Nat.cast_add, Nat.cast_one]
    rw [hfk, hfk1]
    have hc : (0 : K) < v ^ (r + 2) / (w * ((r : K) + 1)) := div_pos hvpow hrpos
    have hmul := mul_le_mul_of_nonneg_left hstep' hc.le
    refine le_trans (le_of_eq ?_) hmul
    rw [div_pow]
    field_simp
  have hsum := Finset.sum_le_sum hterm
  rw [← Finset.mul_sum, Finset.sum_range_sub' f N] at hsum
  refine le_trans hsum ?_
  have hfN : 0 < f N := by
    have := hApos N
    simp only [hf]
    positivity
  have hf0 : f 0 = 1 / v ^ (r + 1) := by simp [hf]
  have hc : (0 : K) < v ^ (r + 2) / (w * ((r : K) + 1)) := div_pos hvpow hrpos
  have hbound : v ^ (r + 2) / (w * ((r : K) + 1)) * (f 0 - f N)
      ≤ v ^ (r + 2) / (w * ((r : K) + 1)) * f 0 :=
    mul_le_mul_of_nonneg_left (by linarith) hc.le
  refine le_trans hbound (le_of_eq ?_)
  rw [hf0, pow_succ]
  field_simp

end RealRooted.Analysis.PowerTail
