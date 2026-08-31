import RealRooted.Analysis.PowerTail.Telescoping

/-!
# Quadratic-denominator reciprocal-power tails

Applications of the positive-spacing telescoping bound to the denominators
`(k + 1) (k + 2)` that occur after pairing symmetric terms.
-/

namespace RealRooted.Analysis.PowerTail

open Finset

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The Bernoulli step with spacing two. -/
theorem binom_step {A : K} (hA : 0 < A) (r : ℕ) :
    A ^ (r + 1) + 2 * ((r : K) + 1) * A ^ r ≤ (A + 2) ^ (r + 1) := by
  simpa using binom_step_w (A := A) (w := 2) hA (by norm_num) r

/-- The reciprocal-power step with spacing two. -/
theorem step_ineq {A : K} (hA : 0 < A) (r : ℕ) :
    2 * ((r : K) + 1) / (A + 2) ^ (r + 2)
      ≤ 1 / A ^ (r + 1) - 1 / (A + 2) ^ (r + 1) := by
  simpa using step_ineq_w (A := A) (w := 2) hA (by norm_num) r

/-- The finite reciprocal-power tail with spacing two. -/
theorem sum_le (u : K) (hu : 0 < u) (r N : ℕ) :
    ∑ k ∈ range N, (u / (u + 2 * ((k : K) + 1))) ^ (r + 2)
      ≤ u / (2 * ((r : K) + 1)) := by
  simpa using sum_le_w u 2 hu (by norm_num) r N

/-- The quadratic denominator is bounded by the spacing-two denominator. -/
theorem sum_sq_le (u : K) (hu : 0 < u) (r N : ℕ) :
    ∑ k ∈ range N, (u / (u + ((k : K) + 1) * ((k : K) + 2))) ^ (r + 2)
      ≤ u / (2 * ((r : K) + 1)) := by
  refine le_trans (Finset.sum_le_sum (fun k _ => ?_)) (sum_le u hu r N)
  have hk : (0 : K) ≤ (k : K) := Nat.cast_nonneg k
  have h1 : (0 : K) < u + 2 * ((k : K) + 1) := by linarith
  have h2 : u + 2 * ((k : K) + 1)
      ≤ u + ((k : K) + 1) * ((k : K) + 2) := by
    nlinarith
  have hdiv : u / (u + ((k : K) + 1) * ((k : K) + 2))
      ≤ u / (u + 2 * ((k : K) + 1)) :=
    div_le_div_of_nonneg_left hu.le h1 h2
  have hnn : (0 : K) ≤ u / (u + ((k : K) + 1) * ((k : K) + 2)) := by
    have : (0 : K) < u + ((k : K) + 1) * ((k : K) + 2) := by nlinarith
    positivity
  exact pow_le_pow_left₀ hnn hdiv _

/-- The quadratic reciprocal-power tail is strictly below one in its band. -/
theorem sum_sq_lt_one (u : K) (hu : 0 < u) (r N : ℕ)
    (hlt : u < 2 * ((r : K) + 1)) :
    ∑ k ∈ range N, (u / (u + ((k : K) + 1) * ((k : K) + 2))) ^ (r + 2) < 1 := by
  refine lt_of_le_of_lt (sum_sq_le u hu r N) ?_
  rw [div_lt_one (by positivity)]
  exact hlt

/-- A geometric bound for the quadratic reciprocal-power tail. -/
theorem sum_sq_sharp (u : K) (hu : 0 < u) (r N : ℕ)
    (hcond : u + 2 ≤ 4 * ((r : K) + 1)) :
    ∑ k ∈ range N, (u / (u + ((k : K) + 1) * ((k : K) + 2))) ^ (r + 2)
      ≤ 2 * (u / (u + 2)) ^ (r + 2) := by
  have hvpos : (0 : K) < u + 2 := by linarith
  have hterm : ∀ k ∈ range N,
      (u / (u + ((k : K) + 1) * ((k : K) + 2))) ^ (r + 2)
        ≤ (u / (u + 2)) ^ (r + 2)
            * ((u + 2) / ((u + 2) + 4 * (k : K))) ^ (r + 2) := by
    intro k _
    have hk : (0 : K) ≤ (k : K) := Nat.cast_nonneg k
    have hden : (u + 2) + 4 * (k : K)
        ≤ u + ((k : K) + 1) * ((k : K) + 2) := by
      rcases Nat.eq_zero_or_pos k with rfl | hkpos
      · norm_num
      · have h1 : (1 : K) ≤ (k : K) := by exact_mod_cast hkpos
        nlinarith [h1]
    have hd1 : (0 : K) < (u + 2) + 4 * (k : K) := by linarith
    have hstep : u / (u + ((k : K) + 1) * ((k : K) + 2))
        ≤ u / ((u + 2) + 4 * (k : K)) :=
      div_le_div_of_nonneg_left hu.le hd1 hden
    have hnn : (0 : K) ≤ u / (u + ((k : K) + 1) * ((k : K) + 2)) := by
      have : (0 : K) < u + ((k : K) + 1) * ((k : K) + 2) := by nlinarith [hk]
      positivity
    refine le_trans (pow_le_pow_left₀ hnn hstep _) (le_of_eq ?_)
    rw [← mul_pow]
    congr 1
    field_simp
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.mul_sum]
  have hgeo : ∑ k ∈ range N,
      ((u + 2) / ((u + 2) + 4 * (k : K))) ^ (r + 2) ≤ 2 := by
    cases N with
    | zero => simp
    | succ M =>
        rw [Finset.sum_range_succ']
        have h0 : ((u + 2) / ((u + 2) + 4 * ((0 : ℕ) : K))) ^ (r + 2) = 1 := by
          norm_num
          rw [div_self (ne_of_gt hvpos), one_pow]
        rw [h0]
        have hrest : ∑ k ∈ range M,
            ((u + 2) / ((u + 2) + 4 * (((k : ℕ) + 1 : ℕ) : K))) ^ (r + 2)
              ≤ (u + 2) / (4 * ((r : K) + 1)) := by
          have h := sum_le_w (u + 2) 4 hvpos (by norm_num) r M
          refine le_trans (le_of_eq (Finset.sum_congr rfl (fun k _ => ?_))) h
          push_cast
          ring_nf
        have hle1 : (u + 2) / (4 * ((r : K) + 1)) ≤ 1 := by
          rw [div_le_one (by positivity)]
          exact hcond
        linarith
  have hbase : (0 : K) ≤ (u / (u + 2)) ^ (r + 2) := by positivity
  calc
    (u / (u + 2)) ^ (r + 2)
        * ∑ k ∈ range N, ((u + 2) / ((u + 2) + 4 * (k : K))) ^ (r + 2)
      ≤ (u / (u + 2)) ^ (r + 2) * 2 := mul_le_mul_of_nonneg_left hgeo hbase
    _ = 2 * (u / (u + 2)) ^ (r + 2) := by ring

end RealRooted.Analysis.PowerTail
