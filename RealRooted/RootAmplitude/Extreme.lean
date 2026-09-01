import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Extreme root-gap bounds

Power-sum data for a nonnegative finite family give a lower bound on the ratio
of its two largest entries, and hence a logarithmic lower bound on the
corresponding extreme root gap.
-/

namespace RealRooted.RootAmplitude

noncomputable section

/-- Power-sum bounds imply a square-ratio bound for two distinguished entries. -/
theorem sq_ratio_ge {x0 x1 s1 s2 : ℝ} (hs2 : 0 ≤ s2)
    (hdom : s2 ≤ x0 * s1) (hsum : x0 ^ 2 + x1 ^ 2 ≤ s2) :
    s2 * x1 ^ 2 ≤ (s1 ^ 2 - s2) * x0 ^ 2 := by
  have h1 : s2 * x1 ^ 2 ≤ s2 * (s2 - x0 ^ 2) := by nlinarith
  have h2 : s2 ^ 2 ≤ s1 ^ 2 * x0 ^ 2 := by nlinarith
  nlinarith

/-- A square-ratio bound with a positive denominator gives a ratio lower bound. -/
theorem ratio_sq_ge {x0 x1 s1 s2 c : ℝ} (hx1 : 0 < x1) (hs2 : 0 ≤ s2)
    (hdom : s2 ≤ x0 * s1) (hsum : x0 ^ 2 + x1 ^ 2 ≤ s2)
    (hc : 0 < s1 ^ 2 - s2) (hcbound : c * (s1 ^ 2 - s2) ≤ s2) :
    c ≤ (x0 / x1) ^ 2 := by
  have hkey := sq_ratio_ge hs2 hdom hsum
  have hx1sq : 0 < x1 ^ 2 := by positivity
  rw [div_pow, le_div_iff₀ hx1sq]
  nlinarith [hkey, hcbound, hx1sq]

/-- The coefficient-coordinate form of the square-ratio criterion. -/
theorem ratio_sq_ge_of_coeffs {x0 x1 a0 a1 a2 c : ℝ} (hx1 : 0 < x1)
    (hs2 : 0 ≤ (a1 / a0) ^ 2 - 2 * (a2 / a0))
    (hdom : (a1 / a0) ^ 2 - 2 * (a2 / a0) ≤ x0 * (a1 / a0))
    (hsum : x0 ^ 2 + x1 ^ 2 ≤ (a1 / a0) ^ 2 - 2 * (a2 / a0))
    (he2 : 0 < a2 / a0)
    (hcbound : c * (2 * (a2 / a0)) ≤ (a1 / a0) ^ 2 - 2 * (a2 / a0)) :
    c ≤ (x0 / x1) ^ 2 := by
  refine ratio_sq_ge hx1 hs2 hdom hsum ?_ ?_
  · have h : (a1 / a0) ^ 2 - ((a1 / a0) ^ 2 - 2 * (a2 / a0)) = 2 * (a2 / a0) := by
      ring
    rw [h]
    linarith
  · have h : (a1 / a0) ^ 2 - ((a1 / a0) ^ 2 - 2 * (a2 / a0)) = 2 * (a2 / a0) := by
      ring
    rw [h]
    exact hcbound

/-- A square ratio of at least `exp 4` gives a logarithmic gap of at least two. -/
theorem two_le_log_of_sq_ratio {r : ℝ} (hr : 0 < r)
    (h : Real.exp 4 ≤ r ^ 2) : 2 ≤ Real.log r := by
  have hsq : r ^ 2 = Real.exp (2 * Real.log r) := by
    rw [two_mul, Real.exp_add, Real.exp_log hr]
    ring
  rw [hsq] at h
  have h' := Real.exp_le_exp.mp h
  linarith

open Finset

/-- The sum of squares of a nonnegative finite family is bounded by its
largest entry times its sum. -/
theorem sum_sq_le_max_mul_sum {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (hnn : ∀ i ∈ s, 0 ≤ x i) {i0 : ι} (hmax : ∀ i ∈ s, x i ≤ x i0) :
    ∑ i ∈ s, (x i) ^ 2 ≤ x i0 * ∑ i ∈ s, x i := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum ?_
  intro i hi
  have h1 := hnn i hi
  have h2 := hmax i hi
  nlinarith

/-- Two distinct members contribute at most the full square sum. -/
theorem two_sq_le_sum_sq {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    {i0 i1 : ι} (h0 : i0 ∈ s) (h1 : i1 ∈ s) (hne : i0 ≠ i1) :
    (x i0) ^ 2 + (x i1) ^ 2 ≤ ∑ i ∈ s, (x i) ^ 2 := by
  classical
  have hsub : ({i0, i1} : Finset ι) ⊆ s := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl
    · exact h0
    · exact h1
  have hpair : ∑ i ∈ ({i0, i1} : Finset ι), (x i) ^ 2 = (x i0) ^ 2 + (x i1) ^ 2 :=
    Finset.sum_pair hne
  rw [← hpair]
  refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_
  intro i _ _
  positivity

/-- The extreme-ratio bound for a finite nonnegative family. -/
theorem ratio_sq_ge_of_family {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (hnn : ∀ i ∈ s, 0 ≤ x i) {i0 i1 : ι} (h0 : i0 ∈ s) (h1 : i1 ∈ s) (hne : i0 ≠ i1)
    (hmax : ∀ i ∈ s, x i ≤ x i0) (hx1 : 0 < x i1) {c : ℝ}
    (hlt : 0 < (∑ i ∈ s, x i) ^ 2 - ∑ i ∈ s, (x i) ^ 2)
    (hc : c * ((∑ i ∈ s, x i) ^ 2 - ∑ i ∈ s, (x i) ^ 2) ≤ ∑ i ∈ s, (x i) ^ 2) :
    c ≤ (x i0 / x i1) ^ 2 := by
  classical
  refine ratio_sq_ge hx1 ?_ (sum_sq_le_max_mul_sum s x hnn hmax)
    (two_sq_le_sum_sq s x h0 h1 hne) hlt hc
  refine Finset.sum_nonneg ?_
  intro i _
  positivity

/-- `K n 3^n ≤ 4^n` propagates upward from any index at least three. -/
theorem mul_three_pow_le_four_pow (K : ℝ) (hK : 0 ≤ K) (N : ℕ) (hN : 3 ≤ N)
    (hbase : K * (N : ℝ) * 3 ^ N ≤ 4 ^ N) :
    ∀ n : ℕ, N ≤ n → K * (n : ℝ) * 3 ^ n ≤ 4 ^ n := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => exact hbase
  | succ k hk ih =>
      have hk3 : (3 : ℝ) ≤ (k : ℝ) := by
        have hkk : (3 : ℕ) ≤ k := le_trans hN hk
        exact_mod_cast hkk
      have h3 : (3 : ℝ) ^ (k + 1) = 3 * 3 ^ k := by ring
      have h4 : (4 : ℝ) ^ (k + 1) = 4 * 4 ^ k := by ring
      have hp : (0 : ℝ) < 3 ^ k := by positivity
      have hslack : (0 : ℝ) ≤ K * 3 ^ k * ((k : ℝ) - 3) :=
        mul_nonneg (mul_nonneg hK (le_of_lt hp)) (by linarith)
      push_cast
      rw [h3, h4]
      nlinarith [ih, hslack]

/-- The explicit numerical threshold `exp 4 < 55`. -/
theorem exp_four_lt : Real.exp 4 < 55 := by
  have hb : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have hpos : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have hpow : Real.exp 4 = (Real.exp 1) ^ 4 := by
    rw [← Real.exp_nat_mul]
    norm_num
  have h2 : (Real.exp 1) ^ 2 < 7.3890561 := by nlinarith [hb, hpos]
  have hsq : (0 : ℝ) ≤ (Real.exp 1) ^ 2 := sq_nonneg _
  have h44 : (Real.exp 1) ^ 4 = ((Real.exp 1) ^ 2) ^ 2 := by ring
  rw [hpow, h44]
  nlinarith [h2, hsq]

end

end RealRooted.RootAmplitude
