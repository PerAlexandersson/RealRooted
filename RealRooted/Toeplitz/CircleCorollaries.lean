module

public import RealRooted.Toeplitz.CircleCriterion
import RealRooted.Mathlib.RingTheory.Polynomial.Chebyshev.Bounds
import Mathlib.Tactic

/-!
# Coefficient corollaries of the circle criterion

We derive the constant four-term criterion, the odd five-diagonal criterion, and the
uniform perturbation criterion from the same circle energy theorem. The endpoints of
all three coefficient regions are included. Source: unpublished manuscript,
RealRooted issues #2164 (consolidation of 2026-11-01), #2102, and #2147.
-/

public section

open Polynomial
open scoped BigOperators

noncomputable section

namespace RealRooted.Toeplitz.Circle

/-- The circle condition is exactly the consolidated certificate
`-1 + ∑ c_j R^(j+1) U_(j-1)(u) ≥ 0`. Its index-zero summand vanishes. -/
theorem circleNonneg_iff_scaled (b : ℕ →₀ ℝ) (R : ℝ) (hR : 0 < R) :
    CircleNonneg b R ↔ ∀ u ∈ Set.Icc (-1 : ℝ) 1,
      0 ≤ -1 + b.sum (fun k a => a * R ^ (k + 1) *
        (Chebyshev.U ℝ ((k : ℤ) - 1)).eval u) := by
  have heq (u : ℝ) : R * (circlePolynomial b R).eval u =
      -1 + b.sum (fun k a => a * R ^ (k + 1) *
        (Chebyshev.U ℝ ((k : ℤ) - 1)).eval u) := by
    simp only [circlePolynomial, Finsupp.sum, eval_add, eval_neg, eval_C,
      eval_finsetSum, eval_mul, mul_add, mul_neg, mul_inv_cancel₀ hR.ne', Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    rw [pow_succ]
    ring_nf
  simp only [CircleNonneg, ← heq, mul_nonneg_iff_of_pos_left hR]

private lemma circlePolynomial_four_eval (c a d R u : ℝ) :
    (circlePolynomial (Finsupp.single 0 c + Finsupp.single 1 a +
      Finsupp.single 2 d) R).eval u = -R⁻¹ + a * R + 2 * d * R ^ 2 * u := by
  unfold circlePolynomial
  rw [Finsupp.sum_add_index (by intros; simp) (by intros; simp [add_mul]),
    Finsupp.sum_add_index (by intros; simp) (by intros; simp [add_mul])]
  simp
  ring_nf

/-- A radius satisfying the scalar cubic barrier certifies the four-term family. -/
theorem circleNonneg_four_of_radius (c a d R : ℝ) (hR : 0 < R)
    (h : 1 ≤ a * R ^ 2 - 2 * |d| * R ^ 3) :
    CircleNonneg (Finsupp.single 0 c + Finsupp.single 1 a + Finsupp.single 2 d) R := by
  intro u hu
  rw [circlePolynomial_four_eval]
  have hdu : -|d| ≤ d * u := by
    have := abs_mul d u
    have hu' : |u| ≤ 1 := abs_le.mpr hu
    have : |d * u| ≤ |d| := by
      rw [abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg d) hu'
    exact (abs_le.mp this).1
  have hmul : 0 ≤ R * (-R⁻¹ + a * R + 2 * d * R ^ 2 * u) := by
    have hi : R * R⁻¹ = 1 := mul_inv_cancel₀ hR.ne'
    nlinarith [mul_nonneg (by nlinarith : 0 ≤ d * u + |d|)
      (by positivity : 0 ≤ 2 * R ^ 3)]
  exact nonneg_of_mul_nonneg_right hmul hR

private lemma exists_radius_four {a d : ℝ} (ha : 0 < a) (h : 27 * d ^ 2 ≤ a ^ 3) :
    ∃ R : ℝ, 0 < R ∧ 1 ≤ a * R ^ 2 - 2 * |d| * R ^ 3 := by
  by_cases hd : d = 0
  · refine ⟨(a + 1) / a, div_pos (by linarith) ha, ?_⟩
    simp only [hd, abs_zero, mul_zero, zero_mul, sub_zero]
    apply (mul_le_mul_iff_right₀ ha).mp
    have hid : a * ((a + 1) / a) ^ 2 * a = (a + 1) ^ 2 := by
      field_simp
    nlinarith [sq_nonneg a]
  · have hdpos : 0 < |d| := abs_pos.mpr hd
    refine ⟨a / (3 * |d|), div_pos ha (by positivity), ?_⟩
    have hs : |d| ^ 2 = d ^ 2 := sq_abs d
    have hid : (a * (a / (3 * |d|)) ^ 2 - 2 * |d| * (a / (3 * |d|)) ^ 3) *
        (27 * d ^ 2) = a ^ 3 := by
      rw [← hs]
      field_simp
      ring_nf
    have hden : 0 < 27 * d ^ 2 := by positivity
    nlinarith

/-- Under `a³ ≥ 27d²` and `a > 0`, all consecutive constant four-term rows
interlace and have simple real roots, including equality in the cubic bound. -/
theorem strictInterl_four_of_cubic (c a d : ℝ) (ha : 0 < a)
    (h : 27 * d ^ 2 ≤ a ^ 3) (n : ℕ) :
    StrictInterl
      (row (Finsupp.single 0 c + Finsupp.single 1 a + Finsupp.single 2 d) n)
      (row (Finsupp.single 0 c + Finsupp.single 1 a + Finsupp.single 2 d) (n + 1)) ∧
    HasSimpleRoots
      (row (Finsupp.single 0 c + Finsupp.single 1 a + Finsupp.single 2 d) n) ∧
    HasSimpleRoots
      (row (Finsupp.single 0 c + Finsupp.single 1 a + Finsupp.single 2 d) (n + 1)) := by
  obtain ⟨R, hR, hbarrier⟩ := exists_radius_four ha h
  exact strictInterl_of_circleNonneg _ R hR (circleNonneg_four_of_radius c a d R hR hbarrier) n

private lemma row_single_zero (c : ℝ) (n : ℕ) :
    row (Finsupp.single 0 c) n = (X - C c) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [row_succ]
    simp [Finsupp.sum_single_index, ih, pow_succ]
    ring_nf

/-- Every constant four-term row splits under `a³ ≥ 27d²`. The degenerate
case `a = d = 0` is included, without a simplicity assertion. -/
theorem splits_four_of_cubic (c a d : ℝ) (h : 27 * d ^ 2 ≤ a ^ 3) (n : ℕ) :
    (row (Finsupp.single 0 c + Finsupp.single 1 a + Finsupp.single 2 d) n).Splits := by
  have ha : 0 ≤ a := by
    by_contra hn
    have : a ^ 3 < 0 := by nlinarith [sq_pos_of_neg (lt_of_not_ge hn)]
    nlinarith [sq_nonneg d]
  rcases ha.eq_or_lt with ha | ha
  · have hd : d = 0 := by rw [← ha] at h; nlinarith [sq_nonneg d]
    simp only [← ha, hd, Finsupp.single_zero, add_zero, row_single_zero]
    exact (Splits.X_sub_C c).pow n
  · exact (strictInterl_four_of_cubic c a d ha h n).1.1.2

private lemma circlePolynomial_odd_eval (c₀ a c R u : ℝ) :
    (circlePolynomial (Finsupp.single 0 c₀ + Finsupp.single 1 a -
      Finsupp.single 3 c) R).eval u = -R⁻¹ + a * R - c * R ^ 3 * (4 * u ^ 2 - 1) := by
  unfold circlePolynomial
  rw [sub_eq_add_neg, ← Finsupp.single_neg]
  rw [Finsupp.sum_add_index (by intros; simp) (by intros; simp [add_mul]),
    Finsupp.sum_add_index (by intros; simp) (by intros; simp [add_mul])]
  simp [-Finsupp.single_neg, Chebyshev.U_two]
  ring_nf

/-- The odd five-diagonal family satisfies the circle condition at a quadratic barrier. -/
theorem circleNonneg_odd_of_radius (c₀ a c R : ℝ) (hc : 0 ≤ c) (hR : 0 < R)
    (h : 1 ≤ a * R ^ 2 - 3 * c * R ^ 4) :
    CircleNonneg (Finsupp.single 0 c₀ + Finsupp.single 1 a - Finsupp.single 3 c) R := by
  intro u hu
  rw [circlePolynomial_odd_eval]
  have hu2 : u ^ 2 ≤ 1 := by nlinarith [hu.1, hu.2]
  have hi : R * R⁻¹ = 1 := mul_inv_cancel₀ hR.ne'
  apply nonneg_of_mul_nonneg_left (b := R) _ hR
  nlinarith [mul_nonneg (by positivity : 0 ≤ 4 * c * R ^ 4)
    (by linarith : 0 ≤ 1 - u ^ 2)]

/-- For `c > 0` and `a ≥ √(12c)`, the odd five-diagonal rows have simple real
roots and consecutive interlacing, including the sharp boundary. -/
theorem strictInterl_odd_of_sqrt (c₀ a c : ℝ) (hc : 0 < c)
    (h : Real.sqrt (12 * c) ≤ a) (n : ℕ) :
    StrictInterl
      (row (Finsupp.single 0 c₀ + Finsupp.single 1 a - Finsupp.single 3 c) n)
      (row (Finsupp.single 0 c₀ + Finsupp.single 1 a - Finsupp.single 3 c) (n + 1)) ∧
    HasSimpleRoots
      (row (Finsupp.single 0 c₀ + Finsupp.single 1 a - Finsupp.single 3 c) n) ∧
    HasSimpleRoots
      (row (Finsupp.single 0 c₀ + Finsupp.single 1 a - Finsupp.single 3 c) (n + 1)) := by
  have ha : 0 < a := lt_of_lt_of_le (Real.sqrt_pos.mpr (by positivity)) h
  have ha2 : 12 * c ≤ a ^ 2 := (Real.sqrt_le_iff).mp h |>.2
  let R := Real.sqrt (2 / a)
  have hR : 0 < R := Real.sqrt_pos.mpr (div_pos (by norm_num) ha)
  have hR2 : R ^ 2 = 2 / a := Real.sq_sqrt (by positivity)
  have hid : a * R ^ 2 = 2 := by rw [hR2]; field_simp
  have hbarrier : 1 ≤ a * R ^ 2 - 3 * c * R ^ 4 := by
    have heq : a ^ 2 * R ^ 4 = 4 := by nlinarith [sq_nonneg (a * R ^ 2 - 2)]
    have := mul_nonneg (sub_nonneg.mpr ha2) (by positivity : 0 ≤ R ^ 4)
    nlinarith
  exact strictInterl_of_circleNonneg _ R hR
    (circleNonneg_odd_of_radius c₀ a c R hc.le hR hbarrier) n

/-- The first uniform perturbation inequality alone implies the circle condition.
The constant coefficient translates roots and is unrestricted. -/
theorem circleNonneg_of_weighted_abs_sum (b : ℕ →₀ ℝ) (R : ℝ)
    (hR : 0 < R) (h : R⁻¹ ≤ b 1 * R -
      ∑ k ∈ b.support.erase 1, (k : ℝ) * |b k| * R ^ k) : CircleNonneg b R := by
  intro u hu
  have huabs : |u| ≤ 1 := abs_le.mpr hu
  have hbound (k : ℕ) :
      -(k : ℝ) * |b k| * R ^ k ≤
        b k * R ^ k * (Chebyshev.U ℝ ((k : ℤ) - 1)).eval u := by
    cases k with
    | zero => simp
    | succ k =>
      have hb := Chebyshev.abs_eval_U_le (K := ℝ) k huabs
      have hab : |b (k + 1) * R ^ (k + 1) * (Chebyshev.U ℝ (k : ℤ)).eval u| ≤
          (k + 1 : ℝ) * |b (k + 1)| * R ^ (k + 1) := by
        rw [abs_mul, abs_mul, abs_of_pos (pow_pos hR _)]
        have := mul_le_mul_of_nonneg_left hb
          (by positivity : 0 ≤ |b (k + 1)| * R ^ (k + 1))
        nlinarith
      convert (abs_le.mp hab).1 using 1 <;> push_cast <;> ring_nf
  have hs := Finset.sum_le_sum (s := b.support.erase 1) (fun k _ => hbound k)
  have heq : b.sum (fun k a => a * R ^ k * (Chebyshev.U ℝ ((k : ℤ) - 1)).eval u) =
      b 1 * R + ∑ k ∈ b.support.erase 1,
        b k * R ^ k * (Chebyshev.U ℝ ((k : ℤ) - 1)).eval u := by
    by_cases hb1 : 1 ∈ b.support
    · rw [Finsupp.sum, ← Finset.sum_erase_add _ _ hb1]
      simp [add_comm]
    · have hbzero : b 1 = 0 := Finsupp.notMem_support_iff.mp hb1
      simp [Finsupp.sum, hbzero]
  change 0 ≤ (circlePolynomial b R).eval u
  simp only [circlePolynomial, Finsupp.sum, eval_add, eval_neg, eval_C,
    eval_finsetSum, eval_mul]
  rw [show (∑ x ∈ b.support, b x * R ^ x * (Chebyshev.U ℝ ((x : ℤ) - 1)).eval u) =
    b 1 * R + ∑ x ∈ b.support.erase 1,
      b x * R ^ x * (Chebyshev.U ℝ ((x : ℤ) - 1)).eval u from heq]
  have hsneg : (∑ k ∈ b.support.erase 1, -(k : ℝ) * |b k| * R ^ k) =
      -(∑ k ∈ b.support.erase 1, (k : ℝ) * |b k| * R ^ k) := by
    simp [← Finset.sum_neg_distrib]
  rw [hsneg] at hs
  linarith

/-- Uniformly small signed tails give simple real roots and consecutive interlacing.
This strengthens the original perturbation statement: its second inequality is unnecessary. -/
theorem strictInterl_of_uniform_perturbation (b : ℕ →₀ ℝ) (R : ℝ)
    (hR : 1 < R) (hb : b 1 = 1)
    (h : (∑ k ∈ b.support.erase 1, (k : ℝ) * |b k| * R ^ (k + 1)) ≤ R ^ 2 - 1)
    (n : ℕ) : StrictInterl (row b n) (row b (n + 1)) ∧
      HasSimpleRoots (row b n) ∧ HasSimpleRoots (row b (n + 1)) := by
  have hRpos : 0 < R := by linarith
  apply strictInterl_of_circleNonneg b R hRpos
  apply circleNonneg_of_weighted_abs_sum b R hRpos
  rw [hb]
  have hs : R * (∑ k ∈ b.support.erase 1, (k : ℝ) * |b k| * R ^ k) =
      ∑ k ∈ b.support.erase 1, (k : ℝ) * |b k| * R ^ (k + 1) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [pow_succ]
    ring_nf
  have hi : R * R⁻¹ = 1 := mul_inv_cancel₀ hRpos.ne'
  apply (mul_le_mul_iff_right₀ hRpos).mp
  nlinarith

end RealRooted.Toeplitz.Circle
