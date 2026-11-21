/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import RealRooted.CombinatorialExamples.CaoFu.TracePolynomial
public import RealRooted.CombinatorialExamples.CaoFu.Remainder
import RealRooted.CombinatorialExamples.CaoFu.SineBound
import RealRooted.CombinatorialExamples.CaoFu.Bounds
import Mathlib.Analysis.Normed.Group.InfiniteSum
import RealRooted.Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
import Mathlib.Tactic

/-!
# The centered disk bound for the Cao--Fu trace polynomial

We assemble the principal-part estimates for Cao--Fu,
arXiv:2610.40496v1, Lemma 3.2 and Theorem 1.1. The parameter `n` denotes
cosecant rank minus one. All series comparisons are absolutely convergent.
-/

public section
noncomputable section
open Finset Polynomial

namespace RealRooted.CaoFu

private theorem summable_odd_poles (j : ℕ) :
    Summable (fun k : ℕ => (2 / ((2 * (k : ℝ) + 1) * Real.pi)) ^ (2 * (j + 1))) := by
  apply (summable_nat_add_iff 1).mp
  refine ((RealRooted.CenteredEulerian.summable_sSeq (s := 2 * (j + 1)) (by lia)).mul_left
    ((2 / Real.pi) ^ (2 * (j + 1)))).congr fun k => ?_
  dsimp [RealRooted.CenteredEulerian.sSeq]
  push_cast
  rw [← mul_pow]
  congr 1
  field_simp
  ring

private theorem principalPart_odd_eq (n : ℕ) (c : ℂ) (k : ℕ) :
    principalPart n ((2 * (k : ℂ) + 1) * (Real.pi / (2 * c))) =
      ∑ j ∈ range (n + 1), (principalCoeff n j : ℂ) * c ^ (2 * (j + 1)) *
        ((2 / ((2 * (k : ℝ) + 1) * Real.pi)) ^ (2 * (j + 1)) : ℝ) := by
  unfold principalPart
  apply sum_congr rfl
  intro j _
  push_cast
  rw [← mul_div_assoc, div_pow, div_div_eq_mul_div, mul_pow, div_pow]
  ring

private theorem summable_principalPart_odd (n : ℕ) (c : ℂ) :
    Summable (fun k : ℕ =>
      principalPart n ((2 * (k : ℂ) + 1) * (Real.pi / (2 * c)))) := by
  simp only [principalPart_odd_eq]
  apply summable_sum
  intro j _
  exact (Complex.summable_ofReal.mpr (summable_odd_poles j)).mul_left _

/-- The cosecant polynomial is the sum of its principal parts at the odd multiples. -/
theorem cosecantPolynomial_eval_eq_tsum_principalPart (n : ℕ) (c : ℂ) :
    ((cosecantPolynomial n).map (algebraMap ℝ ℂ)).eval c =
      2 * ∑' k : ℕ, principalPart n ((2 * (k : ℂ) + 1) * (Real.pi / (2 * c))) := by
  rw [show (∑' k : ℕ, principalPart n ((2 * (k : ℂ) + 1) *
      (Real.pi / (2 * c)))) = ∑ j ∈ range (n + 1),
      (principalCoeff n j : ℂ) * c ^ (2 * (j + 1)) *
        ∑' k : ℕ, (((2 / ((2 * (k : ℝ) + 1) * Real.pi)) ^
          (2 * (j + 1)) : ℝ) : ℂ) by
    simp only [principalPart_odd_eq]
    rw [Summable.tsum_finsetSum (fun j _ =>
      (Complex.summable_ofReal.mpr (summable_odd_poles j)).mul_left _)]
    simp only [tsum_mul_left]]
  simp only [cosecantPolynomial, Polynomial.map_sum, Polynomial.map_mul,
    Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X, Polynomial.eval_finsetSum,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, mul_sum]
  apply sum_congr rfl
  intro j _
  have h := congrArg Complex.ofReal (tangentWeight_eq_odd_poles j)
  rw [Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_tsum] at h
  push_cast at h ⊢
  change (principalCoeff n j : ℂ) * (tangentWeight j : ℂ) * c ^ (2 * (j + 1)) = _
  rw [h]
  ring

private theorem pow_le_max_endpoints {t : ℝ} (ht : 0 ≤ t) {j r : ℕ}
    (hj : 1 ≤ j) (hjr : j ≤ r) : t ^ j ≤ max t (t ^ r) := by
  by_cases ht1 : t ≤ 1
  · apply le_max_of_le_left
    simpa using pow_le_pow_of_le_one ht ht1 hj
  · apply le_max_of_le_right
    exact pow_le_pow_right₀ (by linarith) hjr

private theorem norm_principalPart_odd_le (n : ℕ) (c : ℂ) (k : ℕ) :
    ‖principalPart n ((2 * (k : ℂ) + 1) * (Real.pi / (2 * c)))‖ ≤
      (1 / 2 : ℝ) * max (Complex.normSq c / (2 * (k : ℝ) + 1) ^ 2)
        ((Complex.normSq c / (2 * (k : ℝ) + 1) ^ 2) ^ (n + 1)) := by
  let t := Complex.normSq c / (2 * (k : ℝ) + 1) ^ 2
  have ht : 0 ≤ t := div_nonneg (Complex.normSq_nonneg c) (sq_nonneg _)
  rw [principalPart_odd_eq]
  calc
    _ ≤ ∑ j ∈ range (n + 1), ‖(principalCoeff n j : ℂ) * c ^ (2 * (j + 1)) *
        ((2 / ((2 * (k : ℝ) + 1) * Real.pi)) ^ (2 * (j + 1)) : ℝ)‖ := norm_sum_le _ _
    _ = ∑ j ∈ range (n + 1),
        (principalCoeff n j * (2 / Real.pi) ^ (2 * (j + 1))) * t ^ (j + 1) := by
      apply sum_congr rfl
      intro j _
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (principalCoeff_nonneg n j),
        abs_of_nonneg (by positivity), norm_pow]
      have hratio : ‖c‖ ^ 2 * (2 / ((2 * (k : ℝ) + 1) * Real.pi)) ^ 2 =
          (2 / Real.pi) ^ 2 * (‖c‖ ^ 2 / (2 * (k : ℝ) + 1) ^ 2) := by
        field_simp
      dsimp [t]
      rw [Complex.normSq_eq_norm_sq]
      rw [mul_assoc, show ‖c‖ ^ (2 * (j + 1)) *
          (2 / ((2 * (k : ℝ) + 1) * Real.pi)) ^ (2 * (j + 1)) =
          (‖c‖ ^ 2 * (2 / ((2 * (k : ℝ) + 1) * Real.pi)) ^ 2) ^ (j + 1) by
        rw [mul_pow, pow_mul, pow_mul]]
      rw [hratio, mul_pow, ← pow_mul]
      ring
    _ ≤ (∑ j ∈ range (n + 1), principalCoeff n j * (2 / Real.pi) ^ (2 * (j + 1))) *
        max t (t ^ (n + 1)) := by
      rw [sum_mul]
      apply sum_le_sum
      intro j hj
      apply mul_le_mul_of_nonneg_left
        (pow_le_max_endpoints ht (by lia) (by have := mem_range.mp hj; lia))
      exact mul_nonneg (principalCoeff_nonneg n j) (by positivity)
    _ ≤ (1 / 2 : ℝ) * max t (t ^ (n + 1)) :=
      mul_le_mul_of_nonneg_right (sum_principalCoeff_two_div_pi_pow_le n)
        (le_max_of_le_left ht)

private theorem summable_max_tail {r : ℕ} (hr : 3 ≤ r) {w : ℝ} (hw : 0 ≤ w) :
    Summable (fun k : ℕ => max (w / (2 * ((k : ℝ) + 1) + 1) ^ 2)
      ((w / (2 * ((k : ℝ) + 1) + 1) ^ 2) ^ r)) := by
  have ha : Summable (fun k : ℕ => w / (2 * ((k : ℝ) + 1) + 1) ^ 2) := by
    simpa only [div_eq_mul_inv, one_mul] using
      (summable_odd_inv_sq (a := 1) (by norm_num)).mul_left w
  have hb : Summable (fun k : ℕ => (w / (2 * ((k : ℝ) + 1) + 1) ^ 2) ^ r) := by
    convert (summable_odd_power hr).mul_left ((w / 9) ^ r) using 1
    funext k
    rw [← mul_pow]
    congr 1
    ring
  apply Summable.of_nonneg_of_le (fun k => le_max_of_le_left (div_nonneg hw (sq_nonneg _)))
    (fun k => ?_) (ha.add hb)
  exact max_le (le_add_of_nonneg_right (by positivity))
    (le_add_of_nonneg_left (div_nonneg hw (sq_nonneg _)))

private theorem norm_principalPart_tail_le {n : ℕ} (hn : 2 ≤ n) (c : ℂ) :
    ‖∑' k : ℕ, principalPart n
      ((2 * ((k : ℂ) + 1) + 1) * (Real.pi / (2 * c)))‖ ≤
      (1 / 2 : ℝ) * (Complex.normSq c / 4 +
        (23 / 20 : ℝ) * (Complex.normSq c / 9) ^ (n + 1)) := by
  have hr : 3 ≤ n + 1 := by lia
  have hw := Complex.normSq_nonneg c
  have hs := (summable_max_tail hr hw).mul_left (1 / 2 : ℝ)
  have h := tsum_of_norm_bounded
    (f := fun k : ℕ => principalPart n
      ((2 * ((k : ℂ) + 1) + 1) * (Real.pi / (2 * c)))) hs.hasSum (fun k => ?_)
  · rw [tsum_mul_left] at h
    exact h.trans (mul_le_mul_of_nonneg_left (tsum_max_odd_le hr hw) (by norm_num))
  · simpa only [Nat.cast_add, Nat.cast_one] using norm_principalPart_odd_le n c (k + 1)

private theorem norm_pi_div_two_mul_sq (c : ℂ) :
    ‖(Real.pi : ℂ) / (2 * c)‖ ^ 2 = Real.pi ^ 2 / (4 * Complex.normSq c) := by
  rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos, (show ‖(2 : ℂ)‖ = 2 by norm_num), div_pow, mul_pow,
    ← Complex.normSq_eq_norm_sq]
  norm_num

/-- Outside the squared radius `13/3`, the cosecant polynomial cannot take the value one. -/
theorem cosecantPolynomial_eval_ne_one {n : ℕ} (hn : 2 ≤ n) {c : ℂ}
    (hc : 13 / 3 ≤ Complex.normSq c) :
    ((cosecantPolynomial n).map (algebraMap ℝ ℂ)).eval c ≠ 1 := by
  let x : ℂ := Real.pi / (2 * c)
  have hc0 : c ≠ 0 := by intro h; subst c; norm_num at hc
  have hx0 : x ≠ 0 := div_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
    (mul_ne_zero (by norm_num) hc0)
  have hw0 : 0 < Complex.normSq c := by linarith
  have hxnorm := norm_pi_div_two_mul_sq c
  change ‖x‖ ^ 2 = _ at hxnorm
  have hxhalf : ‖x‖ ≤ Real.pi / 2 := by
    have h : ‖x‖ ^ 2 ≤ (Real.pi / 2) ^ 2 := by
      rw [hxnorm, div_le_iff₀ (by positivity)]
      nlinarith [Real.pi_pos, sq_nonneg Real.pi]
    nlinarith [norm_nonneg x, Real.pi_pos]
  have hxpi : ‖x‖ < Real.pi := hxhalf.trans_lt (by linarith [Real.pi_pos])
  have hsin := sin_pi_mul_ne_zero (Complex.div_pi_mem_integerComplement hx0 hxpi)
  have harg : (Real.pi : ℂ) * (x / Real.pi) = x := by field_simp
  rw [harg] at hsin
  have hX := mul_le_inv_norm_sin_sq hc x hxnorm hsin
  have hdom := two_pow_sub_tail_gt_one (by lia : 3 ≤ n + 1) hc hX
  have hrem := norm_inv_sin_even_pow_sub_principalPart_le_one n hx0 hxhalf
  have htail := norm_principalPart_tail_le hn c
  have hsum := (summable_principalPart_odd n c).tsum_eq_zero_add
  simp only [Nat.cast_zero, mul_zero, zero_add, one_mul] at hsum
  intro hvalue
  rw [cosecantPolynomial_eval_eq_tsum_principalPart n c, hsum] at hvalue
  simp only [Nat.cast_add, Nat.cast_one] at hvalue
  change 2 * (principalPart n x + ∑' k : ℕ, principalPart n
    ((2 * ((k : ℂ) + 1) + 1) * x)) = 1 at hvalue
  have hfirst : 2 * ‖principalPart n x‖ ≤ 1 + 2 * ‖∑' k : ℕ,
      principalPart n ((2 * ((k : ℂ) + 1) + 1) * x)‖ := by
    have heq : (2 : ℂ) * principalPart n x = 1 - 2 * ∑' k : ℕ,
        principalPart n ((2 * ((k : ℂ) + 1) + 1) * x) := by linear_combination hvalue
    have h := norm_sub_le (1 : ℂ) (2 * ∑' k : ℕ,
      principalPart n ((2 * ((k : ℂ) + 1) + 1) * x))
    rw [← heq] at h
    simpa only [norm_mul, (show ‖(2 : ℂ)‖ = 2 by norm_num), norm_one] using h
  have hcsc := norm_add_le (principalPart n x)
    (1 / Complex.sin x ^ (2 * (n + 1)) - principalPart n x)
  rw [show principalPart n x +
      (1 / Complex.sin x ^ (2 * (n + 1)) - principalPart n x) =
      1 / Complex.sin x ^ (2 * (n + 1)) by ring] at hcsc
  have hnorm : ‖1 / Complex.sin x ^ (2 * (n + 1))‖ =
      (‖Complex.sin x‖⁻¹ ^ 2) ^ (n + 1) := by
    rw [norm_div, norm_one, norm_pow, one_div, ← inv_pow, pow_mul]
  rw [hnorm] at hcsc
  change ‖∑' k : ℕ, principalPart n ((2 * ((k : ℂ) + 1) + 1) * x)‖ ≤ _ at htail
  linarith

/-- Every complex root of the centered trace polynomial lies in the required disk. -/
theorem centeredTracePolynomial_normSq_lt {n : ℕ} (hn : 2 ≤ n) {c : ℂ}
    (hc : ((centeredTracePolynomial n).map (algebraMap ℝ ℂ)).eval c = 0) :
    Complex.normSq c < 13 / 3 := by
  by_contra h
  have hne := cosecantPolynomial_eval_ne_one hn (le_of_not_gt h)
  simp only [centeredTracePolynomial, Polynomial.map_mul, Polynomial.map_C,
    Polynomial.map_sub, Polynomial.map_one, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_sub, Polynomial.eval_one] at hc
  have hfactor : (algebraMap ℝ ℂ) (1 / (2 * (4 : ℝ) ^ (n + 1))) ≠ 0 := by
    exact (_root_.map_ne_zero (algebraMap ℝ ℂ)).mpr (by positivity)
  exact hne (sub_eq_zero.mp ((mul_eq_zero.mp hc).resolve_left hfactor))

end RealRooted.CaoFu
