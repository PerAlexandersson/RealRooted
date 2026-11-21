/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import RealRooted.CombinatorialExamples.CaoFu.CosecantExpansion
import Mathlib.Analysis.Complex.Basic
import RealRooted.Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Tactic

/-!
# The cosecant remainder on the half-radius disk

We bound the analytic remainder in Cao--Fu, arXiv:2610.40496v1, Lemma 3.2.
Symmetric nonzero poles have numerators with nonnegative even coefficients.
Their sum at the positive real radius therefore majorizes their norm on the
disk. The exact expansion at `π/2` supplies the bound uniformly in the power.
-/

@[expose] public section
noncomputable section
open Finset
namespace RealRooted.CaoFu
private theorem pair_numerator {R : Type*} [CommRing R] (a z : R) (p : ℕ) :
    (a + z) ^ p + (a - z) ^ p =
      ∑ k ∈ range (p + 1), ((1 + (-1 : R) ^ k) * (p.choose k : R) *
        a ^ (p - k)) * z ^ k := by
  rw [add_comm a z, sub_eq_add_neg, add_comm a (-z), add_pow, add_pow,
    ← sum_add_distrib]
  apply sum_congr rfl
  intro k _
  rw [neg_pow]
  ring

private theorem pair_coeff_nonneg (p k : ℕ) {a : ℝ} (ha : 0 ≤ a) :
    0 ≤ (1 + (-1 : ℝ) ^ k) * (p.choose k : ℝ) * a ^ (p - k) := by
  have h : 0 ≤ 1 + (-1 : ℝ) ^ k := by
    rcases Nat.even_or_odd k with h | h
    · rw [h.neg_one_pow]; norm_num
    · rw [h.neg_one_pow]; norm_num
  positivity

private theorem norm_pair_numerator_le (p : ℕ) {a R : ℝ} (ha : 0 ≤ a)
    {z : ℂ} (hz : ‖z‖ ≤ R) :
    ‖((a : ℂ) + z) ^ p + ((a : ℂ) - z) ^ p‖ ≤ (a + R) ^ p + (a - R) ^ p := by
  rw [pair_numerator, pair_numerator]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro k _
  have hc := pair_coeff_nonneg p k ha
  have hcast : (1 + (-1 : ℂ) ^ k) * (p.choose k : ℂ) * (a : ℂ) ^ (p - k) =
      (((1 + (-1 : ℝ) ^ k) * (p.choose k : ℝ) * a ^ (p - k) : ℝ) : ℂ) := by
    push_cast; rfl
  rw [hcast, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc, norm_pow]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hz k) hc

private theorem pair_inv_pow_eq {R : Type*} [Field R] (a z : R) (p : ℕ)
    (hp : a + z ≠ 0) (hm : a - z ≠ 0) :
    1 / (a + z) ^ p + 1 / (a - z) ^ p =
      ((a + z) ^ p + (a - z) ^ p) / (a ^ 2 - z ^ 2) ^ p := by
  rw [div_add_div 1 1 (pow_ne_zero _ hp) (pow_ne_zero _ hm), ← mul_pow]
  congr 1
  · ring
  · congr 1; ring

/-- A symmetric pair of poles is majorized at the positive real radius. -/
theorem norm_pair_inv_pow_le (p : ℕ) {a R : ℝ} (hR : 0 ≤ R) (ha : R < a)
    {z : ℂ} (hz : ‖z‖ ≤ R) :
    ‖1 / ((a : ℂ) + z) ^ p + 1 / ((a : ℂ) - z) ^ p‖ ≤
      1 / (a + R) ^ p + 1 / (a - R) ^ p := by
  have ha0 : 0 < a := lt_of_le_of_lt hR ha
  have haR : 0 < a ^ 2 - R ^ 2 := by nlinarith
  have hp : (a : ℂ) + z ≠ 0 := by
    intro h
    have hnorm : ‖z‖ = a := by
      have heq : z = -(a : ℂ) := by linear_combination h
      rw [heq, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha0]
    linarith
  have hm : (a : ℂ) - z ≠ 0 := by
    intro h
    have heq : z = (a : ℂ) := (sub_eq_zero.mp h).symm
    have hnorm : ‖z‖ = a := by
      rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha0]
    linarith
  have hd : a ^ 2 - R ^ 2 ≤ ‖(a : ℂ) ^ 2 - z ^ 2‖ := by
    have h := norm_sub_norm_le ((a : ℂ) ^ 2) (z ^ 2)
    rw [norm_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha0] at h
    have hz2 := pow_le_pow_left₀ (norm_nonneg z) hz 2
    linarith
  rw [pair_inv_pow_eq _ _ _ hp hm, norm_div, norm_pow,
    pair_inv_pow_eq a R p (by linarith) (by linarith)]
  exact div_le_div₀ (by positivity) (norm_pair_numerator_le p ha0.le hz)
    (by positivity) (pow_le_pow_left₀ haR.le hd p)

/-- The principal part of `csc^(2(n+1))` at zero. -/
def principalPart (n : ℕ) (z : ℂ) : ℂ :=
  ∑ j ∈ range (n + 1), (principalCoeff n j : ℂ) / z ^ (2 * (j + 1))

/-- The same finite principal part, evaluated over the reals. -/
def principalPartReal (n : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ range (n + 1), principalCoeff n j / x ^ (2 * (j + 1))

/-- Casting the real principal part agrees with its complex evaluation. -/
@[simp] theorem ofReal_principalPartReal (n : ℕ) (x : ℝ) :
    (principalPartReal n x : ℂ) = principalPart n x := by
  simp [principalPart, principalPartReal]

/-- The real principal part at `π/2` is at most one half. -/
theorem principalPartReal_pi_div_two_le (n : ℕ) :
    principalPartReal n (Real.pi / 2) ≤ 1 / 2 := by
  unfold principalPartReal
  convert sum_principalCoeff_two_div_pi_pow_le n using 1
  apply sum_congr rfl
  intro j _
  rw [div_eq_mul_inv, ← inv_pow, inv_div]

private theorem summable_scaled_poles (p : ℕ) (hp : 2 ≤ p) (z : ℂ) :
    Summable (fun m : ℤ => 1 / (z + (Real.pi : ℂ) * m) ^ p) := by
  have h := (Complex.summable_inv_pow_add_int p hp (z / Real.pi)).mul_left
    (((Real.pi : ℂ) ^ p)⁻¹)
  convert h using 1
  funext m
  have harg : z / (Real.pi : ℂ) + m = (z + Real.pi * m) / Real.pi := by field_simp
  rw [harg, div_pow, one_div_div]
  field_simp

private theorem paired_pole_term_eq {R : Type*} [Field R]
    (b z : R) (p : ℕ) (hp : Even p) (k : ℕ) :
    1 / (z + b * (((k : ℤ) + 1 : ℤ) : R)) ^ p +
      1 / (z + b * ((-((k : ℤ) + 1) : ℤ) : R)) ^ p =
      1 / (b * (k + 1) + z) ^ p + 1 / (b * (k + 1) - z) ^ p := by
  push_cast
  rw [show z + b * -((k : R) + 1) = -(b * (k + 1) - z) by ring, hp.neg_pow]
  rw [add_comm z]

private theorem shifted_int_injective :
    Function.Injective (fun k : ℕ => (k : ℤ) + 1) := by
  intro a c h
  exact_mod_cast add_right_cancel h

private theorem paired_pole_sum_eq {R : Type*} [NormedField R] [CompleteSpace R]
    (b z : R) (p : ℕ) (hp : Even p)
    (hs : Summable (fun m : ℤ => 1 / (z + b * m) ^ p)) :
    (∑' m : ℤ, 1 / (z + b * m) ^ p) = 1 / z ^ p +
      ∑' k : ℕ, (1 / (b * (k + 1) + z) ^ p + 1 / (b * (k + 1) - z) ^ p) := by
  have hpos := hs.comp_injective shifted_int_injective
  have hneg := hs.comp_injective (neg_injective.comp shifted_int_injective)
  calc
    _ = (∑' k : ℕ, 1 / (z + b * (((k : ℤ) + 1 : ℤ) : R)) ^ p) + 1 / z ^ p +
        ∑' k : ℕ, 1 / (z + b * ((-((k : ℤ) + 1) : ℤ) : R)) ^ p := by
      simpa only [Int.cast_zero, mul_zero, add_zero] using
        (tsum_of_add_one_of_neg_add_one
          (f := fun m : ℤ => 1 / (z + b * m) ^ p) hpos hneg)
    _ = 1 / z ^ p + ((∑' k : ℕ, 1 / (z + b * (((k : ℤ) + 1 : ℤ) : R)) ^ p) +
        ∑' k : ℕ, 1 / (z + b * ((-((k : ℤ) + 1) : ℤ) : R)) ^ p) := by ring
    _ = 1 / z ^ p + ∑' k : ℕ, (1 / (z + b * (((k : ℤ) + 1 : ℤ) : R)) ^ p +
        1 / (z + b * ((-((k : ℤ) + 1) : ℤ) : R)) ^ p) := by
      exact congrArg (fun w : R => 1 / z ^ p + w) (hpos.tsum_add hneg).symm
    _ = _ := by
      congr 1
      exact tsum_congr (paired_pole_term_eq b z p hp)

private theorem summable_paired_poles {R : Type*} [NormedField R] [CompleteSpace R]
    (b z : R) (p : ℕ) (hp : Even p)
    (hs : Summable (fun m : ℤ => 1 / (z + b * m) ^ p)) :
    Summable (fun k : ℕ => 1 / (b * (k + 1) + z) ^ p +
      1 / (b * (k + 1) - z) ^ p) := by
  have hpos := hs.comp_injective shifted_int_injective
  have hneg := hs.comp_injective (neg_injective.comp shifted_int_injective)
  refine (hpos.add hneg).congr fun k => ?_
  simpa only [Function.comp_apply] using paired_pole_term_eq b z p hp k

private theorem summable_real_scaled_poles (p : ℕ) (hp : 2 ≤ p) (x : ℝ) :
    Summable (fun m : ℤ => 1 / (x + Real.pi * m) ^ p) := by
  apply Complex.summable_ofReal.mp
  simpa only [Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_add,
    Complex.ofReal_mul, Complex.ofReal_one, Complex.ofReal_intCast] using
    summable_scaled_poles p hp x

private abbrev pairedPole (j : ℕ) (z : ℂ) (k : ℕ) : ℂ :=
  1 / ((Real.pi : ℂ) * (k + 1) + z) ^ (2 * (j + 1)) +
    1 / ((Real.pi : ℂ) * (k + 1) - z) ^ (2 * (j + 1))

private abbrev pairedPoleReal (j : ℕ) (x : ℝ) (k : ℕ) : ℝ :=
  1 / (Real.pi * (k + 1) + x) ^ (2 * (j + 1)) +
    1 / (Real.pi * (k + 1) - x) ^ (2 * (j + 1))

private theorem norm_tsum_pairedPole_le (j : ℕ) {z : ℂ} (hz : ‖z‖ ≤ Real.pi / 2) :
    ‖∑' k, pairedPole j z k‖ ≤ ∑' k, pairedPoleReal j (Real.pi / 2) k := by
  have hs := summable_paired_poles Real.pi (Real.pi / 2) (2 * (j + 1))
    (even_two_mul _) (summable_real_scaled_poles _ (by lia) _)
  apply tsum_of_norm_bounded hs.hasSum
  intro k
  have h := norm_pair_inv_pow_le (2 * (j + 1)) (by positivity : 0 ≤ Real.pi / 2)
    (show Real.pi / 2 < Real.pi * (k + 1) by
      have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      nlinarith [Real.pi_pos]) hz
  simpa only [Complex.ofReal_mul, Complex.ofReal_add, Complex.ofReal_natCast,
    Complex.ofReal_one] using h

/-- Removing the zero pole leaves the sum over the symmetric nonzero poles. -/
private theorem inv_sin_even_pow_sub_principalPart (n : ℕ) {z : ℂ}
    (hz : z ≠ 0) (hnorm : ‖z‖ < Real.pi) :
    1 / Complex.sin z ^ (2 * (n + 1)) - principalPart n z =
      ∑ j ∈ range (n + 1), (principalCoeff n j : ℂ) * ∑' k, pairedPole j z k := by
  rw [inv_sin_even_pow_eq_sum_poles n hz hnorm, principalPart, ← sum_sub_distrib]
  apply sum_congr rfl
  intro j _
  rw [paired_pole_sum_eq _ _ _ (even_two_mul _)
    (summable_scaled_poles _ (by lia) _)]
  ring

/-- At `π/2`, the positive pole remainder is exactly one minus the principal part. -/
private theorem sum_pairedPoleReal_pi_div_two (n : ℕ) :
    (∑ j ∈ range (n + 1), principalCoeff n j *
      ∑' k, pairedPoleReal j (Real.pi / 2) k) =
      1 - principalPartReal n (Real.pi / 2) := by
  have h := inv_sin_even_pow_sub_principalPart n
    (show (Real.pi / 2 : ℂ) ≠ 0 by exact_mod_cast (ne_of_gt (half_pos Real.pi_pos)))
    (show ‖(Real.pi / 2 : ℂ)‖ < Real.pi by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
      norm_num
      linarith [Real.pi_pos])
  rw [Complex.sin_pi_div_two, one_pow, div_one] at h
  apply Complex.ofReal_injective
  push_cast
  simpa only [pairedPole, ofReal_principalPartReal, Complex.ofReal_div,
    Complex.ofReal_ofNat] using h.symm

/-- The analytic remainder of every positive even cosecant power is bounded on
`0 < ‖z‖ ≤ π/2`, uniformly in the power. -/
theorem norm_inv_sin_even_pow_sub_principalPart_le (n : ℕ) {z : ℂ}
    (hz : z ≠ 0) (hnorm : ‖z‖ ≤ Real.pi / 2) :
    ‖1 / Complex.sin z ^ (2 * (n + 1)) - principalPart n z‖ ≤
      1 - principalPartReal n (Real.pi / 2) := by
  rw [inv_sin_even_pow_sub_principalPart n hz
    (hnorm.trans_lt (by linarith [Real.pi_pos]))]
  calc
    _ ≤ ∑ j ∈ range (n + 1), ‖(principalCoeff n j : ℂ) * ∑' k, pairedPole j z k‖ :=
      norm_sum_le _ _
    _ ≤ ∑ j ∈ range (n + 1), principalCoeff n j *
        ∑' k, pairedPoleReal j (Real.pi / 2) k := by
      apply sum_le_sum
      intro j _
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (principalCoeff_nonneg n j)]
      exact mul_le_mul_of_nonneg_left (norm_tsum_pairedPole_le j hnorm)
        (principalCoeff_nonneg n j)
    _ = _ := sum_pairedPoleReal_pi_div_two n

/-- The uniform cosecant remainder bound used in the centered disk estimate. -/
theorem norm_inv_sin_even_pow_sub_principalPart_le_one (n : ℕ) {z : ℂ}
    (hz : z ≠ 0) (hnorm : ‖z‖ ≤ Real.pi / 2) :
    ‖1 / Complex.sin z ^ (2 * (n + 1)) - principalPart n z‖ ≤ 1 := by
  apply (norm_inv_sin_even_pow_sub_principalPart_le n hz hnorm).trans
  have hp : 0 ≤ principalPartReal n (Real.pi / 2) := by
    apply sum_nonneg
    intro j _
    exact div_nonneg (principalCoeff_nonneg n j) (by positivity)
  linarith

end RealRooted.CaoFu
