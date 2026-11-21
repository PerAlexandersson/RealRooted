/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import RealRooted.CombinatorialExamples.CaoFu.PrincipalCoefficients
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
import RealRooted.Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
import RealRooted.Mathlib.Analysis.SpecialFunctions.Trigonometric.Cosecant
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Tactic

/-!
# The cosecant principal-part expansion on a punctured disk

We prove the partial-fraction identity used in Cao--Fu,
arXiv:2610.40496v1, Lemma 3.2, for noninteger points of the unit disk
in the scaled variable. This includes the real evaluations needed for
normalization and the finite cosecant sums. The coefficient index `n`
denotes the cosecant power `2(n+1)`.
-/

public section

open Complex Finset Filter Metric Set
open scoped Topology

noncomputable section

namespace RealRooted.CaoFu

private abbrev poleSum (j : ℕ) (z : ℂ) : ℂ :=
  ∑' m : ℤ, 1 / (z + m) ^ (2 * (j + 1))

private abbrev poleWeight (j : ℕ) : ℂ := (Real.pi : ℂ) ^ (-(2 * (j + 1) : ℕ) : ℤ)

private abbrev expansion (n : ℕ) (z : ℂ) : ℂ :=
  ∑ j ∈ range (n + 1), (principalCoeff n j : ℂ) * poleWeight j * poleSum j z

/-- Smoothness of each convergent pole sum follows from the cotangent derivatives. -/
private theorem poleSum_contDiff (j q : ℕ) {z : ℂ}
    (hz : z ∈ integerComplement) (hnorm : ‖z‖ < 1) :
    ContDiffAt ℂ q (poleSum j) z := by
  have h := Complex.contDiffAt_tsum_inv_pow_add_int (2 * j + 1) (by lia) q hz hnorm
  have hidx : 2 * j + 1 + 1 = 2 * (j + 1) := by lia
  simpa only [hidx] using h

/-- Differentiating a pole sum twice raises its even pole order by two. -/
private theorem poleSum_second (j : ℕ) {z : ℂ}
    (hz : z ∈ integerComplement) (hnorm : ‖z‖ < 1) :
    iteratedDeriv 2 (poleSum j) z =
      (2 * (j + 1) : ℂ) * (2 * (j + 1) + 1) * poleSum (j + 1) z := by
  have h := Complex.iteratedDeriv_two_tsum_inv_pow_add_int (2 * j + 1) (by lia) hz hnorm
  have hidx : 2 * j + 1 + 1 = 2 * (j + 1) := by lia
  have hidx' : 2 * j + 1 + 3 = 2 * (j + 1 + 1) := by lia
  rw [hidx, hidx'] at h
  convert h using 1; push_cast; ring

/-- Scaling a raised pole order introduces one additional factor `π⁻²`. -/
private theorem poleWeight_succ (j : ℕ) :
    (Real.pi : ℂ) ^ 2 * poleWeight (j + 1) = poleWeight j := by
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [show (Real.pi : ℂ) ^ 2 = (Real.pi : ℂ) ^ (2 : ℤ) by norm_cast,
    ← zpow_add₀ hpi]
  congr 1

/-- The real coefficient recurrence after casting to `ℂ` and clearing its denominator. -/
private theorem principalCoeff_mul (n j : ℕ) :
    (2 * (n + 1 : ℂ) * (2 * (n + 1) + 1)) * (principalCoeff (n + 1) j : ℂ) =
      (2 * (j : ℂ)) * (2 * j + 1) * principalCoeff n (j - 1) +
        4 * (n + 1 : ℂ) ^ 2 * principalCoeff n j := by
  have hden : (2 * (n + 1 : ℝ) * (2 * (n + 1) + 1)) ≠ 0 := by positivity
  have h := (div_eq_iff hden).mp (show principalCoeff (n + 1) j = _ by rfl)
  have hr : (2 * (n + 1 : ℝ) * (2 * (n + 1) + 1)) * principalCoeff (n + 1) j =
      (2 * (j : ℝ)) * (2 * j + 1) * principalCoeff n (j - 1) +
        4 * (n + 1 : ℝ) ^ 2 * principalCoeff n j := by nlinarith only [h]
  exact_mod_cast hr

/-- The second derivative of the finite principal-part expansion is termwise. -/
private theorem expansion_second (n : ℕ) {z : ℂ}
    (hz : z ∈ integerComplement) (hnorm : ‖z‖ < 1) :
    iteratedDeriv 2 (expansion n) z =
      ∑ j ∈ range (n + 1), (principalCoeff n j : ℂ) * poleWeight j *
        ((2 * (j + 1) : ℂ) * (2 * (j + 1) + 1) * poleSum (j + 1) z) := by
  rw [show expansion n = (fun w : ℂ =>
      ∑ j ∈ range (n + 1), (principalCoeff n j : ℂ) * poleWeight j * poleSum j w) by rfl,
    iteratedDeriv_fun_sum (fun j _ =>
      ContDiffAt.mul (by fun_prop) (poleSum_contDiff j 2 hz hnorm))]
  apply sum_congr rfl
  intro j _
  rw [iteratedDeriv_const_mul_field, poleSum_second j hz hnorm]

/-- The finite expansion obeys the same second-derivative recurrence as the cosecant powers. -/
private theorem expansion_recurrence (n : ℕ) {z : ℂ}
    (hz : z ∈ integerComplement) (hnorm : ‖z‖ < 1) :
    iteratedDeriv 2 (expansion n) z +
        4 * (n + 1 : ℂ) ^ 2 * (Real.pi : ℂ) ^ 2 * expansion n z =
      (2 * (n + 1 : ℂ) * (2 * (n + 1) + 1)) * (Real.pi : ℂ) ^ 2 *
        expansion (n + 1) z := by
  rw [expansion_second n hz hnorm]
  have hrec : (2 * (n + 1 : ℂ) * (2 * (n + 1) + 1)) * (Real.pi : ℂ) ^ 2 *
      expansion (n + 1) z =
      (Real.pi : ℂ) ^ 2 *
        ∑ j ∈ range (n + 2),
          ((2 * (j : ℂ)) * (2 * j + 1) * principalCoeff n (j - 1) +
            4 * (n + 1 : ℂ) ^ 2 * principalCoeff n j) * poleWeight j * poleSum j z := by
    simp only [expansion, mul_sum]
    apply sum_congr rfl
    intro j _
    have h := principalCoeff_mul n j
    linear_combination (Real.pi : ℂ) ^ 2 * poleWeight j * poleSum j z * h
  rw [hrec]
  have hsplit : (∑ j ∈ range (n + 2),
      ((2 * (j : ℂ)) * (2 * j + 1) * principalCoeff n (j - 1) +
        4 * (n + 1 : ℂ) ^ 2 * principalCoeff n j) * poleWeight j * poleSum j z) =
      (∑ j ∈ range (n + 2),
        ((2 * (j : ℂ)) * (2 * j + 1) * principalCoeff n (j - 1)) *
          poleWeight j * poleSum j z) +
      ∑ j ∈ range (n + 2), (4 * (n + 1 : ℂ) ^ 2 * principalCoeff n j) *
        poleWeight j * poleSum j z := by
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro j _
    ring
  rw [hsplit, mul_add]
  have hleft : (Real.pi : ℂ) ^ 2 *
      (∑ j ∈ range (n + 2),
        ((2 * (j : ℂ)) * (2 * j + 1) * principalCoeff n (j - 1)) * poleWeight j * poleSum j z) =
      ∑ j ∈ range (n + 1), (principalCoeff n j : ℂ) * poleWeight j *
        ((2 * (j + 1) : ℂ) * (2 * (j + 1) + 1) * poleSum (j + 1) z) := by
    rw [show n + 2 = (n + 1) + 1 by lia, sum_range_succ']
    simp only [Nat.cast_zero, mul_zero, zero_mul, zero_add, add_zero, mul_sum]
    apply sum_congr rfl
    intro j _
    rw [Nat.add_sub_cancel]
    have hw := poleWeight_succ j
    push_cast
    linear_combination (principalCoeff n j : ℂ) *
      (2 * (j + 1)) * (2 * (j + 1) + 1) * poleSum (j + 1) z * hw
  rw [hleft]
  congr 1
  rw [show n + 2 = (n + 1) + 1 by lia, sum_range_succ,
    principalCoeff_eq_zero_of_lt (show n < n + 1 by lia)]
  simp only [Complex.ofReal_zero, mul_zero, zero_mul, add_zero, expansion, mul_sum]
  apply sum_congr rfl
  intro j _
  ring

/-- Cao--Fu, Lemma 3.2: the principal-part expansion at noninteger points of the unit disk.
The recurrence indices are reduced by one, and the variable is scaled by `π`. -/
theorem sin_neg_even_zpow_eq_sum_poles (n : ℕ) {z : ℂ}
    (hz : z ∈ integerComplement) (hnorm : ‖z‖ < 1) :
    sin (Real.pi * z) ^ (-(2 * (n + 1) : ℕ) : ℤ) =
      ∑ j ∈ range (n + 1), (principalCoeff n j : ℂ) *
        (Real.pi : ℂ) ^ (-(2 * (j + 1) : ℕ) : ℤ) *
          (∑' m : ℤ, 1 / (z + m) ^ (2 * (j + 1))) := by
  have hmain : ∀ n : ℕ, sin (Real.pi * z) ^ (-(2 * (n + 1) : ℕ) : ℤ) = expansion n z := by
    intro n
    induction n generalizing z with
    | zero =>
      have h := Complex.tsum_inv_sq_add_int_eq hz hnorm
      simp only [expansion, range_one, sum_singleton, principalCoeff, ↓reduceIte,
        Complex.ofReal_one, one_mul, poleWeight, poleSum, zero_add, mul_one]
      rw [h]
      have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
      simp only [zpow_neg, zpow_natCast]
      field_simp
    | succ n ih =>
      have hU : IsOpen (integerComplement ∩ ball (0 : ℂ) 1) :=
        isOpen_compl_range_intCast.inter isOpen_ball
      have hzU : z ∈ integerComplement ∩ ball (0 : ℂ) 1 := ⟨hz, by simpa using hnorm⟩
      have heq : (fun w : ℂ => sin (Real.pi * w) ^ (-(2 * (n + 1) : ℕ) : ℤ)) =ᶠ[𝓝 z]
          expansion n := by
        filter_upwards [hU.mem_nhds hzU] with w hw
        exact ih hw.1 (by simpa using hw.2)
      have hder := (heq.iteratedDeriv 2).eq_of_nhds
      have hf := Complex.iteratedDeriv_two_sin_mul_neg_even_zpow Real.pi (n + 1)
        (sin_pi_mul_ne_zero hz)
      rw [hder, ih hz hnorm] at hf
      have he := expansion_recurrence n hz hnorm
      have hcoef : (2 * (n + 1 : ℂ) * (2 * (n + 1) + 1)) * (Real.pi : ℂ) ^ 2 ≠ 0 := by
        have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
        have hd : (2 * (n + 1 : ℂ) * (2 * (n + 1) + 1)) ≠ 0 := by
          have hdReal : (2 * (n + 1 : ℝ) * (2 * (n + 1) + 1)) ≠ 0 := by positivity
          exact_mod_cast hdReal
        exact mul_ne_zero hd (pow_ne_zero _ hpi)
      apply mul_left_cancel₀ hcoef
      calc
        _ = iteratedDeriv 2 (expansion n) z +
            4 * (n + 1 : ℂ) ^ 2 * (Real.pi : ℂ) ^ 2 * expansion n z := by
          simpa only [Nat.cast_add, Nat.cast_one, mul_assoc] using hf.symm
        _ = _ := he
  exact hmain n

/-- The principal-part identity in the original variable on `0 < ‖z‖ < π`.
This is the domain needed for Cao--Fu, Lemma 3.2, and the centered-disk estimate. -/
theorem inv_sin_even_pow_eq_sum_poles (n : ℕ) {z : ℂ}
    (hz : z ≠ 0) (hnorm : ‖z‖ < Real.pi) :
    1 / sin z ^ (2 * (n + 1)) =
      ∑ j ∈ range (n + 1), (principalCoeff n j : ℂ) *
        (∑' m : ℤ, 1 / (z + (Real.pi : ℂ) * m) ^ (2 * (j + 1))) := by
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hn : ‖z / (Real.pi : ℂ)‖ < 1 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos,
      div_lt_one Real.pi_pos]
    exact hnorm
  have h := sin_neg_even_zpow_eq_sum_poles n (Complex.div_pi_mem_integerComplement hz hnorm) hn
  have harg : (Real.pi : ℂ) * (z / Real.pi) = z := by field_simp
  rw [harg] at h
  have hterm (j : ℕ) : poleWeight j * poleSum j (z / Real.pi) =
      ∑' m : ℤ, 1 / (z + (Real.pi : ℂ) * m) ^ (2 * (j + 1)) := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro m
    have hid : z / (Real.pi : ℂ) + m = (z + Real.pi * m) / Real.pi := by field_simp
    rw [hid]
    simp only [poleWeight, zpow_neg, zpow_natCast, div_pow, one_div_div]
    field_simp
  calc
    _ = ∑ j ∈ range (n + 1), (principalCoeff n j : ℂ) *
        poleWeight j * poleSum j (z / Real.pi) := by
      simpa only [poleSum, zpow_neg, zpow_natCast, one_div] using h
    _ = _ := by
      apply sum_congr rfl
      intro j _
      rw [mul_assoc, hterm]

/-- The real pole sum at a half-integer has a nonnegative inverse-power summand. -/
private theorem half_pole_nonneg (j : ℕ) (m : ℤ) :
    0 ≤ 1 / ((1 / 2 : ℝ) + m) ^ (2 * (j + 1)) := by
  apply div_nonneg (by norm_num)
  rw [pow_mul]
  exact pow_nonneg (sq_nonneg _) _

/-- The two nearest poles give a lower bound on the real half-integer pole sum. -/
private theorem half_pole_sum_ge (j : ℕ) :
    2 * (2 : ℝ) ^ (2 * (j + 1)) ≤
      ∑' m : ℤ, 1 / ((1 / 2 : ℝ) + m) ^ (2 * (j + 1)) := by
  have hs : Summable (fun m : ℤ => 1 / ((1 / 2 : ℝ) + m) ^ (2 * (j + 1))) := by
    apply Complex.summable_ofReal.mp
    simpa only [Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_add,
      Complex.ofReal_one, Complex.ofReal_ofNat, Complex.ofReal_intCast] using
      Complex.summable_inv_pow_add_int (2 * (j + 1)) (by lia) (1 / 2)
  have h := hs.sum_le_tsum ({0, -1} : Finset ℤ) (fun m _ => half_pole_nonneg j m)
  have heq : (∑ m ∈ ({0, -1} : Finset ℤ),
      1 / ((1 / 2 : ℝ) + m) ^ (2 * (j + 1))) = 2 * (2 : ℝ) ^ (2 * (j + 1)) := by
    norm_num [pow_mul, div_pow]
    ring
  rwa [heq] at h

/-- Evaluating the principal-part expansion at `π/2` gives its exact normalization. -/
theorem sum_principalCoeff_half_poles (n : ℕ) :
    (∑ j ∈ range (n + 1), principalCoeff n j / Real.pi ^ (2 * (j + 1)) *
      ∑' m : ℤ, 1 / ((1 / 2 : ℝ) + m) ^ (2 * (j + 1))) = 1 := by
  have hz : (1 / 2 : ℂ) ∈ integerComplement := by
    rintro ⟨m, hm⟩
    have hmR := congrArg Complex.re hm
    norm_num at hmR
    have hpos : 0 < m := by exact_mod_cast (show (0 : ℝ) < m by rw [hmR]; norm_num)
    have hlt : m < 1 := by exact_mod_cast (show (m : ℝ) < 1 by rw [hmR]; norm_num)
    lia
  have hn : ‖(1 / 2 : ℂ)‖ < 1 := by norm_num
  have h := sin_neg_even_zpow_eq_sum_poles n hz hn
  have harg : (Real.pi : ℂ) * (1 / 2) = Real.pi / 2 := by ring
  rw [harg, Complex.sin_pi_div_two, one_zpow] at h
  apply Complex.ofReal_injective
  push_cast
  simpa only [zpow_neg, zpow_natCast, div_eq_mul_inv] using h.symm

/-- The principal part at `π/2` is at most one half, as in Round 2, (F5). -/
theorem sum_principalCoeff_two_div_pi_pow_le (n : ℕ) :
    (∑ j ∈ range (n + 1), principalCoeff n j * (2 / Real.pi) ^ (2 * (j + 1))) ≤
      (1 / 2 : ℝ) := by
  have h : 2 * (∑ j ∈ range (n + 1),
      principalCoeff n j * (2 / Real.pi) ^ (2 * (j + 1))) ≤ 1 := by
    calc
      _ = ∑ j ∈ range (n + 1), (principalCoeff n j / Real.pi ^ (2 * (j + 1))) *
          (2 * (2 : ℝ) ^ (2 * (j + 1))) := by
        rw [mul_sum]
        apply sum_congr rfl
        intro j _
        simp only [div_eq_mul_inv]
        ring
      _ ≤ ∑ j ∈ range (n + 1), (principalCoeff n j / Real.pi ^ (2 * (j + 1))) *
          ∑' m : ℤ, 1 / ((1 / 2 : ℝ) + m) ^ (2 * (j + 1)) := by
        apply sum_le_sum
        intro j _
        exact mul_le_mul_of_nonneg_left (half_pole_sum_ge j)
          (div_nonneg (principalCoeff_nonneg n j) (by positivity))
      _ = 1 := sum_principalCoeff_half_poles n
  linarith

end RealRooted.CaoFu
