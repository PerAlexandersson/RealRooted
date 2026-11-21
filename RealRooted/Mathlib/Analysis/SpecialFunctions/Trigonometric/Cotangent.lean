/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Summable
import Mathlib.Analysis.PSeries
import Mathlib.Tactic

/-!
# Cotangent derivative series in the punctured unit disk

We extend the differentiated cotangent expansion to real noninteger points in
the unit disk. The proof uses uniform bounds on smaller disks and the general
open-set termwise differentiation theorem. This supplies the analytic domain
needed by Cao--Fu, arXiv:2610.40496v1, Lemma 3.2.
The derivative formula follows Mathlib's cotangent development by Chris Birkbeck;
its upper-half-plane hypothesis is replaced by a disk estimate.
-/

public section

open Set Metric Complex Real
open scoped Topology

noncomputable section

namespace Complex

/-- Each nonzero integer pole stays uniformly separated from a smaller unit disk. -/
private theorem nat_pole_norm_lower {R : ℝ} (hR₀ : 0 ≤ R)
    {z : ℂ} (hz : ‖z‖ < R) (n : ℕ) :
    (1 - R) * ((n : ℝ) + 1) ≤ ‖z - ((n : ℂ) + 1)‖ ∧
      (1 - R) * ((n : ℝ) + 1) ≤ ‖z + ((n : ℂ) + 1)‖ := by
  have hnorm : ‖(n : ℂ) + 1‖ = (n : ℝ) + 1 := by
    norm_cast
  have hsub := norm_sub_norm_le ((n : ℂ) + 1) z
  have hadd := norm_sub_norm_le ((n : ℂ) + 1) (-z)
  rw [hnorm, norm_sub_rev] at hsub
  rw [hnorm, norm_neg, sub_neg_eq_add, add_comm ((n : ℂ) + 1) z] at hadd
  have hprod : 0 ≤ R * n := mul_nonneg hR₀ (Nat.cast_nonneg n)
  constructor <;> nlinarith

/-- Pairing opposite poles improves the zeroth-order bound to an inverse-square tail. -/
private theorem cotTerm_norm_le {R : ℝ} (hR₀ : 0 ≤ R) (hR₁ : R < 1)
    (n : ℕ) {z : ℂ} (hz : ‖z‖ < R) (hz' : z ∈ integerComplement) :
    ‖cotTerm z n‖ ≤ (2 / (1 - R) ^ 2) * (1 / ((n : ℝ) + 1) ^ 2) := by
  have hlower := nat_pole_norm_lower hR₀ hz n
  have hp : 0 < (1 - R) * ((n : ℝ) + 1) := by positivity
  rw [cotTerm_identity hz' n]
  simp only [norm_mul, norm_div, norm_one, norm_ofNat]
  calc
    _ ≤ 2 * 1 * (1 / (((1 - R) * ((n : ℝ) + 1)) *
        ((1 - R) * ((n : ℝ) + 1)))) := by
      apply mul_le_mul
      · have hz1 : ‖z‖ ≤ 1 := (le_of_lt hz).trans (le_of_lt hR₁)
        linarith
      · apply one_div_le_one_div_of_le (by positivity)
        exact mul_le_mul hlower.2 hlower.1 (by positivity) (norm_nonneg _)
      · positivity
      · positivity
    _ = _ := by simp only [div_eq_mul_inv, mul_inv_rev, ← inv_pow]; ring

/-- The derivative terms of the paired cotangent series have a uniform power bound. -/
private theorem cotTerm_derivative_norm_le {R : ℝ} (hR₀ : 0 ≤ R) (hR₁ : R < 1)
    (k n : ℕ) {z : ℂ} (hz : ‖z‖ < R) (hz' : z ∈ integerComplement) :
    ‖iteratedDeriv k (fun w => cotTerm w n) z‖ ≤
      (2 * (k.factorial : ℝ) / (1 - R) ^ (k + 1)) *
        (1 / ((n : ℝ) + 1) ^ (k + 1)) := by
  rw [eqOn_iteratedDeriv_cotTerm k n hz']
  have hexp : (-1 - (k : ℤ)) = -(k + 1 : ℕ) := by lia
  simp only [hexp, zpow_neg, zpow_natCast, ← one_div]
  have hlower := nat_pole_norm_lower hR₀ hz n
  have hp : 0 < (1 - R) * ((n : ℝ) + 1) := by positivity
  have hsub : ‖1 / (z - ((n : ℂ) + 1)) ^ (k + 1)‖ ≤
      1 / ((1 - R) * ((n : ℝ) + 1)) ^ (k + 1) := by
    rw [norm_div, norm_one, norm_pow]
    gcongr
    exact hlower.1
  have hadd : ‖1 / (z + ((n : ℂ) + 1)) ^ (k + 1)‖ ≤
      1 / ((1 - R) * ((n : ℝ) + 1)) ^ (k + 1) := by
    rw [norm_div, norm_one, norm_pow]
    gcongr
    exact hlower.2
  calc
    _ ≤ (k.factorial : ℝ) *
        (1 / ((1 - R) * ((n : ℝ) + 1)) ^ (k + 1) +
          1 / ((1 - R) * ((n : ℝ) + 1)) ^ (k + 1)) := by
      simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_natCast]
      exact mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add hadd hsub))
        (Nat.cast_nonneg _)
    _ = _ := by simp only [mul_pow, one_div, mul_inv_rev]; ring

/-- The disk majorant is summable for every positive derivative order. -/
private theorem summable_cotTerm_derivative_bound (R : ℝ) {k : ℕ} (hk : 1 ≤ k) :
    Summable (fun n : ℕ => (2 * (k.factorial : ℝ) / (1 - R) ^ (k + 1)) *
      (1 / ((n : ℝ) + 1) ^ (k + 1))) := by
  apply Summable.mul_left
  have h := (summable_nat_add_iff 1).mpr
    (Real.summable_one_div_nat_pow.mpr (show 1 < k + 1 by lia))
  simpa only [Nat.cast_add, Nat.cast_one] using h

/-- On a smaller punctured unit disk the cotangent term derivatives are locally uniformly
summable, including at real noninteger points. -/
private theorem summableLocallyUniformlyOn_cotTerm_derivative {R : ℝ}
    (hR₀ : 0 ≤ R) (hR₁ : R < 1) {k : ℕ} (hk : 1 ≤ k) :
    SummableLocallyUniformlyOn
      (fun n => iteratedDerivWithin k (fun z => cotTerm z n)
        (integerComplement ∩ ball 0 R)) (integerComplement ∩ ball 0 R) := by
  have hopen : IsOpen (integerComplement ∩ ball (0 : ℂ) R) :=
    isOpen_compl_range_intCast.inter isOpen_ball
  apply SummableLocallyUniformlyOn_of_locally_bounded hopen
  intro K hK _
  refine ⟨_, summable_cotTerm_derivative_bound R hk, ?_⟩
  intro n z hz
  have hzU := hK hz
  rw [iteratedDerivWithin_of_isOpen hopen hzU]
  exact cotTerm_derivative_norm_le hR₀ hR₁ k n (by simpa using hzU.2) hzU.1

/-- The iterated cotangent terms remain differentiable on the smaller punctured disk. -/
private theorem differentiableOn_cotTerm_derivative (R : ℝ) (k n : ℕ) :
    DifferentiableOn ℂ (iteratedDerivWithin k (fun z => cotTerm z n)
      (integerComplement ∩ ball 0 R)) (integerComplement ∩ ball 0 R) := by
  have hopen : IsOpen (integerComplement ∩ ball (0 : ℂ) R) :=
    isOpen_compl_range_intCast.inter isOpen_ball
  have h : DifferentiableOn ℂ (fun z : ℂ => (-1) ^ k * k.factorial *
      ((z + (n + 1)) ^ (-1 - k : ℤ) + (z - (n + 1)) ^ (-1 - k : ℤ)))
      (integerComplement ∩ ball 0 R) := by
    apply DifferentiableOn.const_mul
    apply DifferentiableOn.add <;> refine DifferentiableOn.zpow (by fun_prop) <| .inl ?_
    · intro z hz
      simpa only [Int.cast_add, Int.cast_natCast, Int.cast_one] using
        integerComplement_add_ne_zero hz.1 (n + 1)
    · intro z hz
      simpa only [Int.cast_neg, Int.cast_add, Int.cast_natCast, Int.cast_one,
        sub_eq_add_neg] using integerComplement_add_ne_zero hz.1 (-(n + 1))
  apply h.congr
  intro z hz
  rw [iteratedDerivWithin_of_isOpen hopen hz, eqOn_iteratedDeriv_cotTerm k n hz.1]

/-- The iterated derivative of the cotangent series is its termwise derivative on a smaller
punctured unit disk, with no condition on the sign of the imaginary part. -/
private theorem iteratedDerivWithin_tsum_cotTerm {R : ℝ} (hR₀ : 0 ≤ R) (hR₁ : R < 1)
    (k : ℕ) {z : ℂ} (hz : z ∈ integerComplement ∩ ball 0 R) :
    iteratedDerivWithin k (fun z => ∑' n : ℕ, cotTerm z n)
      (integerComplement ∩ ball 0 R) z =
        ∑' n : ℕ, iteratedDerivWithin k (fun z => cotTerm z n)
          (integerComplement ∩ ball 0 R) z := by
  have hopen : IsOpen (integerComplement ∩ ball (0 : ℂ) R) :=
    isOpen_compl_range_intCast.inter isOpen_ball
  by_cases hk : k = 1
  · subst k
    have hderiv := Complex.hasSum_deriv_of_summable_norm
      (summable_cotTerm_derivative_bound R (k := 1) (by lia))
      (fun n => by simpa using differentiableOn_cotTerm_derivative R 0 n) hopen
      (fun n w hw => by
        simpa using cotTerm_norm_le hR₀ hR₁ n (by simpa using hw.2) hw.1) hz
    simp only [iteratedDerivWithin_one, derivWithin_of_isOpen hopen hz]
    exact hderiv.tsum_eq.symm
  · exact iteratedDerivWithin_tsum k hopen hz (fun z hz => summable_cotTerm hz.1)
      (fun l hl _ => summableLocallyUniformlyOn_cotTerm_derivative hR₀ hR₁ hl)
      (fun n l z _ hz =>
        (differentiableOn_cotTerm_derivative R l n).differentiableAt (hopen.mem_nhds hz))

/-- The positive and negative poles in a differentiated cotangent expansion are summable. -/
private theorem summable_cotTerm_poles {k : ℕ} (hk : 1 ≤ k) (z : ℂ) :
    Summable (fun n : ℕ => (z + (n + 1)) ^ (-1 - k : ℤ)) ∧
      Summable (fun n : ℕ => (z - (n + 1)) ^ (-1 - k : ℤ)) := by
  have h := summable_int_iff_summable_nat_and_neg.mp
    (EisensteinSeries.linear_right_summable z 1 (k := k + 1) (by lia))
  constructor
  · apply ((summable_nat_add_iff 1).mpr h.1).congr
    simp [← zpow_neg, sub_eq_add_neg]
  · apply ((summable_nat_add_iff 1).mpr h.2).congr
    simp [← zpow_neg, sub_eq_add_neg]

/-- The differentiated cotangent series in the punctured unit disk, including real points.
This is the disk-domain counterpart of Mathlib's upper-half-plane expansion. -/
theorem iteratedDeriv_cot_pi_mul_eq_tsum_of_norm_lt_one {k : ℕ} (hk : 1 ≤ k) {z : ℂ}
    (hz : z ∈ integerComplement) (hznorm : ‖z‖ < 1) :
    iteratedDeriv k (fun w : ℂ => (Real.pi : ℂ) * cot (Real.pi * w)) z =
      (-1) ^ k * k.factorial * ∑' n : ℤ, 1 / (z + n) ^ (k + 1) := by
  let R : ℝ := (‖z‖ + 1) / 2
  let U : Set ℂ := integerComplement ∩ ball 0 R
  have hR₀ : 0 ≤ R := by dsimp [R]; positivity
  have hR₁ : R < 1 := by dsimp [R]; linarith
  have hzU : z ∈ U := ⟨hz, by simp only [mem_ball, dist_zero_right]; dsimp [R]; linarith⟩
  have hopen : IsOpen U := isOpen_compl_range_intCast.inter isOpen_ball
  have hseries : iteratedDerivWithin k
      (fun w : ℂ => (Real.pi : ℂ) * cot (Real.pi * w) - 1 / w) U z =
        ∑' n : ℕ, (-1 : ℂ) ^ k * k.factorial *
          ((z + (n + 1)) ^ (-1 - k : ℤ) + (z - (n + 1)) ^ (-1 - k : ℤ)) := by
    rw [iteratedDerivWithin_congr (fun w hw => cot_series_rep' hw.1) hzU,
      iteratedDerivWithin_tsum_cotTerm hR₀ hR₁ k hzU]
    apply tsum_congr
    intro n
    rw [iteratedDerivWithin_of_isOpen hopen hzU, eqOn_iteratedDeriv_cotTerm k n hz]
  have hsub : iteratedDerivWithin k
      (fun w : ℂ => (Real.pi : ℂ) * cot (Real.pi * w) - 1 / w) U z =
        iteratedDeriv k (fun w : ℂ => (Real.pi : ℂ) * cot (Real.pi * w)) z -
          (-1) ^ k * k.factorial * z ^ (-1 - k : ℤ) := by
    simp_rw [sub_eq_add_neg]
    rw [iteratedDerivWithin_fun_add hzU hopen.uniqueDiffOn]
    · rw [iteratedDerivWithin_of_isOpen hopen hzU, iteratedDerivWithin_fun_neg,
        iteratedDerivWithin_one_div k hopen hzU]
      ring
    · simp only [Complex.cot]
      have hc : ContDiff ℂ k (fun w : ℂ => cos (Real.pi * w)) :=
        Complex.contDiff_cos.comp (by fun_prop)
      have hs : ContDiff ℂ k (fun w : ℂ => sin (Real.pi * w)) :=
        Complex.contDiff_sin.comp (by fun_prop)
      exact ContDiffWithinAt.mul (by fun_prop)
        (hc.contDiffWithinAt.div hs.contDiffWithinAt (sin_pi_mul_ne_zero hz))
    · fun_prop (disch := exact integerComplement.ne_zero hz)
  have hpoles := summable_cotTerm_poles hk z
  have hsum : z ^ (-1 - k : ℤ) +
      (∑' n : ℕ, ((z + (n + 1)) ^ (-1 - k : ℤ) +
        (z - (n + 1)) ^ (-1 - k : ℤ))) = ∑' n : ℤ, (z + n) ^ (-1 - k : ℤ) := by
    rw [tsum_of_add_one_of_neg_add_one (by simpa using hpoles.1)
      (by simpa [sub_eq_add_neg] using hpoles.2), hpoles.1.tsum_add hpoles.2]
    push_cast
    ring
  rw [tsum_mul_left, hsub] at hseries
  have hmain : iteratedDeriv k (fun w : ℂ => (Real.pi : ℂ) * cot (Real.pi * w)) z =
      (-1) ^ k * k.factorial * ∑' n : ℤ, (z + n) ^ (-1 - k : ℤ) := by
    rw [← hsum]
    linear_combination hseries
  rw [hmain]
  congr 1
  apply tsum_congr
  intro n
  rw [show (-1 - (k : ℤ)) = -(k + 1 : ℕ) by lia, zpow_neg, zpow_natCast, one_div]

/-- The cosecant-square partial-fraction identity throughout the punctured unit disk. -/
theorem tsum_inv_sq_add_int_eq {z : ℂ} (hz : z ∈ integerComplement) (hznorm : ‖z‖ < 1) :
    (∑' n : ℤ, 1 / (z + n) ^ 2) = (Real.pi : ℂ) ^ 2 / sin (Real.pi * z) ^ 2 := by
  have hseries := iteratedDeriv_cot_pi_mul_eq_tsum_of_norm_lt_one (k := 1) (by lia) hz hznorm
  simp only [iteratedDeriv_one, pow_one, Nat.factorial_one, Nat.cast_one, mul_one,
    neg_mul, one_mul] at hseries
  have hsin := sin_pi_mul_ne_zero hz
  have hlinear : HasDerivAt (fun w : ℂ => (Real.pi : ℂ) * w) Real.pi z := by
    convert (hasDerivAt_id z).const_mul (Real.pi : ℂ) using 1 <;> simp
  have hc := (hasDerivAt_cos (Real.pi * z)).comp z hlinear
  have hs := (hasDerivAt_sin (Real.pi * z)).comp z hlinear
  have hder := ((hc.div hs hsin).const_mul (Real.pi : ℂ)).deriv
  simp only [Pi.div_apply, Function.comp_apply] at hder
  have hvalue : deriv (fun w : ℂ => (Real.pi : ℂ) * cot (Real.pi * w)) z =
      -(Real.pi : ℂ) ^ 2 / sin (Real.pi * z) ^ 2 := by
    simp only [Complex.cot]
    rw [hder]
    calc
      _ = -((Real.pi : ℂ) ^ 2) *
          (sin (Real.pi * z) ^ 2 + cos (Real.pi * z) ^ 2) / sin (Real.pi * z) ^ 2 := by ring
      _ = _ := by rw [sin_sq_add_cos_sq]; ring
  rw [hvalue] at hseries
  have h := congrArg (fun w : ℂ => -w) hseries
  simpa only [neg_div, neg_neg] using h.symm

/-- Inverse-power pole sums of order at least two converge absolutely. -/
theorem summable_inv_pow_add_int (p : ℕ) (hp : 2 ≤ p) (z : ℂ) :
    Summable (fun n : ℤ => 1 / (z + n) ^ p) := by
  have h := EisensteinSeries.linear_right_summable z 1 (k := (p : ℤ)) (by exact_mod_cast hp)
  simpa only [Int.cast_one, one_mul, zpow_natCast, one_div] using h

/-- A nonzero point of the radius-`π` disk scales to the integer complement. -/
theorem div_pi_mem_integerComplement {z : ℂ} (hz : z ≠ 0) (hznorm : ‖z‖ < Real.pi) :
    z / (Real.pi : ℂ) ∈ integerComplement := by
  have hnorm : ‖z / (Real.pi : ℂ)‖ < 1 := by
    rw [norm_div, norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos,
      div_lt_one Real.pi_pos]
    exact hznorm
  rintro ⟨n, hn⟩
  by_cases hn₀ : n = 0
  · subst n
    have hdiv : z / (Real.pi : ℂ) = 0 := by simpa only [Int.cast_zero] using hn.symm
    rcases div_eq_zero_iff.mp hdiv with h | h
    · exact hz h
    · exact Real.pi_ne_zero (ofReal_eq_zero.mp h)
  · have hlarge : (1 : ℝ) ≤ |(n : ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast Int.one_le_abs hn₀
    rw [← hn, norm_intCast] at hnorm
    linarith

/-- The cosecant-square partial fractions at every nonzero complex point of norm less than `π`.
In particular this includes the real arguments required by Cao--Fu, Lemma 3.2. -/
theorem tsum_inv_sq_add_int_pi_eq {z : ℂ} (hz : z ≠ 0) (hznorm : ‖z‖ < Real.pi) :
    (∑' n : ℤ, 1 / (z + (Real.pi : ℂ) * n) ^ 2) = 1 / sin z ^ 2 := by
  have hpi : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hnorm : ‖z / (Real.pi : ℂ)‖ < 1 := by
    rw [norm_div, norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos,
      div_lt_one Real.pi_pos]
    exact hznorm
  have h := tsum_inv_sq_add_int_eq (div_pi_mem_integerComplement hz hznorm) hnorm
  have harg : (Real.pi : ℂ) * (z / Real.pi) = z := by field_simp
  rw [harg] at h
  calc
    _ = (Real.pi : ℂ)⁻¹ ^ 2 * ∑' n : ℤ, 1 / (z / Real.pi + n) ^ 2 := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro n
      field_simp
    _ = _ := by rw [h]; field_simp

/-- A second derivative of a convergent inverse-power pole sum raises its power by two. -/
theorem iteratedDeriv_two_tsum_inv_pow_add_int (k : ℕ) (hk : 1 ≤ k) {z : ℂ}
    (hz : z ∈ integerComplement) (hznorm : ‖z‖ < 1) :
    iteratedDeriv 2 (fun w : ℂ => ∑' n : ℤ, 1 / (w + n) ^ (k + 1)) z =
      (k + 1 : ℂ) * (k + 2) * ∑' n : ℤ, 1 / (z + n) ^ (k + 3) := by
  let F : ℂ → ℂ := fun w => (Real.pi : ℂ) * cot (Real.pi * w)
  have hU : IsOpen (integerComplement ∩ ball (0 : ℂ) 1) :=
    isOpen_compl_range_intCast.inter isOpen_ball
  have hzU : z ∈ integerComplement ∩ ball (0 : ℂ) 1 := ⟨hz, by simpa using hznorm⟩
  have hloc : iteratedDeriv k F =ᶠ[𝓝 z]
      (fun w : ℂ => ((-1 : ℂ) ^ k * k.factorial) * ∑' n : ℤ, 1 / (w + n) ^ (k + 1)) := by
    filter_upwards [hU.mem_nhds hzU] with w hw
    exact iteratedDeriv_cot_pi_mul_eq_tsum_of_norm_lt_one hk hw.1 (by simpa using hw.2)
  have hdiff := (hloc.iteratedDeriv 2).eq_of_nhds
  have horder : iteratedDeriv 2 (iteratedDeriv k F) = iteratedDeriv (k + 2) F := by
    rw [show k + 2 = 2 + k by lia]
    simp only [iteratedDeriv_eq_iterate, Function.iterate_add_apply]
  rw [horder] at hdiff
  conv_rhs at hdiff => rw [iteratedDeriv_const_mul_field]
  rw [iteratedDeriv_cot_pi_mul_eq_tsum_of_norm_lt_one
    (show 1 ≤ k + 2 by lia) hz hznorm] at hdiff
  have hsign : (-1 : ℂ) ^ (k + 2) = (-1) ^ k := by rw [pow_add]; norm_num
  have hfac : ((k + 2).factorial : ℂ) = (k + 2) * (k + 1) * k.factorial := by
    rw [Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    ring
  have hcoef : (-1 : ℂ) ^ k * k.factorial ≠ 0 := by
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (by exact_mod_cast Nat.factorial_ne_zero k)
  apply mul_left_cancel₀ hcoef
  rw [← hdiff, hsign, hfac]
  have hidx : k + 2 + 1 = k + 3 := by lia
  rw [hidx]
  ring

/-- Inverse-power pole sums are smooth at noninteger points of the unit disk. -/
theorem contDiffAt_tsum_inv_pow_add_int (k : ℕ) (hk : 1 ≤ k) (n : ℕ) {z : ℂ}
    (hz : z ∈ integerComplement) (hznorm : ‖z‖ < 1) :
    ContDiffAt ℂ n (fun w : ℂ => ∑' m : ℤ, 1 / (w + m) ^ (k + 1)) z := by
  let F : ℂ → ℂ := fun w => (Real.pi : ℂ) * cot (Real.pi * w)
  let c : ℂ := (-1) ^ k * k.factorial
  have hc : c ≠ 0 := by
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (by exact_mod_cast Nat.factorial_ne_zero k)
  have hF : ContDiffAt ℂ (n + k) F z := by
    have hcos : ContDiff ℂ (n + k) (fun w : ℂ => cos (Real.pi * w)) :=
      Complex.contDiff_cos.comp (by fun_prop)
    have hsin : ContDiff ℂ (n + k) (fun w : ℂ => sin (Real.pi * w)) :=
      Complex.contDiff_sin.comp (by fun_prop)
    exact ContDiffAt.mul (by fun_prop)
      (hcos.contDiffAt.div hsin.contDiffAt (sin_pi_mul_ne_zero hz))
  have hiter : ContDiffAt ℂ n (iteratedDeriv k F) z := by
    have hi := hF.iteratedFDeriv_right (m := n) (i := k) (by norm_cast)
    change ContDiffAt ℂ n
      ((ContinuousMultilinearMap.piFieldEquiv ℂ (Fin k) ℂ).symm ∘ iteratedFDeriv ℂ k F) z
    exact (ContinuousMultilinearMap.piFieldEquiv ℂ (Fin k) ℂ).symm.contDiff.contDiffAt.comp z hi
  have hU : IsOpen (integerComplement ∩ ball (0 : ℂ) 1) :=
    isOpen_compl_range_intCast.inter isOpen_ball
  have hzU : z ∈ integerComplement ∩ ball (0 : ℂ) 1 := ⟨hz, by simpa using hznorm⟩
  have heq : (fun w : ℂ => ∑' m : ℤ, 1 / (w + m) ^ (k + 1)) =ᶠ[𝓝 z]
      (fun w : ℂ => c⁻¹ * iteratedDeriv k F w) := by
    filter_upwards [hU.mem_nhds hzU] with w hw
    have h : iteratedDeriv k F w = c * ∑' m : ℤ, 1 / (w + m) ^ (k + 1) :=
      iteratedDeriv_cot_pi_mul_eq_tsum_of_norm_lt_one hk hw.1 (by simpa using hw.2)
    rw [h, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]
  exact (ContDiffAt.mul (by fun_prop) hiter).congr_of_eventuallyEq heq

end Complex
