/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.Analysis.MellinInversion
import RealRooted.Mathlib.NumberTheory.LSeries.RiemannZeta.LocalLogDeriv
import RealRooted.Mathlib.NumberTheory.LSeries.RiemannZeta.ZeroCount
import RealRooted.Mathlib.Analysis.Complex.PartialFractions
import RealRooted.Mathlib.Analysis.MellinInversion.Decay
import TauCeti.Analysis.MellinInversion
import TauCeti.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Lemma

/-!
# A zero-free positive line under the Riemann hypothesis

Mathlib's Riemann hypothesis places every zeta zero of positive real part, apart
from the excluded pole, on the critical line. Consequently the vertical line
`Re s = 9 / 20` is zero-free. Along this line the logarithmic derivative is
`O(log |t|)` for `3 ≤ |t|`.

The logarithmic bound combines the unconditional local partial-fraction estimate
with Jensen's bound for the sum of divisor multiplicities. Each nearby zero lies
at horizontal distance `1 / 20` from the evaluation point. The argument retains
multiplicities and needs neither simplicity of the zeros nor a zero-free gap
around the real axis.

## References

* H. Davenport, *Multiplicative Number Theory*, 3rd ed., Chapters 15 and 17.
-/

public section

open Complex Metric Set

namespace RiemannHypothesis

/-- A zero of positive real part lies on the critical line under Mathlib's RH. -/
theorem re_eq_half_of_riemannZeta_eq_zero_of_re_pos (hRH : RiemannHypothesis)
    {s : ℂ} (hs : 0 < s.re) (hz : riemannZeta s = 0) (hs1 : s ≠ 1) : s.re = 1 / 2 := by
  apply hRH s hz _ hs1
  rintro ⟨n, hn⟩
  have hre : s.re = -2 * ((n : ℝ) + 1) := by simpa using congrArg Complex.re hn
  linarith [show (0 : ℝ) ≤ n from Nat.cast_nonneg n]

/-- The fixed positive line to the left of the critical line is zero-free under RH. -/
theorem riemannZeta_ne_zero_of_re_eq_nine_twentieths (hRH : RiemannHypothesis)
    {s : ℂ} (hs : s.re = 9 / 20) : riemannZeta s ≠ 0 := by
  intro hz
  have hs1 : s ≠ 1 := by
    intro h
    norm_num [h] at hs
  have hhalf := hRH.re_eq_half_of_riemannZeta_eq_zero_of_re_pos (s := s)
    (by linarith) hz hs1
  linarith

private lemma distance_from_divisor_support (hRH : RiemannHypothesis)
    {t : ℝ} (ht : 3 ≤ |t|) {ρ : ℂ}
    (hρ : ρ ∈ Function.support
      (MeromorphicOn.divisor riemannZeta (closedBall (2 + I * t) (8 / 5)))) :
    1 / 20 ≤ ‖((9 / 20 : ℂ) + I * t) - ρ‖ := by
  let D := MeromorphicOn.divisor riemannZeta (closedBall (2 + I * t) (8 / 5))
  have hmem : ρ ∈ closedBall (2 + I * t) (8 / 5) := D.supportWithinDomain hρ
  have hd : ‖ρ - (2 + I * t)‖ ≤ 8 / 5 := by
    simpa only [mem_closedBall, dist_eq_norm] using hmem
  have hre : |ρ.re - 2| ≤ 8 / 5 := by
    simpa using (abs_re_le_norm (ρ - (2 + I * t))).trans hd
  have hpos : 0 < ρ.re := by linarith [(abs_le.mp hre).1]
  have hne : ρ ≠ 1 := by
    intro h
    have him := (abs_im_le_norm (ρ - (2 + I * t))).trans hd
    have him' : |t| ≤ 8 / 5 := by simpa [h] using him
    linarith
  have hA := TauCeti.analyticOnNhd_riemannZeta_closedBall ht ρ
    ((closedBall_subset_closedBall (by norm_num : (8 / 5 : ℝ) ≤ 7 / 4)) hmem)
  have hz : riemannZeta ρ = 0 := by
    by_contra hz
    exact hρ (hA.divisor_apply_eq_zero hz)
  have hhalf := hRH.re_eq_half_of_riemannZeta_eq_zero_of_re_pos hpos hz hne
  have h := abs_re_le_norm (((9 / 20 : ℂ) + I * t) - ρ)
  norm_num [hhalf] at h
  exact h

/-- Under RH, the logarithmic derivative on `Re s = 9 / 20` has logarithmic height growth. -/
theorem exists_norm_logDeriv_riemannZeta_le_log (hRH : RiemannHypothesis) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 3 ≤ |t| →
      ‖logDeriv riemannZeta ((9 / 20 : ℂ) + I * t)‖ ≤ C * Real.log |t| := by
  obtain ⟨C₁, hC₁, hlocal⟩ := TauCeti.exists_norm_logDeriv_riemannZeta_sub_divisor_le_log
  obtain ⟨C₂, hC₂, hcount⟩ := TauCeti.exists_sum_divisor_riemannZeta_le_log
  refine ⟨C₁ + 20 * C₂, by positivity, fun t ht ↦ ?_⟩
  let D := MeromorphicOn.divisor riemannZeta (closedBall (2 + I * t) (8 / 5))
  let s : ℂ := (9 / 20 : ℂ) + I * t
  have hs : ‖s - (2 + I * t)‖ ≤ 31 / 20 := by
    have heq : s - (2 + I * t) = -(31 / 20 : ℂ) := by dsimp [s]; ring
    rw [heq]
    norm_num
  have hζ : riemannZeta s ≠ 0 :=
    hRH.riemannZeta_ne_zero_of_re_eq_nine_twentieths (by simp [s])
  have hloc := hlocal t ht s hs hζ
  have hf : AnalyticOnNhd ℂ riemannZeta (closedBall (2 + I * t) (8 / 5)) :=
    (TauCeti.analyticOnNhd_riemannZeta_closedBall ht).mono
      (closedBall_subset_closedBall (by norm_num))
  have hfin : Function.HasFiniteSupport D := D.finiteSupport (isCompact_closedBall _ _)
  have hsum := Complex.norm_finsum_intCast_div_sub_le hfin
    (MeromorphicOn.AnalyticOnNhd.divisor_nonneg hf)
    (by norm_num : (0 : ℝ) < 1 / 20)
    (fun ρ hρ ↦ distance_from_divisor_support hRH ht hρ)
  have hsum' : ‖∑ᶠ ρ, (D ρ : ℂ) / (s - ρ)‖ ≤ 20 * C₂ * Real.log |t| := by
    have h20 : ‖∑ᶠ ρ, (D ρ : ℂ) / (s - ρ)‖ ≤
        20 * ((∑ᶠ ρ, D ρ : ℤ) : ℝ) := by norm_num at hsum ⊢; exact hsum
    have hc : ((∑ᶠ ρ, D ρ : ℤ) : ℝ) ≤ C₂ * Real.log |t| := hcount t ht
    exact h20.trans (by nlinarith)
  calc
    ‖logDeriv riemannZeta s‖ =
        ‖(logDeriv riemannZeta s - ∑ᶠ ρ, (D ρ : ℂ) / (s - ρ)) +
          ∑ᶠ ρ, (D ρ : ℂ) / (s - ρ)‖ := by rw [sub_add_cancel]
    _ ≤ ‖logDeriv riemannZeta s - ∑ᶠ ρ, (D ρ : ℂ) / (s - ρ)‖ +
        ‖∑ᶠ ρ, (D ρ : ℂ) / (s - ρ)‖ := norm_add_le _ _
    _ ≤ C₁ * Real.log |t| + 20 * C₂ * Real.log |t| := add_le_add hloc hsum'
    _ = (C₁ + 20 * C₂) * Real.log |t| := by ring

/-- Under RH, the logarithmic derivative is continuous on every positive vertical line
avoiding the critical line and the pole at `1`. -/
theorem continuous_logDeriv_riemannZeta_line (hRH : RiemannHypothesis) {σ : ℝ}
    (hσ : 0 < σ) (hhalf : σ ≠ 1 / 2) (h1 : σ ≠ 1) :
    Continuous (fun t : ℝ ↦ logDeriv riemannZeta ((σ : ℂ) + I * t)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have hs1 : (σ : ℂ) + I * t ≠ 1 := by
    intro h
    apply h1
    simpa using congrArg Complex.re h
  have hz : riemannZeta ((σ : ℂ) + I * t) ≠ 0 := by
    intro h
    apply hhalf
    simpa using hRH.re_eq_half_of_riemannZeta_eq_zero_of_re_pos (by simpa using hσ) h hs1
  exact ((analyticOn_riemannZeta _ (by simpa using hs1)).logDeriv hz).continuousAt.comp
    (f := fun u : ℝ ↦ (σ : ℂ) + I * u) (by fun_prop)

/-- A global sublinear bound for the logarithmic derivative on the positive left contour line,
including its compact range of heights. -/
theorem exists_norm_logDeriv_riemannZeta_le_rpow (hRH : RiemannHypothesis) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ,
      ‖logDeriv riemannZeta ((9 / 20 : ℂ) + I * t)‖ ≤ C * (1 + |t|) ^ (1 / 2 : ℝ) := by
  have hcont : Continuous (fun t : ℝ ↦ logDeriv riemannZeta ((9 / 20 : ℂ) + I * t)) := by
    simpa using hRH.continuous_logDeriv_riemannZeta_line
      (σ := 9 / 20) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨D, hD⟩ := (isCompact_Icc : IsCompact (Icc (-3 : ℝ) 3)).exists_bound_of_continuousOn
    hcont.continuousOn
  obtain ⟨B, hB, htail⟩ := hRH.exists_norm_logDeriv_riemannZeta_le_log
  refine ⟨|D| + 2 * B + 1, by positivity, fun t ↦ ?_⟩
  have hw : 1 ≤ (1 + |t|) ^ (1 / 2 : ℝ) :=
    Real.one_le_rpow (by linarith [abs_nonneg t]) (by norm_num)
  by_cases ht : 3 ≤ |t|
  · have hlog : Real.log |t| ≤ 2 * (1 + |t|) ^ (1 / 2 : ℝ) := by
      have h := Real.log_le_rpow_div (abs_nonneg t) (by norm_num : (0 : ℝ) < 1 / 2)
      have hm := Real.rpow_le_rpow (abs_nonneg t) (by linarith : |t| ≤ 1 + |t|)
        (by norm_num : (0 : ℝ) ≤ 1 / 2)
      linarith
    have h := (htail t ht).trans (mul_le_mul_of_nonneg_left hlog hB.le)
    nlinarith [abs_nonneg D]
  · have hmem : t ∈ Icc (-3 : ℝ) 3 := by
      obtain ⟨_, _⟩ := abs_le.mp (le_of_lt (lt_of_not_ge ht))
      constructor <;> linarith
    have h := hD t hmem
    have hD' : D ≤ |D| := le_abs_self D
    nlinarith [abs_nonneg D]

/-- Under RH, the logarithmic derivative divided by the first-order Perron denominator
is absolutely integrable on the positive line `Re s = 9 / 20`. -/
theorem verticalIntegrable_logDeriv_riemannZeta (hRH : RiemannHypothesis) :
    VerticalIntegrable (fun s : ℂ ↦ logDeriv riemannZeta s / (s * (s + 1))) (9 / 20) := by
  obtain ⟨C, _, hbound⟩ := hRH.exists_norm_logDeriv_riemannZeta_le_rpow
  refine Complex.verticalIntegrable_div_mul_add_one_of_le_rpow
    (C := C) (r := 1 / 2) (by norm_num) (by norm_num) (by norm_num) ?_ ?_
  · simpa only [mul_comm] using hRH.continuous_logDeriv_riemannZeta_line
      (σ := 9 / 20) (by norm_num) (by norm_num) (by norm_num)
  · intro t
    simpa only [ofReal_div, ofReal_ofNat, mul_comm] using hbound t

/-- Under RH, the smoothed zeta Perron integrand is absolutely integrable on the positive
left contour line, for every positive real base. -/
theorem integrable_logDeriv_riemannZeta_mul_cpow (hRH : RiemannHypothesis)
    {x : ℝ} (hx : 0 < x) :
    MeasureTheory.Integrable (fun t : ℝ ↦
      logDeriv riemannZeta ((9 / 20 : ℂ) + t * I) * (x : ℂ) ^ ((9 / 20 : ℂ) + t * I) /
        (((9 / 20 : ℂ) + t * I) * ((9 / 20 : ℂ) + t * I + 1))) := by
  have h := hRH.verticalIntegrable_logDeriv_riemannZeta.integrable_cpow_smul (inv_pos.mpr hx)
  simp only [ofReal_inv, inv_cpow_ofReal_nonneg hx.le, cpow_neg, inv_inv,
    smul_eq_mul, ofReal_div, ofReal_ofNat] at h
  convert h using 1
  funext t
  ring

end RiemannHypothesis
