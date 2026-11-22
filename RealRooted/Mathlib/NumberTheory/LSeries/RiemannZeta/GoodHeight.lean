/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import Mathlib.NumberTheory.LSeries.RiemannZeta
import RealRooted.Mathlib.Analysis.Complex.PartialFractions
import RealRooted.Mathlib.NumberTheory.LSeries.RiemannZeta.ZeroWindow
import RealRooted.Mathlib.NumberTheory.LSeries.RiemannZeta.ZeroCount
import RealRooted.Mathlib.NumberTheory.LSeries.RiemannZeta.LocalLogDeriv
import RealRooted.Mathlib.NumberTheory.LSeries.RiemannZeta.RiemannHypothesis
import RealRooted.Mathlib.Topology.Instances.Real.FiniteSeparation
import TauCeti.Analysis.Meromorphic.Divisor
import Mathlib.Tactic.Lemma

/-!
# Good heights for a contour to the left of the critical line

Under Mathlib's Riemann hypothesis, every interval `[T, T + 1]`, for `T ≥ 5`,
contains a height `t` at which zeta is nonzero throughout the horizontal segment
`9 / 20 ≤ Re s ≤ 2`, and its logarithmic derivative is uniformly `O(log(T)^2)`.

A finite-set separation theorem chooses `t` away from the ordinates of zeros in
a fixed window about `T + 1 / 2`. RH confines the nearby zeros to the critical
line, so the local partial-fraction estimate only involves zeros in this window.
Jensen's bound counts their full multiplicities.

## References

* H. Davenport, *Multiplicative Number Theory*, 3rd ed., Chapter 17.
-/

public section

open Complex Metric Set TauCeti

namespace RiemannHypothesis

private lemma nearby_height_log_le {T t : ℝ} (hT : 5 ≤ T) (ht : t ∈ Icc T (T + 1)) :
    3 ≤ |t| ∧ Real.log |t| ≤ 2 * Real.log T := by
  have ht0 : 0 ≤ t := by linarith [ht.1]
  rw [abs_of_nonneg ht0]
  refine ⟨by linarith [ht.1], ?_⟩
  calc
    Real.log t ≤ Real.log (T ^ 2) := Real.log_le_log (by linarith [ht.1])
      (by nlinarith [ht.2])
    _ = 2 * Real.log T := by rw [Real.log_pow]; norm_num

private lemma card_window_ordinates_le_order_sum {T : ℝ} (hT : 5 ≤ T)
    (hfin : (riemannZetaZeroWindow (T + 1 / 2) (6 / 5)).Finite) :
    ((hfin.toFinset.image Complex.im).card : ℝ) ≤
      ∑ ρ ∈ hfin.toFinset, (analyticOrderNatAt riemannZeta ρ : ℝ) := by
  classical
  have hc : (hfin.toFinset.image Complex.im).card ≤ hfin.toFinset.card := Finset.card_image_le
  have hc' : ((hfin.toFinset.image Complex.im).card : ℝ) ≤ hfin.toFinset.card := by
    exact_mod_cast hc
  refine hc'.trans ?_
  rw [Finset.card_eq_sum_ones, Nat.cast_sum]
  refine Finset.sum_le_sum fun ρ hρ ↦ ?_
  have hmem := hfin.mem_toFinset.mp hρ
  have hne := ne_one_of_mem_riemannZetaZeroWindow
    (by rw [abs_of_nonneg (by linarith)]; linarith : (6 / 5 : ℝ) < |T + 1 / 2|) hmem
  exact_mod_cast one_le_analyticOrderNatAt_riemannZeta hmem.1 hne

private lemma exists_separated_height (hRH : RiemannHypothesis) :
    ∃ A : ℝ, 0 < A ∧ ∀ T : ℝ, 5 ≤ T →
      ∃ t ∈ Icc T (T + 1), ∃ δ : ℝ, 0 < δ ∧ δ⁻¹ ≤ A * Real.log T ∧
        ∀ ρ ∈ riemannZetaZeroWindow (T + 1 / 2) (6 / 5), δ ≤ |t - ρ.im| := by
  classical
  obtain ⟨C, hC, hwindow⟩ := hRH.exists_sum_riemannZetaZeroWindow_order_wide_le_log
  have h5 : 0 < Real.log 5 := Real.log_pos (by norm_num)
  refine ⟨4 * C + 2 / Real.log 5, by positivity, fun T hT ↦ ?_⟩
  have ht0 : 4 ≤ |T + 1 / 2| := by rw [abs_of_nonneg (by linarith)]; linarith
  obtain ⟨hfin, hsum⟩ := hwindow (T + 1 / 2) ht0
  let G := hfin.toFinset.image Complex.im
  have hcard : (G.card : ℝ) ≤
      ∑ ρ ∈ hfin.toFinset, (analyticOrderNatAt riemannZeta ρ : ℝ) :=
    card_window_ordinates_le_order_sum hT hfin
  have hlog := (nearby_height_log_le hT
    (show T + 1 / 2 ∈ Icc T (T + 1) from ⟨by linarith, by linarith⟩)).2
  have hcard' : (G.card : ℝ) ≤ 2 * C * Real.log T := by
    have h := hcard.trans (hsum.trans (mul_le_mul_of_nonneg_left hlog hC.le))
    nlinarith
  obtain ⟨t, ht, hsep⟩ := G.exists_mem_Icc_forall_le_abs_sub
    (a := T) (b := T + 1) (by linarith)
  let δ : ℝ := 1 / (2 * ((G.card : ℝ) + 1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  refine ⟨t, ht, δ, hδ, ?_, fun ρ hρ ↦ ?_⟩
  · have hlogT : Real.log 5 ≤ Real.log T := Real.log_le_log (by norm_num) hT
    have htwo : 2 ≤ 2 / Real.log 5 * Real.log T := by
      rw [div_mul_eq_mul_div, le_div_iff₀ h5]
      linarith
    simp only [δ, one_div, inv_inv]
    nlinarith
  · have hmem : ρ.im ∈ G := Finset.mem_image.mpr ⟨ρ, hfin.mem_toFinset.mpr hρ, rfl⟩
    simpa [δ] using hsep ρ.im hmem

private lemma divisor_support_mem_window (hRH : RiemannHypothesis)
    {T t : ℝ} (hT : 5 ≤ T) (ht : t ∈ Icc T (T + 1)) {ρ : ℂ}
    (hρ : ρ ∈ Function.support
      (MeromorphicOn.divisor riemannZeta (closedBall (2 + I * t) (8 / 5)))) :
    ρ ∈ riemannZetaZeroWindow (T + 1 / 2) (6 / 5) := by
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
    have h3 := (nearby_height_log_le hT ht).1
    linarith
  have hA := analyticOnNhd_riemannZeta_closedBall (nearby_height_log_le hT ht).1 ρ
    ((closedBall_subset_closedBall (by norm_num : (8 / 5 : ℝ) ≤ 7 / 4)) hmem)
  have hz : riemannZeta ρ = 0 := by
    by_contra hz
    exact hρ (hA.divisor_apply_eq_zero hz)
  have hhalf := hRH.re_eq_half_of_riemannZeta_eq_zero_of_re_pos hpos hz hne
  have hsq : ‖ρ - (2 + I * t)‖ ^ 2 ≤ (8 / 5 : ℝ) ^ 2 :=
    sq_le_sq' (by linarith [norm_nonneg (ρ - (2 + I * t))]) hd
  rw [Complex.sq_norm] at hsq
  norm_num [Complex.normSq_apply, hhalf] at hsq
  have him : |ρ.im - t| ≤ 3 / 5 := abs_le_of_sq_le_sq (by nlinarith) (by norm_num)
  have hmid : |t - (T + 1 / 2)| ≤ 1 / 2 :=
    abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
  refine ⟨hz, hpos, ?_⟩
  calc
    |ρ.im - (T + 1 / 2)| ≤ |ρ.im - t| + |t - (T + 1 / 2)| := abs_sub_le _ _ _
    _ ≤ 3 / 5 + 1 / 2 := add_le_add him hmid
    _ ≤ 6 / 5 := by norm_num

private lemma riemannZeta_ne_zero_of_separated_window
    {T t δ σ : ℝ} (ht : t ∈ Icc T (T + 1)) (hδ : 0 < δ) (hσ : 0 < σ)
    (hsep : ∀ ρ ∈ riemannZetaZeroWindow (T + 1 / 2) (6 / 5), δ ≤ |t - ρ.im|) :
    riemannZeta (σ + I * t) ≠ 0 := by
  intro hz
  have hmem : (σ : ℂ) + I * t ∈ riemannZetaZeroWindow (T + 1 / 2) (6 / 5) := by
    refine ⟨hz, by simpa using hσ, ?_⟩
    simp only [add_im, ofReal_im, mul_im, I_re, zero_mul, I_im, ofReal_re, one_mul, zero_add]
    rw [abs_le]
    constructor <;> linarith [ht.1, ht.2]
  have h := hsep _ hmem
  simp at h
  linarith

private lemma norm_logDeriv_le_at_separated_height (hRH : RiemannHypothesis)
    {T t δ A B L : ℝ} (hT : 5 ≤ T) (ht : t ∈ Icc T (T + 1))
    (hδ : 0 < δ) (hA : 0 < A) (hB : 0 < B) (hL : 0 < L)
    (hinv : δ⁻¹ ≤ A * Real.log T)
    (hsep : ∀ ρ ∈ riemannZetaZeroWindow (T + 1 / 2) (6 / 5), δ ≤ |t - ρ.im|)
    (hcount : ((∑ᶠ ρ, MeromorphicOn.divisor riemannZeta
      (closedBall (2 + I * t) (8 / 5)) ρ : ℤ) : ℝ) ≤ B * Real.log |t|)
    (hlocal : ∀ s : ℂ, ‖s - (2 + I * t)‖ ≤ 31 / 20 → riemannZeta s ≠ 0 →
      ‖logDeriv riemannZeta s - ∑ᶠ ρ, (MeromorphicOn.divisor riemannZeta
        (closedBall (2 + I * t) (8 / 5)) ρ : ℂ) / (s - ρ)‖ ≤ L * Real.log |t|)
    {σ : ℝ} (hσ : σ ∈ Icc (9 / 20 : ℝ) 2) :
    riemannZeta (σ + I * t) ≠ 0 ∧
      ‖logDeriv riemannZeta (σ + I * t)‖ ≤
        (2 * L / Real.log 5 + 2 * A * B) * Real.log T ^ 2 := by
  let s : ℂ := σ + I * t
  let D := MeromorphicOn.divisor riemannZeta (closedBall (2 + I * t) (8 / 5))
  have hζ : riemannZeta s ≠ 0 :=
    riemannZeta_ne_zero_of_separated_window ht hδ (by linarith [hσ.1]) hsep
  refine ⟨hζ, ?_⟩
  have hheight := nearby_height_log_le hT ht
  have hs : ‖s - (2 + I * t)‖ ≤ 31 / 20 := by
    have heq : s - (2 + I * t) = ((σ - 2 : ℝ) : ℂ) := by dsimp [s]; push_cast; ring
    rw [heq, norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith [hσ.1, hσ.2]
  have hf : AnalyticOnNhd ℂ riemannZeta (closedBall (2 + I * t) (8 / 5)) :=
    (analyticOnNhd_riemannZeta_closedBall hheight.1).mono
      (closedBall_subset_closedBall (by norm_num))
  have hfin : Function.HasFiniteSupport D := D.finiteSupport (isCompact_closedBall _ _)
  have hdist : ∀ ρ ∈ Function.support D, δ ≤ ‖s - ρ‖ := by
    intro ρ hρ
    have hw := divisor_support_mem_window hRH hT ht hρ
    have hi : |t - ρ.im| ≤ ‖s - ρ‖ := by simpa [s] using abs_im_le_norm (s - ρ)
    exact (hsep ρ hw).trans hi
  have hsum := Complex.norm_finsum_intCast_div_sub_le hfin
    (MeromorphicOn.AnalyticOnNhd.divisor_nonneg hf) hδ hdist
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have hlogt : 0 ≤ Real.log |t| := Real.log_nonneg (by linarith [hheight.1])
  have hsum' : ‖∑ᶠ ρ, (D ρ : ℂ) / (s - ρ)‖ ≤ 2 * A * B * Real.log T ^ 2 := by
    calc
      _ ≤ δ⁻¹ * ((∑ᶠ ρ, D ρ : ℤ) : ℝ) := hsum
      _ ≤ δ⁻¹ * (B * Real.log |t|) :=
        mul_le_mul_of_nonneg_left hcount (inv_nonneg.mpr hδ.le)
      _ ≤ (A * Real.log T) * (2 * B * Real.log T) :=
        mul_le_mul hinv (by nlinarith [hheight.2]) (mul_nonneg hB.le hlogt)
          (mul_nonneg hA.le hlogT)
      _ = _ := by ring
  have h5 : 0 < Real.log 5 := Real.log_pos (by norm_num)
  have h5T : Real.log 5 ≤ Real.log T := Real.log_le_log (by norm_num) hT
  have herror : L * Real.log |t| ≤ (2 * L / Real.log 5) * Real.log T ^ 2 := by
    have hlog : L * Real.log |t| ≤ 2 * L * Real.log T := by nlinarith [hheight.2]
    refine hlog.trans ?_
    rw [div_mul_eq_mul_div, le_div_iff₀ h5]
    nlinarith [mul_nonneg (show 0 ≤ 2 * L * Real.log T by positivity) (sub_nonneg.mpr h5T)]
  calc
    ‖logDeriv riemannZeta s‖ =
        ‖(logDeriv riemannZeta s - ∑ᶠ ρ, (D ρ : ℂ) / (s - ρ)) +
          ∑ᶠ ρ, (D ρ : ℂ) / (s - ρ)‖ := by rw [sub_add_cancel]
    _ ≤ ‖logDeriv riemannZeta s - ∑ᶠ ρ, (D ρ : ℂ) / (s - ρ)‖ +
        ‖∑ᶠ ρ, (D ρ : ℂ) / (s - ρ)‖ := norm_add_le _ _
    _ ≤ (2 * L / Real.log 5) * Real.log T ^ 2 + 2 * A * B * Real.log T ^ 2 :=
      add_le_add ((hlocal s hs hζ).trans herror) hsum'
    _ = _ := by ring

/-- Under RH, every unit interval at large positive height contains a zero-free horizontal
segment on which the logarithmic derivative of zeta is bounded by `C * log(T)^2`. -/
theorem exists_good_height (hRH : RiemannHypothesis) : ∃ C : ℝ, 0 < C ∧
    ∀ T : ℝ, 5 ≤ T → ∃ t ∈ Icc T (T + 1), ∀ σ ∈ Icc (9 / 20 : ℝ) 2,
      riemannZeta (σ + I * t) ≠ 0 ∧
        ‖logDeriv riemannZeta (σ + I * t)‖ ≤ C * Real.log T ^ 2 := by
  obtain ⟨A, hA, hsep⟩ := exists_separated_height hRH
  obtain ⟨B, hB, hcount⟩ := exists_sum_divisor_riemannZeta_le_log
  obtain ⟨L, hL, hlocal⟩ := exists_norm_logDeriv_riemannZeta_sub_divisor_le_log
  have h5 : 0 < Real.log 5 := Real.log_pos (by norm_num)
  refine ⟨2 * L / Real.log 5 + 2 * A * B, by positivity, fun T hT ↦ ?_⟩
  obtain ⟨t, ht, δ, hδ, hinv, hfar⟩ := hsep T hT
  refine ⟨t, ht, fun σ hσ ↦ ?_⟩
  have h3 := (nearby_height_log_le hT ht).1
  exact norm_logDeriv_le_at_separated_height hRH hT ht hδ hA hB hL hinv hfar
    (hcount t h3) (hlocal t h3) hσ

end RiemannHypothesis
