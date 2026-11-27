/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import RealRooted.CombinatorialExamples.CatalanWordPeaks.LogSectors
public import Mathlib.MeasureTheory.Integral.Bochner.Set
import RealRooted.CombinatorialExamples.CatalanWordPeaks.LogarithmicContour
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic

/-!
# The exact four-ray coefficient formula

Continue the coefficient integrand across the four radial cuts, deform its
Cauchy circle to the cut edges, and integrate the exact square-root jumps.

Source: ProgramComputer, *Strict peaks in Catalan words*, coefficient formula
and finite-certificate method, ISC license. Copyright 2026 ProgramComputer

Permission to use, copy, modify, and/or distribute this software for any
purpose with or without fee is hereby granted, provided that the above
copyright notice and this permission notice appear in all copies.

THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY
SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN ACTION
OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF OR IN
CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
-/

@[expose] public noncomputable section

namespace RealRooted.CatalanWordPeaks.CutGeometry

open Complex Set MeasureTheory Filter
open scoped ComplexConjugate Interval Topology

/-- The finite deformation isolates the outer arcs and the four jump integrals
in logarithmic radius. -/
private theorem analyticGenerating_finiteDeformation {d : ℝ} (hd : 0 < d) (hD : d < 1)
    {r : NNReal} (h₀ : 0 < r) (hr : (r : ℝ) < radius d) (n : ℕ)
    {b : ℝ} (hb : Real.log r ≤ b) :
    ((scale d ^ n * (polynomial n).eval (1 - (scale d ^ 2)⁻¹) : ℝ) : ℂ) =
      (2 * (Real.pi : ℂ) * I)⁻¹ * (
        (∑ j ∈ Finset.range 5,
          I • (∫ y in sectorAngle d j..sectorAngle d (j + 1),
            logSector d n j ((b : ℂ) + (y : ℂ) * I))) +
        ∑ j ∈ Finset.range 4, (
          ∫ x in Real.log r..b,
            logSector d n (j + 1) ((x : ℂ) + (sectorAngle d (j + 1) : ℂ) * I) -
              logSector d n j ((x : ℂ) + (sectorAngle d (j + 1) : ℂ) * I))) := by
  have h₀R : 0 < (r : ℝ) := by exact_mod_cast h₀
  let inner : ℝ → ℂ := fun y => logIntegrand d n ((Real.log r : ℂ) + (y : ℂ) * I)
  have hTransport := RealRooted.CatalanWordPeaks.LogarithmicContour.deform (m := 4) hb
    (sectorAngle d) (sectorAngle_mono hd hD) (logSector d n) inner
    (fun j hj => (logSector_continuousOn hd hD hj n).mono fun z hz => hz.2)
    (fun j hj => (logSector_differentiableOn hd hD hj n).mono fun z hz => hz.2)
    (by
      intro j hj y hy
      have hIm : (((Real.log r : ℂ) + (y : ℂ) * I)).im = y := by simp [Complex.mul_im]
      have he : ‖exp ((Real.log r : ℂ) + (y : ℂ) * I)‖ = (r : ℝ) := by
        simp [Complex.norm_exp, Complex.mul_re, Real.exp_log h₀R]
      have hR := he.le.trans hr.le
      simp only [logSector, inner, logIntegrand, analyticGenerating,
        logBranch_eq_branch_inner hd hD hj (hIm.symm ▸ hy) hR])
    (fun j _ => (logIntegrand_continuous_on_circle hd hD h₀R hr n).intervalIntegrable _ _)
    (by
      intro x _
      simpa only [sectorAngle, Complex.ofReal_zero, zero_mul, add_zero]
        using logSector_periodic_boundary d n x)
  have hAngular := RealRooted.CatalanWordPeaks.LogarithmicContour.circleIntegral_eq_angular
    (analyticGenerating d) (Real.log r) n
  rw [Real.exp_log h₀R] at hAngular
  rw [analyticGenerating_cauchyCoeff hd hD h₀ hr n, hAngular]
  exact congrArg ((2 * (Real.pi : ℂ) * I)⁻¹ * ·) hTransport

private def onCut (d : ℝ) (j : Fin 4) (x : ℝ) : ℂ :=
  (x : ℂ) + (sectorAngle d (j.val + 1) : ℂ) * I

private def otherFactors (d : ℝ) (j : Fin 4) (x : ℝ) : ℂ :=
  ∏ i ∈ Finset.univ.erase j, sectorFactor d j.val i (onCut d j x)

private theorem sectorFactor_forward (d : ℝ) (j : Fin 4) (x : ℝ) :
    sectorFactor d (j.val + 1) j (onCut d j x) = logStripRoot ‖cutPoint d j‖ (x : ℂ) := by
  simp only [sectorFactor, onCut, liftedAngle, Nat.lt_succ_self, ite_true, add_sub_cancel_right]

private theorem sectorFactor_backward (d : ℝ) (j : Fin 4) (x : ℝ) :
    sectorFactor d j.val j (onCut d j x) =
      logStripRoot ‖cutPoint d j‖ ((x : ℂ) + (2 * Real.pi : ℝ) * I) := by
  simp only [sectorFactor, onCut, liftedAngle, lt_irrefl, ite_false]
  congr 1
  push_cast
  ring

private theorem logBranch_cut_difference (d : ℝ) (j : Fin 4) (x : ℝ) :
    logBranch d (j.val + 1) (onCut d j x) - logBranch d j.val (onCut d j x) =
      (logStripRoot ‖cutPoint d j‖ (x : ℂ) -
        logStripRoot ‖cutPoint d j‖ ((x : ℂ) + (2 * Real.pi : ℝ) * I)) * otherFactors d j x := by
  have hprod :
      (∏ i ∈ Finset.univ.erase j, sectorFactor d (j.val + 1) i (onCut d j x)) =
        otherFactors d j x := by
    unfold otherFactors
    apply Finset.prod_congr rfl
    intro i hi
    have hij : i.val ≠ j.val := fun h => (Finset.mem_erase.mp hi).1 (Fin.ext h)
    have h : (i.val < j.val + 1) ↔ i.val < j.val := by lia
    simp only [sectorFactor, liftedAngle, h]
  have hSplit (k : ℕ) :
      logBranch d k (onCut d j x) = sectorFactor d k j (onCut d j x) *
        ∏ i ∈ Finset.univ.erase j, sectorFactor d k i (onCut d j x) :=
    (Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)).symm
  rw [hSplit, hSplit, hprod, sectorFactor_forward, sectorFactor_backward, sub_mul]
  rfl

private theorem logSector_eq_quotient {d : ℝ} (hd : 0 < d) (hD : d < 1)
    (n : ℕ) {j : ℕ} (hj : j ≤ 4) {z : ℂ}
    (hz : z.im ∈ Icc (sectorAngle d j) (sectorAngle d (j + 1)))
    (hzc : exp z ≠ (scale d : ℂ)) :
    logSector d n j z = (exp z)⁻¹ ^ n *
      ((1 - (exp z) ^ 2 - logBranch d j z) / (2 * exp z * ((scale d : ℂ) - exp z))) := by
  unfold logSector
  congr 1
  have hDen := logGenerating_denominator_ne_zero hd hD hj hz
  have hSub := sub_ne_zero.mpr hzc.symm
  apply (div_eq_div_iff hDen (mul_ne_zero (mul_ne_zero (by norm_num) (exp_ne_zero z)) hSub)).mpr
  have hsq := logBranch_sq hd hD hj hz
  unfold quartic at hsq
  linear_combination hsq

private theorem logSector_cut_difference {d : ℝ} (hd : 0 < d) (hD : d < 1)
    (n : ℕ) (j : Fin 4) (x : ℝ) :
    logSector d n (j.val + 1) (onCut d j x) - logSector d n j.val (onCut d j x) =
      (exp (onCut d j x))⁻¹ ^ n *
        ((logStripRoot ‖cutPoint d j‖ (x : ℂ) -
          logStripRoot ‖cutPoint d j‖ ((x : ℂ) + (2 * Real.pi : ℝ) * I)) *
          (-otherFactors d j x / (2 * exp (onCut d j x) *
            ((scale d : ℂ) - exp (onCut d j x))))) := by
  let z := onCut d j x
  have hy : z.im = sectorAngle d (j.val + 1) := by simp [z, onCut, Complex.mul_im]
  have h₁ : j.val ≤ 4 := j.isLt.le
  have h₂ : j.val + 1 ≤ 4 := Nat.succ_le_of_lt j.isLt
  have hz₁ : z.im ∈ Icc (sectorAngle d j.val) (sectorAngle d (j.val + 1)) :=
    hy.symm ▸ ⟨(sectorAngle_step hd hD h₁).le, le_rfl⟩
  have hz₂ : z.im ∈ Icc (sectorAngle d (j.val + 1)) (sectorAngle d (j.val + 1 + 1)) :=
    hy.symm ▸ ⟨le_rfl, (sectorAngle_step hd hD h₂).le⟩
  have hzc : exp z ≠ (scale d : ℂ) := by
    intro he
    apply exp_im_ne_zero_on_cut hd hD j.val j z
    · right
      simp [hy, liftedAngle]
    · simp [he]
  change logSector d n (j.val + 1) z - logSector d n j.val z = _
  rw [logSector_eq_quotient hd hD n h₂ hz₂ hzc, logSector_eq_quotient hd hD n h₁ hz₁ hzc,
    ← mul_sub, ← sub_div]
  rw [show 1 - (exp z) ^ 2 - logBranch d (j.val + 1) z -
      (1 - (exp z) ^ 2 - logBranch d j.val z) =
        -(logBranch d (j.val + 1) z - logBranch d j.val z) by ring]
  dsimp [z]
  rw [logBranch_cut_difference]
  ring

private theorem large_quotient_norm_le {c : ℝ} (hc : 0 ≤ c) (hc₁ : c ≤ 1)
    {z B : ℂ} (hz : 2 ≤ ‖z‖) (hB : B ^ 2 = quartic c z) :
    ‖(1 - z ^ 2 - B) / (2 * z * ((c : ℂ) - z))‖ ≤ 5 := by
  let r := ‖z‖
  have hr : 2 ≤ r := hz
  have hcNorm : ‖(c : ℂ)‖ = c := by simp [abs_of_nonneg hc]
  have hp : ‖1 + z ^ 2‖ ≤ 1 + r ^ 2 := by
    calc
      _ ≤ ‖(1 : ℂ)‖ + ‖z ^ 2‖ := norm_add_le _ _
      _ = _ := by rw [norm_one, Complex.norm_pow]
  have hBsq : ‖B‖ ^ 2 ≤ (1 + r ^ 2) ^ 2 + 4 * r := by
    rw [← norm_pow, hB, quartic]
    refine (norm_sub_le _ _).trans ?_
    simp only [norm_pow, norm_mul, Complex.norm_ofNat, hcNorm]
    exact add_le_add (pow_le_pow_left₀ (norm_nonneg _) hp 2)
      (by nlinarith [mul_nonneg (norm_nonneg z) (sub_nonneg.mpr hc₁)])
  have hBn : ‖B‖ ≤ r ^ 2 + 2 :=
    (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
      (hBsq.trans (by nlinarith [sq_nonneg (r - 1)]))
  have hNum : ‖1 - z ^ 2 - B‖ ≤ 5 * r ^ 2 := by
    have hp' : ‖1 - z ^ 2‖ ≤ 1 + r ^ 2 := by
      calc
        _ ≤ ‖(1 : ℂ)‖ + ‖z ^ 2‖ := norm_sub_le _ _
        _ = _ := by rw [norm_one, Complex.norm_pow]
    exact (norm_sub_le _ _).trans (by nlinarith [sq_nonneg (r - 1)])
  have hgap : r - c ≤ ‖(c : ℂ) - z‖ := by
    simpa only [hcNorm, norm_sub_rev] using norm_sub_norm_le z (c : ℂ)
  have hDen : r ^ 2 ≤ ‖2 * z * ((c : ℂ) - z)‖ := by
    simp only [norm_mul, Complex.norm_ofNat]
    nlinarith [mul_nonneg (norm_nonneg z) (sub_nonneg.mpr hgap),
      mul_nonneg (norm_nonneg z) (show 0 ≤ r - 2 * c by linarith)]
  rw [norm_div]
  exact (div_le_iff₀ ((pow_pos (by linarith : 0 < r) 2).trans_le hDen)).mpr
    (hNum.trans (by nlinarith))

/-- The coefficient integrand decays exponentially in the logarithmic radius. -/
private theorem logSector_norm_le_large {d : ℝ} (hd : 0 < d) (hD : d < 1)
    (n : ℕ) {j : ℕ} (hj : j ≤ 4) {z : ℂ}
    (hz : z.im ∈ Icc (sectorAngle d j) (sectorAngle d (j + 1)))
    (hlarge : Real.log 2 ≤ z.re) :
    ‖logSector d n j z‖ ≤ 5 * Real.exp (-(n : ℝ) * z.re) := by
  have hc := scale_pos hd
  have hc₁ : scale d ≤ 1 := by nlinarith [scale_sq_lt_one hd hD]
  have hnorm : 2 ≤ ‖exp z‖ := by
    rw [norm_exp, ← Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    exact Real.exp_le_exp.mpr hlarge
  have hne : exp z ≠ (scale d : ℂ) := by
    intro heq
    rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc.le] at hnorm
    linarith
  rw [logSector_eq_quotient hd hD n hj hz hne, norm_mul, norm_pow, norm_inv]
  calc
    _ ≤ ‖exp z‖⁻¹ ^ n * 5 := mul_le_mul_of_nonneg_left
      (large_quotient_norm_le hc.le hc₁ hnorm (logBranch_sq hd hD hj hz)) (by positivity)
    _ = _ := by
      rw [norm_exp, ← Real.exp_neg, ← Real.exp_nat_mul, mul_neg, neg_mul, mul_comm]

private def outerArcs (d : ℝ) (n : ℕ) (b : ℝ) : ℂ :=
  ∑ j ∈ Finset.range 5,
    I • (∫ y in sectorAngle d j..sectorAngle d (j + 1),
      logSector d n j ((b : ℂ) + (y : ℂ) * I))

private theorem outerArcs_norm_le {d : ℝ} (hd : 0 < d) (hD : d < 1)
    (n : ℕ) {b : ℝ} (hb : Real.log 2 ≤ b) :
    ‖outerArcs d n b‖ ≤ 10 * Real.pi * Real.exp (-(n : ℝ) * b) := by
  unfold outerArcs
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ j ∈ Finset.range 5,
        (5 * Real.exp (-(n : ℝ) * b)) * (sectorAngle d (j + 1) - sectorAngle d j) := by
      apply Finset.sum_le_sum
      intro j hj
      have hj' : j ≤ 4 := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hj
      have ho := (sectorAngle_step hd hD hj').le
      rw [norm_smul, Complex.norm_I, one_mul, ← abs_of_nonneg (sub_nonneg.mpr ho)]
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro y hy
      rw [uIoc_of_le ho] at hy
      simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_I_re,
        Complex.ofReal_im, neg_zero, add_zero] using
        logSector_norm_le_large hd hD n hj' (z := (b : ℂ) + (y : ℂ) * I)
          (by simpa using And.intro hy.1.le hy.2) (by simpa using hb)
    _ = _ := by rw [← Finset.mul_sum, Finset.sum_range_sub]; simp only [sectorAngle]; ring

private theorem outerArcs_tendsto_zero {d : ℝ} (hd : 0 < d) (hD : d < 1)
    {n : ℕ} (hn : 0 < n) : Tendsto (outerArcs d n) atTop (𝓝 0) := by
  have hExp : Tendsto (fun b : ℝ => Real.exp (-(n : ℝ) * b)) atTop (𝓝 0) := by
    simpa [Function.comp_def, neg_mul] using Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_id.const_mul_atTop (Nat.cast_pos.mpr hn : (0 : ℝ) < n))
  have hBound : Tendsto (fun b : ℝ => 10 * Real.pi * Real.exp (-(n : ℝ) * b)) atTop (𝓝 0) := by
    simpa using (hExp.const_mul (10 * Real.pi))
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hBound
  filter_upwards [eventually_ge_atTop (Real.log 2)] with b hb
  exact outerArcs_norm_le hd hD n hb

/-- The outward radial boundary difference in logarithmic coordinates. -/
private def logRayJump (d : ℝ) (n j : ℕ) (x : ℝ) : ℂ :=
  let z := (x : ℂ) + (sectorAngle d (j + 1) : ℂ) * I
  logSector d n (j + 1) z - logSector d n j z

private theorem logSector_continuous_on_ray {d : ℝ} (hd : 0 < d) (hD : d < 1)
    (n : ℕ) {j : ℕ} (hj : j ≤ 4) {y : ℝ}
    (hy : y ∈ Icc (sectorAngle d j) (sectorAngle d (j + 1))) :
    Continuous (fun x : ℝ => logSector d n j ((x : ℂ) + (y : ℂ) * I)) := by
  have hMap : Continuous (fun x : ℝ => (x : ℂ) + (y : ℂ) * I) := by fun_prop
  apply (logSector_continuousOn hd hD hj n).comp_continuous hMap
  intro x
  simpa [Complex.mul_im] using hy

private theorem logRayJump_continuous {d : ℝ} (hd : 0 < d) (hD : d < 1)
    (n : ℕ) {j : ℕ} (hj : j < 4) : Continuous (logRayJump d n j) := by
  exact (logSector_continuous_on_ray hd hD n (Nat.succ_le_of_lt hj)
    ⟨le_rfl, (sectorAngle_step hd hD (Nat.succ_le_of_lt hj)).le⟩).sub
    (logSector_continuous_on_ray hd hD n hj.le
      ⟨(sectorAngle_step hd hD hj.le).le, le_rfl⟩)

private theorem logRayJump_norm_le_large {d : ℝ} (hd : 0 < d) (hD : d < 1)
    (n : ℕ) {j : ℕ} (hj : j < 4) {x : ℝ} (hx : Real.log 2 ≤ x) :
    ‖logRayJump d n j x‖ ≤ 10 * Real.exp (-(n : ℝ) * x) := by
  let z := (x : ℂ) + (sectorAngle d (j + 1) : ℂ) * I
  have hIm : z.im = sectorAngle d (j + 1) := by simp [z, Complex.mul_im]
  have hRe : z.re = x := by simp [z, Complex.mul_re]
  have h₁ : z.im ∈ Icc (sectorAngle d j) (sectorAngle d (j + 1)) := hIm.symm ▸
    ⟨(sectorAngle_step hd hD hj.le).le, le_rfl⟩
  have h₂ : z.im ∈ Icc (sectorAngle d (j + 1)) (sectorAngle d (j + 1 + 1)) := hIm.symm ▸
    ⟨le_rfl, (sectorAngle_step hd hD (Nat.succ_le_of_lt hj)).le⟩
  calc
    _ ≤ ‖logSector d n (j + 1) z‖ + ‖logSector d n j z‖ := norm_sub_le _ _
    _ ≤ 5 * Real.exp (-(n : ℝ) * z.re) + 5 * Real.exp (-(n : ℝ) * z.re) :=
      add_le_add (logSector_norm_le_large hd hD n (Nat.succ_le_of_lt hj) h₂ (hRe.symm ▸ hx))
        (logSector_norm_le_large hd hD n hj.le h₁ (hRe.symm ▸ hx))
    _ = _ := by rw [hRe]; ring

/-- Each logarithmic jump is absolutely integrable to infinity for positive indices. -/
private theorem logRayJump_integrable {d : ℝ} (hd : 0 < d) (hD : d < 1) {n : ℕ} (hn : 0 < n)
    {j : ℕ} (hj : j < 4) (a : ℝ) : IntegrableOn (logRayJump d n j) (Ioi a) := by
  let cutoff := max a (Real.log 2)
  have hCont := logRayJump_continuous hd hD n hj
  have hDecay : -(n : ℝ) < 0 := neg_neg_of_pos (Nat.cast_pos.mpr hn)
  have hNear : IntegrableOn (logRayJump d n j) (Icc a cutoff) :=
    hCont.continuousOn.integrableOn_Icc
  have hFar : IntegrableOn (logRayJump d n j) (Ioi cutoff) := by
    refine (Integrable.const_mul (integrableOn_exp_mul_Ioi hDecay cutoff) 10).mono'
      hCont.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem (measurableSet_Ioi (a := cutoff))] with x hx
    exact logRayJump_norm_le_large hd hD n hj
      ((le_max_right a (Real.log 2)).trans hx.le)
  apply (hNear.union hFar).mono_set
  intro x hx
  by_cases h : x ≤ cutoff
  · exact Or.inl ⟨hx.le, h⟩
  · exact Or.inr (lt_of_not_ge h)

/-- The outer arcs vanish and only the four improper logarithmic jumps remain. -/
private theorem analyticGenerating_logarithmicRays {d : ℝ} (hd : 0 < d) (hD : d < 1)
    {r : NNReal} (h₀ : 0 < r) (hr : (r : ℝ) < radius d) {n : ℕ} (hn : 0 < n) :
    ((scale d ^ n * (polynomial n).eval (1 - (scale d ^ 2)⁻¹) : ℝ) : ℂ) =
      (2 * (Real.pi : ℂ) * I)⁻¹ *
        ∑ j ∈ Finset.range 4, (∫ x in Ioi (Real.log r), logRayJump d n j x) := by
  let a := Real.log (r : ℝ)
  let coefficient : ℂ := ((scale d ^ n * (polynomial n).eval (1 - (scale d ^ 2)⁻¹) : ℝ) : ℂ)
  let normalizer : ℂ := (2 * (Real.pi : ℂ) * I)⁻¹
  have hJumps : Tendsto (fun b : ℝ => ∑ j ∈ Finset.range 4,
      (∫ x in a..b, logRayJump d n j x)) atTop
      (𝓝 (∑ j ∈ Finset.range 4, (∫ x in Ioi a, logRayJump d n j x))) :=
    tendsto_finsetSum _ fun j hj =>
      intervalIntegral_tendsto_integral_Ioi a (logRayJump_integrable hd hD hn
        (Finset.mem_range.mp hj) a) tendsto_id
  have hTotal : Tendsto (fun b : ℝ => normalizer *
      (outerArcs d n b + ∑ j ∈ Finset.range 4, (∫ x in a..b, logRayJump d n j x))) atTop
      (𝓝 (normalizer * ∑ j ∈ Finset.range 4, (∫ x in Ioi a, logRayJump d n j x))) := by
    simpa using ((outerArcs_tendsto_zero hd hD hn).add hJumps).const_mul normalizer
  have hEventually :
      (fun b : ℝ => normalizer *
        (outerArcs d n b + ∑ j ∈ Finset.range 4, (∫ x in a..b, logRayJump d n j x))) =ᶠ[atTop]
      fun _ : ℝ => coefficient := by
    filter_upwards [eventually_ge_atTop a] with b hb
    exact (analyticGenerating_finiteDeformation hd hD h₀ hr n hb).symm
  exact tendsto_nhds_unique tendsto_const_nhds (hTotal.congr' hEventually)

private theorem sectorAngle_strict {d : ℝ} (hd : 0 < d) (hD : d < 1)
    {i j : ℕ} (hij : i < j) (hj : j ≤ 5) : sectorAngle d i < sectorAngle d j :=
  (sectorAngle_step hd hD (show i ≤ 4 by lia)).trans_le
    (sectorAngle_mono hd hD (Nat.succ_le_of_lt hij))

private theorem otherFactors_principal {d : ℝ} (hd : 0 < d) (hD : d < 1)
    (j : Fin 4) (x : ℝ) :
    otherFactors d j x =
      ∏ i ∈ Finset.univ.erase j, cutFactor (cutPoint d i) (exp (onCut d j x)) := by
  unfold otherFactors
  apply Finset.prod_congr rfl
  intro i hi
  have hne : i.val ≠ j.val := fun h => (Finset.mem_erase.mp hi).1 (Fin.ext h)
  have hIm : (onCut d j x).im = sectorAngle d (j.val + 1) := by simp [onCut, Complex.mul_im]
  have h₀ (p : Fin 4) : 0 < sectorAngle d (p.val + 1) :=
    sectorAngle_strict hd hD (Nat.zero_lt_succ _) (by lia)
  have hπ (p : Fin 4) : sectorAngle d (p.val + 1) < 2 * Real.pi := by
    exact sectorAngle_strict hd hD (show p.val + 1 < 5 by lia) le_rfl
  have hLift :
      liftedAngle d j.val i < (onCut d j x).im ∧
        (onCut d j x).im < liftedAngle d j.val i + 2 * Real.pi := by
    rw [hIm]
    unfold liftedAngle
    split_ifs with h
    · exact ⟨sectorAngle_strict hd hD (by lia) (by lia), by linarith [h₀ i, hπ j]⟩
    · refine ⟨by linarith [hπ i, h₀ j], ?_⟩
      have hLT := sectorAngle_strict hd hD (show j.val + 1 < i.val + 1 by lia) (by lia)
      linarith
  rw [sectorFactor, logStripRoot_eq_cutFactor (cutPoint_norm_pos hd hD i) hLift.1 hLift.2,
    liftedAngle_polar hd hD]

private theorem exp_onCut {d : ℝ} (hd : 0 < d) (hD : d < 1)
    (j : Fin 4) (x : ℝ) :
    exp (onCut d j x) = cutPoint d j * ((Real.exp x / ‖cutPoint d j‖ : ℝ) : ℂ) := by
  have hR : (‖cutPoint d j‖ : ℂ) ≠ 0 := by exact_mod_cast (cutPoint_norm_pos hd hD j).ne'
  let e := exp ((sectorAngle d (j.val + 1) : ℂ) * I)
  calc
    exp (onCut d j x) = (Real.exp x : ℂ) * e := by simp [onCut, e, exp_add, ofReal_exp]
    _ = ((‖cutPoint d j‖ : ℂ) * e) * ((Real.exp x / ‖cutPoint d j‖ : ℝ) : ℂ) := by
      push_cast
      field_simp [hR]
    _ = _ := by rw [show (‖cutPoint d j‖ : ℂ) * e = cutPoint d j from cutPoint_polar hd hD j]

/-- The analytic factor of a ray jump with its singular square root omitted. -/
def rayPrefactor (d : ℝ) (j : Fin 4) (z : ℂ) : ℂ :=
  -(∏ i ∈ Finset.univ.erase j, cutFactor (cutPoint d i) z) /
    (2 * z * ((scale d : ℂ) - z))

/-- The normalized radial integrand in the coefficient identity. -/
def rayIntegrand (d : ℝ) (n : ℕ) (j : Fin 4) (s : ℝ) : ℂ :=
  (Real.sqrt s : ℂ) * (1 + (s : ℂ))⁻¹ ^ (n + 1) *
    rayPrefactor d j (cutPoint d j * (1 + (s : ℂ)))

private theorem real_exp_log_cut {d : ℝ} (hd : 0 < d) (hD : d < 1)
    (j : Fin 4) {s : ℝ} (hs : 0 ≤ s) :
    Real.exp (Real.log (‖cutPoint d j‖ * (1 + s))) / ‖cutPoint d j‖ = 1 + s := by
  have hR := cutPoint_norm_pos hd hD j
  rw [Real.exp_log (mul_pos hR (by linarith))]
  exact mul_div_cancel_left₀ _ hR.ne'

/-- The logarithmic jump including the Jacobian equals the normalized radial integrand. -/
private theorem logRayJump_eq_normalized {d : ℝ} (hd : 0 < d) (hD : d < 1)
    (n : ℕ) (j : Fin 4) {s : ℝ} (hs : 0 ≤ s) :
    (1 + s)⁻¹ • logRayJump d n j.val (Real.log (‖cutPoint d j‖ * (1 + s))) =
      (-2 * I) * (cutPoint d j)⁻¹ ^ n * rayIntegrand d n j s := by
  let x := Real.log (‖cutPoint d j‖ * (1 + s))
  have hScale : Real.exp x / ‖cutPoint d j‖ = 1 + s := real_exp_log_cut hd hD j hs
  have hOut : 1 ≤ Real.exp x / ‖cutPoint d j‖ := by rw [hScale]; linarith
  change (1 + s)⁻¹ •
    (logSector d n (j.val + 1) (onCut d j x) - logSector d n j.val (onCut d j x)) = _
  rw [logSector_cut_difference hd hD, logStripRoot_jump _ _ hOut,
    otherFactors_principal hd hD, exp_onCut hd hD, hScale]
  rw [show 1 + s - 1 = s by ring]
  simp only [rayIntegrand, rayPrefactor, Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_add,
    Complex.ofReal_one, mul_inv_rev, mul_pow, pow_succ]
  ring

private theorem logRayJump_vanishes_inward {d : ℝ} (hd : 0 < d) (hD : d < 1)
    (n : ℕ) (j : Fin 4) {x : ℝ} (hx : x ≤ Real.log ‖cutPoint d j‖) :
    logRayJump d n j.val x = 0 := by
  have hR := cutPoint_norm_pos hd hD j
  have hIn : Real.exp x / ‖cutPoint d j‖ ≤ 1 :=
    (div_le_one hR).mpr (by simpa only [Real.exp_log hR] using Real.exp_le_exp.mpr hx)
  change logSector d n (j.val + 1) (onCut d j x) -
    logSector d n j.val (onCut d j x) = 0
  rw [logSector_cut_difference hd hD, logStripRoot_boundary_eq _ _ hIn,
    sub_self, zero_mul, mul_zero]

private theorem logRayJump_integral_cutoff {d : ℝ} (hd : 0 < d) (hD : d < 1)
    (n : ℕ) (j : Fin 4) {a : ℝ} (ha : a ≤ Real.log ‖cutPoint d j‖) :
    (∫ x in Ioi a, logRayJump d n j.val x) =
      ∫ x in Ioi (Real.log ‖cutPoint d j‖), logRayJump d n j.val x := by
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi (Ioi_subset_Ioi ha)
  intro x hx
  exact logRayJump_vanishes_inward hd hD n j (le_of_not_gt hx.2)

private theorem normalizedRay_integral_data {d : ℝ} (hd : 0 < d) (hD : d < 1)
    {n : ℕ} (hn : 0 < n) (j : Fin 4) :
    IntegrableOn (rayIntegrand d n j) (Ioi 0) ∧
      (∫ x in Ioi (Real.log ‖cutPoint d j‖), logRayJump d n j.val x) =
        (-2 * I) * (cutPoint d j)⁻¹ ^ n * ∫ s in Ioi 0, rayIntegrand d n j s := by
  let R := ‖cutPoint d j‖
  let scaleFactor := (-2 * I) * (cutPoint d j)⁻¹ ^ n
  have hR : 0 < R := cutPoint_norm_pos hd hD j
  have hz : cutPoint d j ≠ 0 := norm_pos_iff.mp hR
  have hScale : scaleFactor ≠ 0 := mul_ne_zero
    (mul_ne_zero (by norm_num) I_ne_zero) (pow_ne_zero _ (inv_ne_zero hz))
  let f : ℝ → ℂ := fun s => (1 + s)⁻¹ • logRayJump d n j.val (Real.log (R * (1 + s)))
  have hSub : IntegrableOn f (Ioi 0) ∧
      (∫ x in Ioi (Real.log R), logRayJump d n j.val x) = ∫ s in Ioi 0, f s :=
    RealRooted.CatalanWordPeaks.LogarithmicContour.integral_logRadius_improper hR
      (logRayJump_integrable hd hD hn j.isLt (Real.log R))
  have hEq : EqOn f (fun s => scaleFactor * rayIntegrand d n j s) (Ioi 0) :=
    fun s hs => logRayJump_eq_normalized hd hD n j (le_of_lt hs)
  have hi : IntegrableOn (fun s ↦ scaleFactor * rayIntegrand d n j s) (Ioi 0) :=
    hSub.1.congr_fun hEq measurableSet_Ioi
  refine ⟨(integrable_const_mul_iff (isUnit_iff_ne_zero.mpr hScale) _).mp hi, ?_⟩
  rw [hSub.2, setIntegral_congr_fun measurableSet_Ioi hEq, MeasureTheory.integral_const_mul]

/-- Each normalized ray integrand is absolutely integrable. -/
theorem rayIntegrand_integrable {d : ℝ} (hd : 0 < d) (hD : d < 1)
    {n : ℕ} (hn : 0 < n) (j : Fin 4) : IntegrableOn (rayIntegrand d n j) (Ioi 0) :=
  (normalizedRay_integral_data hd hD hn j).1

/-- The exact Catalan coefficient as the sum of the four improper ray integrals. -/
theorem analyticGenerating_fourRays {d : ℝ} (hd : 0 < d) (hD : d < 1)
    {n : ℕ} (hn : 0 < n) :
    ((scale d ^ n * (polynomial n).eval (1 - (scale d ^ 2)⁻¹) : ℝ) : ℂ) =
      ∑ j : Fin 4, (-((cutPoint d j)⁻¹ ^ n) / (Real.pi : ℂ)) *
        ∫ s in Ioi 0, rayIntegrand d n j s := by
  let r : NNReal := ⟨radius d / 2, div_nonneg (radius_pos hd.le).le (by norm_num)⟩
  have h₀R : 0 < (r : ℝ) := div_pos (radius_pos hd.le) (by norm_num)
  have h₀ : 0 < r := by exact_mod_cast h₀R
  have hr : (r : ℝ) < radius d := half_lt_self (radius_pos hd.le)
  rw [analyticGenerating_logarithmicRays hd hD h₀ hr hn, ← Fin.sum_univ_eq_sum_range,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have hRadius : Real.log (r : ℝ) ≤ Real.log ‖cutPoint d j‖ :=
    Real.log_le_log h₀R (hr.le.trans (radius_le_cutPoint hd hD j))
  rw [logRayJump_integral_cutoff hd hD n j hRadius, (normalizedRay_integral_data hd hD hn j).2]
  have hπI : (2 * (Real.pi : ℂ) * I)⁻¹ * (-2 * I) = -(Real.pi : ℂ)⁻¹ := by
    field_simp [I_ne_zero, Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]
  calc
    _ = ((2 * (Real.pi : ℂ) * I)⁻¹ * (-2 * I)) * ((cutPoint d j)⁻¹ ^ n *
        ∫ s in Ioi 0, rayIntegrand d n j s) := by ring
    _ = _ := by rw [hπI]; ring

end RealRooted.CatalanWordPeaks.CutGeometry
