/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import Mathlib.Analysis.Meromorphic.Order
public import Mathlib.Analysis.Complex.Basic
import TauCeti.Analysis.Contour.Argument.Principle

/-!
# Logarithmic derivative limits at zeros and poles

The residue of the logarithmic derivative is the meromorphic order. Along a
vertical approach to a real zero, the scaled imaginary part of the negative
logarithmic derivative tends to the zero multiplicity.
-/

public section

open Complex Filter Set Topology

/-- Multiplying the logarithmic derivative by the displacement removes its simple
pole and gives the meromorphic order as the limiting value. -/
theorem MeromorphicAt.tendsto_sub_mul_logDeriv {f : ℂ → ℂ} {c : ℂ} {n : ℤ}
    (hf : MeromorphicAt f c) (hn : meromorphicOrderAt f c = (n : WithTop ℤ)) :
    Tendsto (fun z => (z - c) * _root_.logDeriv f z) (𝓝[≠] c) (𝓝 (n : ℂ)) := by
  obtain ⟨g, hg, hgn, heq⟩ := TauCeti.Contour.logDeriv_eventuallyEq_principalPart hf hn
  have hcont := (hg.logDeriv hgn).continuousAt
  have hlim : Tendsto (fun z => (n : ℂ) + (z - c) * _root_.logDeriv g z)
      (𝓝[≠] c) (𝓝 (n : ℂ)) := by
    simpa only [id_eq, sub_self, zero_mul, add_zero] using tendsto_const_nhds.add
      (((tendsto_id.sub_const c).mono_left nhdsWithin_le_nhds).mul
        (hcont.tendsto.mono_left nhdsWithin_le_nhds))
  apply hlim.congr'
  filter_upwards [heq, self_mem_nhdsWithin] with z hz hzc
  rw [hz]
  have hne : z - c ≠ 0 := sub_ne_zero.mpr hzc
  field_simp

/-- At a real point of finite meromorphic order, the scaled imaginary part of the
negative logarithmic derivative along the upper vertical ray tends to that order. -/
theorem MeromorphicAt.tendsto_mul_im_neg_logDeriv {f : ℂ → ℂ} {r : ℝ} {n : ℤ}
    (hf : MeromorphicAt f (r : ℂ))
    (hn : meromorphicOrderAt f (r : ℂ) = (n : WithTop ℤ)) :
    Tendsto (fun y : ℝ => y * (-_root_.logDeriv f ((r : ℂ) + (y : ℂ) * I)).im)
      (𝓝[>] (0 : ℝ)) (𝓝 (n : ℝ)) := by
  have hp : Tendsto (fun y : ℝ => (r : ℂ) + (y : ℂ) * I)
      (𝓝[>] (0 : ℝ)) (𝓝[≠] (r : ℂ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have hcont : Continuous (fun y : ℝ => (r : ℂ) + (y : ℂ) * I) := by fun_prop
      simpa using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with y hy
      intro heq
      have him := congrArg Complex.im heq
      simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, I_re,
        mul_one, mul_zero, zero_add, add_zero] at him
      exact (ne_of_gt hy) him
  have h := (hf.tendsto_sub_mul_logDeriv hn).comp hp
  have hr := Complex.continuous_re.continuousAt.tendsto.comp h
  convert hr using 1
  · ext y
    simp only [Function.comp_apply, add_sub_cancel_left, mul_re, mul_im,
      ofReal_re, ofReal_im, I_re, I_im, neg_im]
    ring

/-- The upper vertical logarithmic-derivative limit at an analytic point of
finite vanishing order is its natural zero multiplicity, including multiplicity zero. -/
theorem AnalyticAt.tendsto_mul_im_neg_logDeriv {f : ℂ → ℂ} {r : ℝ}
    (hf : AnalyticAt ℂ f (r : ℂ)) (hfin : analyticOrderAt f (r : ℂ) ≠ ⊤) :
    Tendsto (fun y : ℝ => y * (-_root_.logDeriv f ((r : ℂ) + (y : ℂ) * I)).im)
      (𝓝[>] (0 : ℝ)) (𝓝 (analyticOrderNatAt f (r : ℂ) : ℝ)) := by
  have hn : meromorphicOrderAt f (r : ℂ) =
      ((analyticOrderNatAt f (r : ℂ) : ℤ) : WithTop ℤ) := by
    rw [hf.meromorphicOrderAt_eq, ← Nat.cast_analyticOrderNatAt hfin]
    simp
  simpa only [Int.cast_natCast] using hf.meromorphicAt.tendsto_mul_im_neg_logDeriv hn
