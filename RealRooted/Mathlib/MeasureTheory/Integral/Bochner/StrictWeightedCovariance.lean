/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import RealRooted.Mathlib.MeasureTheory.Integral.Bochner.WeightedCovariance

/-!
# Strict covariance for increasing functions on a half-line

A positive weight and two strictly increasing functions give a strictly positive
covariance. The integrability hypotheses are exactly those needed by the
symmetrized integral identity.
-/

public section

open Set

namespace MeasureTheory

private theorem sub_mul_sub_nonneg {a : ℝ} {f g : ℝ → ℝ}
    (hf : MonotoneOn f (Ioi a)) (hg : MonotoneOn g (Ioi a))
    {x y : ℝ} (hx : x ∈ Ioi a) (hy : y ∈ Ioi a) :
    0 ≤ (f y - f x) * (g y - g x) := by
  rcases le_total x y with hxy | hyx
  · exact mul_nonneg (sub_nonneg.mpr (hf hx hy hxy))
      (sub_nonneg.mpr (hg hx hy hxy))
  · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr (hf hy hx hyx))
      (sub_nonpos.mpr (hg hy hx hyx))

private theorem restrict_volume_Ioo_pos {a b c : ℝ} (hab : a ≤ b) (hbc : b < c) :
    0 < volume.restrict (Ioi a) (Ioo b c) := by
  have hs : Ioo b c ⊆ Ioi a := fun _ hx => hab.trans_lt hx.1
  rw [Measure.restrict_apply measurableSet_Ioo, inter_eq_left.mpr hs]
  exact isOpen_Ioo.measure_pos volume (nonempty_Ioo.mpr hbc)

/-- Strictly increasing functions have a positive weighted covariance on a half-line. -/
theorem mul_integral_weighted_lt_of_strictMonoOn {a : ℝ} {w f g : ℝ → ℝ}
    (hwpos : ∀ x ∈ Ioi a, 0 < w x)
    (hf : StrictMonoOn f (Ioi a)) (hg : StrictMonoOn g (Ioi a))
    (hw : IntegrableOn w (Ioi a))
    (hwf : IntegrableOn (fun x => w x * f x) (Ioi a))
    (hwg : IntegrableOn (fun x => w x * g x) (Ioi a))
    (hwfg : IntegrableOn (fun x => w x * f x * g x) (Ioi a)) :
    (∫ x in Ioi a, w x * f x) * (∫ x in Ioi a, w x * g x) <
      (∫ x in Ioi a, w x) * (∫ x in Ioi a, w x * f x * g x) := by
  let μ := volume.restrict (Ioi a)
  let K (z : ℝ × ℝ) := w z.1 * w z.2 * (f z.2 - f z.1) * (g z.2 - g z.1)
  have hi : Integrable K (μ.prod μ) :=
    integrable_weight_mul_sub_mul_sub hw hwf hwg hwfg
  have hmem : ∀ᵐ z : ℝ × ℝ ∂μ.prod μ, z ∈ Ioi a ×ˢ Ioi a := by
    dsimp [μ]
    rw [Measure.prod_restrict]
    exact ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioi)
  have hn : 0 ≤ᵐ[μ.prod μ] K := by
    filter_upwards [hmem] with z hz
    dsimp [K]
    simpa only [mul_assoc] using mul_nonneg (hwpos z.1 hz.1).le
      (mul_nonneg (hwpos z.2 hz.2).le
        (sub_mul_sub_nonneg hf.monotoneOn hg.monotoneOn hz.1 hz.2))
  have hs : Ioo (a + 1) (a + 2) ×ˢ Ioo (a + 3) (a + 4) ⊆ Function.support K := by
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    have hx' : x ∈ Ioi a := by
      change a < x
      linarith [hx.1]
    have hy' : y ∈ Ioi a := by
      change a < y
      linarith [hy.1]
    have hxy : x < y := by linarith [hx.2, hy.1]
    exact (mul_pos (mul_pos (mul_pos (hwpos x hx') (hwpos y hy'))
      (sub_pos.mpr (hf hx' hy' hxy))) (sub_pos.mpr (hg hx' hy' hxy))).ne'
  have hspos : 0 < μ.prod μ (Ioo (a + 1) (a + 2) ×ˢ Ioo (a + 3) (a + 4)) := by
    rw [Measure.prod_prod]
    exact pos_iff_ne_zero.mpr (mul_ne_zero
      (restrict_volume_Ioo_pos (by linarith) (by linarith)).ne'
      (restrict_volume_Ioo_pos (by linarith) (by linarith)).ne')
  have hk : 0 < ∫ z, K z ∂μ.prod μ :=
    (integral_pos_iff_support_of_nonneg_ae hn hi).mpr (hspos.trans_le (measure_mono hs))
  have he := integral_weight_mul_sub_mul_sub hw hwf hwg hwfg
  change (∫ z, K z ∂μ.prod μ) = _ at he
  rw [he] at hk
  linarith

end MeasureTheory
