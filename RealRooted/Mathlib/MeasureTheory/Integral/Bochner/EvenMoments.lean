/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.Positivity.Finset
import RealRooted.Mathlib.MeasureTheory.Integral.Bochner.StrictWeightedCovariance
import RealRooted.Mathlib.MeasureTheory.Integral.IntegralEqImproper.Power

/-!
# Strict Turán inequalities for even moments

The increasing logarithmic slope `-w' / (t * w)` gives strict Turán inequalities
for the even moments of a positive weight. This is the integral argument in
Csordas and Varga, *Moment Inequalities and the Riemann Hypothesis* (1988),
Proposition 2.2 and the first proof of Theorem 2.4.
-/

public section

open Set Filter
open scoped Topology

namespace MeasureTheory

/-- The even moments of a real weight on the positive half-line. -/
@[expose] noncomputable def evenMoment (w : ℝ → ℝ) (n : ℕ) : ℝ :=
  ∫ t in Ioi (0 : ℝ), t ^ (2 * n) * w t

private theorem pow_mul_neg_div_mul {w w' : ℝ → ℝ} (k : ℕ) {t : ℝ}
    (ht : t ≠ 0) (hw : w t ≠ 0) :
    t ^ (k + 1) * w t * (-(w' t) / (t * w t)) = -t ^ k * w' t := by
  rw [pow_succ]
  field_simp [ht, hw]

private theorem moment_times_square (w : ℝ → ℝ) (n : ℕ) (t : ℝ) :
    (t ^ (2 * (n + 1)) * w t) * t ^ 2 = t ^ (2 * (n + 2)) * w t := by
  rw [show 2 * (n + 2) = 2 * (n + 1) + 2 by lia, pow_add]
  ring

/-- Positive weights with increasing scaled logarithmic slope have strict even-moment
Turán inequalities. All polynomial moments and the derivative moments used in integration
by parts are integrable, and the weight decays faster than every natural power. -/
theorem evenMoment_turan_lt_of_strictMonoOn {w w' : ℝ → ℝ}
    (hcont : ContinuousAt w 0) (hpos : ∀ t ∈ Ioi (0 : ℝ), 0 < w t)
    (hd : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt w (w' t) t)
    (hmono : StrictMonoOn (fun t => -(w' t) / (t * w t)) (Ioi (0 : ℝ)))
    (hm : ∀ k : ℕ, IntegrableOn (fun t => t ^ k * w t) (Ioi (0 : ℝ)))
    (hdm : ∀ k : ℕ, IntegrableOn (fun t => t ^ (k + 1) * w' t) (Ioi (0 : ℝ)))
    (hlim : ∀ k : ℕ, Tendsto (fun t => t ^ k * w t) atTop (𝓝 0)) (n : ℕ) :
    (2 * n + 1 : ℝ) * evenMoment w n * evenMoment w (n + 2) <
      (2 * n + 3 : ℝ) * evenMoment w (n + 1) ^ 2 := by
  let W (t : ℝ) := t ^ (2 * (n + 1)) * w t
  let H (t : ℝ) := -(w' t) / (t * w t)
  have hWH (t : ℝ) (ht : t ∈ Ioi (0 : ℝ)) :
      W t * H t = -t ^ (2 * n + 1) * w' t := by
    dsimp [W, H]
    rw [show 2 * (n + 1) = (2 * n + 1) + 1 by lia]
    exact pow_mul_neg_div_mul _ ht.ne' (hpos t ht).ne'
  have hWsH (t : ℝ) (ht : t ∈ Ioi (0 : ℝ)) :
      W t * t ^ 2 * H t = -t ^ (2 * n + 3) * w' t := by
    rw [moment_times_square]
    dsimp [H]
    rw [show 2 * (n + 2) = (2 * n + 3) + 1 by lia]
    exact pow_mul_neg_div_mul _ ht.ne' (hpos t ht).ne'
  have hW : IntegrableOn W (Ioi (0 : ℝ)) := hm _
  have hWs : IntegrableOn (fun t => W t * t ^ 2) (Ioi (0 : ℝ)) := by
    simpa only [W, moment_times_square] using hm (2 * (n + 2))
  have hWHint : IntegrableOn (fun t => W t * H t) (Ioi (0 : ℝ)) := by
    apply ((hdm (2 * n)).neg).congr_fun _ measurableSet_Ioi
    intro t ht
    simpa only [Pi.neg_apply, neg_mul] using (hWH t ht).symm
  have hWsHint : IntegrableOn (fun t => W t * t ^ 2 * H t) (Ioi (0 : ℝ)) := by
    have hi := (hdm (2 * n + 2)).neg
    apply hi.congr_fun _ measurableSet_Ioi
    intro t ht
    simpa only [Pi.neg_apply, show 2 * n + 2 + 1 = 2 * n + 3 by lia, neg_mul]
      using (hWsH t ht).symm
  have hs : StrictMonoOn (fun t : ℝ => t ^ 2) (Ioi (0 : ℝ)) := by
    intro x hx y hy hxy
    nlinarith [mul_pos (sub_pos.mpr hxy) (add_pos hx hy)]
  have h := mul_integral_weighted_lt_of_strictMonoOn
    (fun t ht => mul_pos (pow_pos ht _) (hpos t ht)) hs hmono hW hWs hWHint hWsHint
  have hi₀ : (∫ t in Ioi (0 : ℝ), W t * H t) =
      (2 * n + 1 : ℝ) * evenMoment w n := by
    rw [setIntegral_congr_fun measurableSet_Ioi hWH]
    simp_rw [neg_mul]
    rw [integral_neg, integral_Ioi_pow_succ_mul_deriv_eq hcont hd (2 * n) (hm _) (hdm _) (hlim _)]
    simp only [evenMoment, neg_mul, neg_neg, Nat.cast_add, Nat.cast_mul,
      Nat.cast_ofNat, Nat.cast_one]
  have hi₁ : (∫ t in Ioi (0 : ℝ), W t * t ^ 2 * H t) =
      (2 * n + 3 : ℝ) * evenMoment w (n + 1) := by
    rw [setIntegral_congr_fun measurableSet_Ioi hWsH]
    simp_rw [neg_mul]
    have hp := integral_Ioi_pow_succ_mul_deriv_eq hcont hd (2 * n + 2) (hm _) (hdm _) (hlim _)
    rw [show 2 * n + 3 = (2 * n + 2) + 1 by lia, integral_neg, hp]
    simp only [neg_mul, neg_neg, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    rw [show 2 * n + 2 = 2 * (n + 1) by lia]
    change (2 * (n : ℝ) + 2 + 1) * evenMoment w (n + 1) = _
    ring
  have hi₂ : (∫ t in Ioi (0 : ℝ), W t * t ^ 2) = evenMoment w (n + 2) := by
    simp only [W, moment_times_square, evenMoment]
  rw [hi₀, hi₁, hi₂] at h
  change evenMoment w (n + 2) * _ < evenMoment w (n + 1) * _ at h
  nlinarith

end MeasureTheory
