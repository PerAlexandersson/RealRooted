/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import TauCeti.MeasureTheory.Integral.Exp.Decay
import Mathlib.Tactic.Ring

/-!
# Laplace moments of nonnegative exponential mixtures

A summable weighted inverse moment justifies both the actual integrability
and the exchange of the spectral sum and the Laplace integral. Zero weights
and an empty spectrum are allowed. The Laplace parameter may be zero.
-/

public section

open MeasureTheory Set

namespace Real

/-- Nonnegative shifts preserve summability of weighted inverse moments. -/
theorem summable_mul_factorial_div_add_pow {ι : Type*} {r w : ι → ℝ}
    (hr : ∀ i, 0 < r i) (hw : ∀ i, 0 ≤ w i) (n : ℕ)
    (hs : Summable (fun i ↦ w i / r i ^ (n + 1)))
    {x : ℝ} (hx : 0 ≤ x) :
    Summable (fun i ↦ w i * (n.factorial : ℝ) / (x + r i) ^ (n + 1)) := by
  apply Summable.of_nonneg_of_le
    (fun i ↦ div_nonneg (mul_nonneg (hw i) (Nat.cast_nonneg _))
      (pow_nonneg (add_nonneg hx (hr i).le) _)) ?_ (hs.mul_left (n.factorial : ℝ))
  intro i
  calc
    w i * (n.factorial : ℝ) / (x + r i) ^ (n + 1) ≤
        w i * (n.factorial : ℝ) / r i ^ (n + 1) :=
      div_le_div_of_nonneg_left (mul_nonneg (hw i) (Nat.cast_nonneg _))
        (pow_pos (hr i) _) (pow_le_pow_left₀ (hr i).le (le_add_of_nonneg_left hx) _)
    _ = _ := by ring

/-- A nonnegative exponential mixture has its expected Laplace moment,
with actual integrability even when every weight is zero. -/
theorem integrableOn_and_integral_exp_mul_pow_mul_tsum
    {ι : Type*} [Countable ι] {r w : ι → ℝ}
    (hr : ∀ i, 0 < r i) (hw : ∀ i, 0 ≤ w i) (n : ℕ)
    (hs : Summable (fun i ↦ w i / r i ^ (n + 1)))
    {x : ℝ} (hx : 0 ≤ x) :
    IntegrableOn (fun t : ℝ ↦ exp (-x * t) * t ^ n *
        ∑' i, w i * exp (-r i * t)) (Ioi 0) ∧
      (∫ t : ℝ in Ioi 0, exp (-x * t) * t ^ n *
        ∑' i, w i * exp (-r i * t)) =
          ∑' i, w i * (n.factorial : ℝ) / (x + r i) ^ (n + 1) := by
  have hpos (i : ι) : 0 < x + r i := add_pos_of_nonneg_of_pos hx (hr i)
  have hint (i : ι) : IntegrableOn
      (fun t : ℝ ↦ w i * (t ^ n * exp (-((x + r i) * t)))) (Ioi 0) :=
    (TauCeti.integrableOn_pow_mul_exp_neg_mul_Ioi n (hpos i)).const_mul (w i)
  have heval (i : ι) :
      (∫ t : ℝ in Ioi 0, w i * (t ^ n * exp (-((x + r i) * t)))) =
        w i * (n.factorial : ℝ) / (x + r i) ^ (n + 1) := by
    rw [integral_const_mul, TauCeti.integral_pow_mul_exp_neg_mul_Ioi n (hpos i)]
    ring
  have hnorm (i : ι) :
      (∫ t : ℝ in Ioi 0, ‖w i * (t ^ n * exp (-((x + r i) * t)))‖) =
        w i * (n.factorial : ℝ) / (x + r i) ^ (n + 1) := by
    rw [← heval i]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 0 < t)
    exact Real.norm_of_nonneg
      (mul_nonneg (hw i) (mul_nonneg (pow_nonneg ht.le _) (exp_nonneg _)))
  have hsx := summable_mul_factorial_div_add_pow hr hw n hs hx
  have hnormsum : Summable
      (fun i ↦ ∫ t : ℝ in Ioi 0, ‖w i * (t ^ n * exp (-((x + r i) * t)))‖) := by
    simpa only [hnorm] using hsx
  have hfun : (fun t : ℝ ↦ ∑' i, w i * (t ^ n * exp (-((x + r i) * t)))) =
      (fun t : ℝ ↦ exp (-x * t) * t ^ n * ∑' i, w i * exp (-r i * t)) := by
    funext t
    calc
      _ = ∑' i, (exp (-x * t) * t ^ n) * (w i * exp (-r i * t)) := by
        apply tsum_congr
        intro i
        simp only [add_mul, neg_add, exp_add, neg_mul]
        ring
      _ = _ := by rw [tsum_mul_left]
  have heq :
      (∫ t : ℝ in Ioi 0, exp (-x * t) * t ^ n * ∑' i, w i * exp (-r i * t)) =
        ∑' i, w i * (n.factorial : ℝ) / (x + r i) ^ (n + 1) := by
    rw [← hfun, ← integral_tsum_of_summable_integral_norm hint hnormsum]
    simp only [heval]
  refine ⟨?_, heq⟩
  by_cases h : ∃ i, 0 < w i
  · obtain ⟨i, hi⟩ := h
    apply Integrable.of_integral_ne_zero
    rw [heq]
    exact (hsx.tsum_pos
      (fun j ↦ div_nonneg (mul_nonneg (hw j) (Nat.cast_nonneg _))
        (pow_nonneg (hpos j).le _)) i
      (div_pos (mul_pos hi (by exact_mod_cast Nat.factorial_pos n))
        (pow_pos (hpos i) _))).ne'
  · have hwzero : ∀ i, w i = 0 := by
      intro i
      exact le_antisymm (le_of_not_gt (fun hi ↦ h ⟨i, hi⟩)) (hw i)
    simp only [hwzero, zero_mul, tsum_zero, mul_zero]
    exact integrableOn_zero

end Real
