/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

import Mathlib.Analysis.MellinTransform
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import TauCeti.Analysis.MellinTransform.UpperTail
import Mathlib.Analysis.Complex.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Logarithmic moments of rapidly decreasing Mellin kernels

Every derivative of an upper Mellin integral is obtained by multiplying its
kernel by the corresponding power of the logarithm.
-/

public section

open Complex Set Filter MeasureTheory Asymptotics
open scoped Topology

private theorem isBigO_mul_log_pow {f : ℝ → ℂ}
    (hf : ∀ r : ℝ, f =O[atTop] fun t => t ^ r) (n : ℕ) (r : ℝ) :
    (fun t => f t * (Real.log t : ℂ) ^ n) =O[atTop] fun t => t ^ r := by
  have hl : (fun t : ℝ => (Real.log t : ℂ) ^ n) =O[atTop] fun t => t ^ (1 : ℝ) := by
    simpa only [← ofReal_pow, isBigO_ofReal_left, Real.rpow_natCast] using
      (isLittleO_log_rpow_rpow_atTop (n : ℝ) (by norm_num : (0 : ℝ) < 1)).isBigO
  refine ((hf (r - 1)).mul hl).congr' EventuallyEq.rfl ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  rw [← Real.rpow_add ht]
  congr 1
  ring

private theorem continuousOn_mul_log_pow {f : ℝ → ℂ}
    (hf : ContinuousOn f (Ici 1)) (n : ℕ) :
    ContinuousOn (fun t => f t * (Real.log t : ℂ) ^ n) (Ici 1) :=
  hf.mul ((continuous_ofReal.comp_continuousOn
    (Real.continuousOn_log.mono (fun _ ht => ne_of_gt (zero_lt_one.trans_le ht)))).pow n)

/-- All logarithmic moments of a rapidly decreasing continuous kernel are integrable. -/
theorem integrableOn_mul_log_pow_cpow {f : ℝ → ℂ}
    (hc : ContinuousOn f (Ici 1)) (hO : ∀ r : ℝ, f =O[atTop] fun t => t ^ r)
    (n : ℕ) (s : ℂ) :
    IntegrableOn (fun t : ℝ => f t * (Real.log t : ℂ) ^ n * (t : ℂ) ^ (s - 1))
      (Ioi 1) := by
  have h := TauCeti.integrableOn_mul_cpow_of_isBigO
    ((continuousOn_mul_log_pow hc n).locallyIntegrableOn measurableSet_Ici)
    (isBigO_mul_log_pow hO n ((-s).re - 1)) (s := -s) (sub_one_lt _)
  simpa only [neg_add_rev, neg_neg, sub_eq_add_neg, add_comm] using h

/-- Differentiation adds one logarithmic factor to an upper Mellin integral. -/
theorem hasDerivAt_integral_mul_log_pow_cpow {f : ℝ → ℂ}
    (hc : ContinuousOn f (Ici 1)) (hO : ∀ r : ℝ, f =O[atTop] fun t => t ^ r)
    (n : ℕ) (s : ℂ) :
    HasDerivAt (fun z : ℂ => ∫ t in Ioi (1 : ℝ),
      f t * (Real.log t : ℂ) ^ n * (t : ℂ) ^ (z - 1))
      (∫ t in Ioi (1 : ℝ), f t * (Real.log t : ℂ) ^ (n + 1) * (t : ℂ) ^ (s - 1)) s := by
  have h := (TauCeti.hasDerivAt_integral_mul_cpow_of_isBigO
    ((continuousOn_mul_log_pow hc n).locallyIntegrableOn measurableSet_Ici)
    (isBigO_mul_log_pow hO n ((-s).re - 1)) (s := -s) (sub_one_lt _)).comp s
      (hasDerivAt_id' s).neg
  simpa only [Function.comp_def, neg_add_rev, neg_neg, neg_mul, mul_neg,
    mul_one, neg_neg, sub_eq_add_neg, add_comm, pow_succ, mul_assoc] using h

/-- Iterated differentiation under a rapidly decreasing upper Mellin integral. -/
theorem iteratedDeriv_integral_mul_cpow {f : ℝ → ℂ}
    (hc : ContinuousOn f (Ici 1)) (hO : ∀ r : ℝ, f =O[atTop] fun t => t ^ r)
    (n : ℕ) (s : ℂ) :
    iteratedDeriv n (fun z : ℂ => ∫ t in Ioi (1 : ℝ), f t * (t : ℂ) ^ (z - 1)) s =
      ∫ t in Ioi (1 : ℝ), f t * (Real.log t : ℂ) ^ n * (t : ℂ) ^ (s - 1) := by
  induction n generalizing s with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, funext ih]
    exact (hasDerivAt_integral_mul_log_pow_cpow hc hO n s).deriv

/-- Real logarithmic moments with arbitrary real power weights are integrable. -/
theorem integrableOn_mul_log_pow_rpow {f : ℝ → ℝ}
    (hc : ContinuousOn f (Ici 1)) (hO : ∀ r : ℝ, f =O[atTop] fun t => t ^ r)
    (n : ℕ) (r : ℝ) :
    IntegrableOn (fun t : ℝ => f t * Real.log t ^ n * t ^ r) (Ioi 1) := by
  have h := (integrableOn_mul_log_pow_cpow
    (continuous_ofReal.comp_continuousOn hc)
    (fun r => isBigO_ofReal_left.mpr (hO r)) n ((r : ℂ) + 1)).re
  refine h.congr_fun (fun t ht => ?_) measurableSet_Ioi
  simp only [Function.comp_apply, add_sub_cancel_right, ← ofReal_pow,
    ← ofReal_cpow (zero_lt_one.trans ht).le, ← ofReal_mul]
  rfl

/-- Multiplication by logarithmic and power weights preserves vanishing at infinity
for a rapidly decreasing function. -/
theorem tendsto_mul_log_pow_rpow_zero {f : ℝ → ℝ}
    (hO : ∀ r : ℝ, f =O[atTop] fun t => t ^ r) (n : ℕ) (r : ℝ) :
    Tendsto (fun t : ℝ => f t * Real.log t ^ n * t ^ r) atTop (𝓝 0) := by
  have hlog : (fun t => f t * Real.log t ^ n) =O[atTop] fun t => t ^ (-r - 1) := by
    have h := isBigO_mul_log_pow (fun r => isBigO_ofReal_left.mpr (hO r)) n (-r - 1)
    simpa only [← ofReal_pow, ← ofReal_mul, isBigO_ofReal_left] using h
  have hprod := hlog.mul (isBigO_refl (fun t : ℝ => t ^ r) atTop)
  have hpow : (fun t : ℝ => t ^ (-r - 1) * t ^ r) =ᶠ[atTop] fun t => t ^ (-1 : ℝ) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    rw [← Real.rpow_add ht]
    congr 1
    ring
  exact (hprod.congr' EventuallyEq.rfl hpow).trans_tendsto (tendsto_rpow_neg_atTop one_pos)
