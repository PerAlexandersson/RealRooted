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
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Integration by parts for polynomial weights on the positive half-line
-/

public section

open Set Filter
open scoped Topology

namespace MeasureTheory

/-- Integration by parts for a positive power, with both improper boundary values justified. -/
theorem integral_Ioi_pow_succ_mul_deriv_eq {w w' : ℝ → ℝ}
    (hcont : ContinuousAt w 0)
    (hd : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt w (w' t) t) (k : ℕ)
    (hw : IntegrableOn (fun t => t ^ k * w t) (Ioi (0 : ℝ)))
    (hw' : IntegrableOn (fun t => t ^ (k + 1) * w' t) (Ioi (0 : ℝ)))
    (hlim : Tendsto (fun t => t ^ (k + 1) * w t) atTop (𝓝 0)) :
    (∫ t in Ioi (0 : ℝ), t ^ (k + 1) * w' t) =
      -((k + 1 : ℕ) : ℝ) * ∫ t in Ioi (0 : ℝ), t ^ k * w t := by
  have hu (t : ℝ) (_ht : t ∈ Ioi (0 : ℝ)) :
      HasDerivAt (fun u : ℝ => u ^ (k + 1)) (((k + 1 : ℕ) : ℝ) * t ^ k) t := by
    simpa only [Nat.add_sub_cancel] using hasDerivAt_pow (k + 1) t
  have hi : IntegrableOn
      (fun t => (((k + 1 : ℕ) : ℝ) * t ^ k) * w t) (Ioi (0 : ℝ)) := by
    simpa only [IntegrableOn, mul_assoc] using hw.const_mul ((k + 1 : ℕ) : ℝ)
  have hz : Tendsto (fun t => t ^ (k + 1) * w t) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hc : ContinuousAt (fun t : ℝ => t ^ (k + 1) * w t) 0 :=
      (continuousAt_id.pow _).mul hcont
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  have h := integral_Ioi_mul_deriv_eq_deriv_mul hu hd hw' hi hz hlim
  simpa only [zero_sub, sub_zero, mul_assoc, integral_const_mul, neg_mul] using h

end MeasureTheory
