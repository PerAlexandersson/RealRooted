/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import RealRooted.Mathlib.MeasureTheory.Integral.Bochner.EvenMoments
import Mathlib.Tactic.Positivity.Finset
import RealRooted.Mathlib.Analysis.Convex.LogSqrtSlope

/-!
# Strict moment inequalities from log-concavity

This is the general positive-kernel implication used by Csordas and Varga,
*Moment Inequalities and the Riemann Hypothesis* (1988), Theorem 2.4.
The application to the Riemann xi kernel requires its separate analytic kernel
and normalization theorems.
-/

public section

open Set Filter Real
open scoped Topology

namespace MeasureTheory

/-- A positive rapidly decreasing weight whose logarithm is strictly concave after
square-root substitution satisfies every strict quadratic even-moment inequality. -/
theorem evenMoment_turan_lt_of_strictConcaveOn {w w' : ℝ → ℝ}
    (hcont : ContinuousAt w 0) (hpos : ∀ t ∈ Ioi (0 : ℝ), 0 < w t)
    (hd : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt w (w' t) t)
    (hc : StrictConcaveOn ℝ (Ioi (0 : ℝ)) (fun u => log (w (sqrt u))))
    (hm : ∀ k : ℕ, IntegrableOn (fun t => t ^ k * w t) (Ioi (0 : ℝ)))
    (hdm : ∀ k : ℕ, IntegrableOn (fun t => t ^ (k + 1) * w' t) (Ioi (0 : ℝ)))
    (hlim : ∀ k : ℕ, Tendsto (fun t => t ^ k * w t) atTop (𝓝 0)) (n : ℕ) :
    (2 * n + 1 : ℝ) * evenMoment w n * evenMoment w (n + 2) <
      (2 * n + 3 : ℝ) * evenMoment w (n + 1) ^ 2 :=
  evenMoment_turan_lt_of_strictMonoOn hcont hpos hd
    (hc.strictMonoOn_neg_deriv_div_mul hpos hd) hm hdm hlim n

end MeasureTheory
