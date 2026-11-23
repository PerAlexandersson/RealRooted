/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Log-concavity after the square-root substitution

Strict concavity of `log (w (sqrt t))` makes `-w' / (t * w)` strictly increasing.
Only first derivatives of the weight are required.
-/

public section

open Set Real

namespace StrictConcaveOn

/-- Strict log-concavity after a square-root substitution gives an increasing scaled
logarithmic slope on the positive half-line. -/
theorem strictMonoOn_neg_deriv_div_mul {w w' : ℝ → ℝ}
    (hc : StrictConcaveOn ℝ (Ioi (0 : ℝ)) (fun u => log (w (sqrt u))))
    (hw : ∀ t ∈ Ioi (0 : ℝ), 0 < w t)
    (hd : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt w (w' t) t) :
    StrictMonoOn (fun t => -(w' t) / (t * w t)) (Ioi (0 : ℝ)) := by
  have hF (u : ℝ) (hu : u ∈ Ioi (0 : ℝ)) :
      HasDerivAt (fun v => log (w (sqrt v)))
        ((w (sqrt u))⁻¹ * (w' (sqrt u) * (1 / (2 * sqrt u)))) u := by
    exact (hasDerivAt_log (hw _ (sqrt_pos.mpr hu)).ne').comp u
      ((hd _ (sqrt_pos.mpr hu)).comp u (hasDerivAt_sqrt hu.ne'))
  have ha := hc.strictAntiOn_deriv (fun u hu => (hF u hu).differentiableAt)
  have he (t : ℝ) (ht : t ∈ Ioi (0 : ℝ)) :
      -(w' t) / (t * w t) = -2 * deriv (fun u => log (w (sqrt u))) (t ^ 2) := by
    rw [(hF (t ^ 2) (sq_pos_of_pos ht)).deriv, sqrt_sq ht.le]
    field_simp [ht.ne', (hw t ht).ne']
  intro x hx y hy hxy
  change -(w' x) / (x * w x) < -(w' y) / (y * w y)
  rw [he x hx, he y hy]
  have hsq : x ^ 2 < y ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr hxy) (add_pos hx hy)]
  have h := ha (sq_pos_of_pos hx) (sq_pos_of_pos hy) hsq
  linarith

end StrictConcaveOn
