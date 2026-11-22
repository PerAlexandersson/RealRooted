/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import TauCeti.Analysis.Complex.GrowthOrder

/-!
# Growth order from global exponential bounds

A global bound by a constant times an exponential power gives the corresponding
growth-order bound. No analyticity is required for this implication.
-/

public section

open Filter Asymptotics Bornology

namespace TauCeti

/-- A global exponential-power bound implies the corresponding order bound. -/
theorem orderLE_of_norm_le_mul_exp_rpow {f : ℂ → ℂ} {B C p : ℝ}
    (hbound : ∀ z, ‖f z‖ ≤ B * Real.exp (C * ‖z‖ ^ p)) : OrderLE f p := by
  rw [orderLE_def]
  intro q hpq
  apply (show f =O[cobounded ℂ] (fun z => Real.exp (C * ‖z‖ ^ p)) from ?_).trans
    (isBigO_exp_mul_norm_rpow C hpq)
  apply IsBigO.of_bound B
  exact Eventually.of_forall fun z => by
    simpa only [Real.norm_eq_abs, Real.abs_exp] using hbound z

end TauCeti
