/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import TauCeti.Analysis.Complex.GrowthOrder

/-!
# Growth order after polynomial factor removal

Outside a bounded set, the inverse of a nonzero polynomial is bounded.
Removing that factor therefore preserves every upper growth-order bound.
-/

public section

open Complex Polynomial Filter Asymptotics Bornology

namespace TauCeti

/-- Removing a nonzero polynomial factor does not increase growth order. -/
theorem OrderLE.of_polynomial_mul {f : ℂ → ℂ} {p : ℂ[X]} {rho : ℝ}
    (h : OrderLE (fun z => p.eval z * f z) rho) (hp : p ≠ 0) : OrderLE f rho := by
  have hpoly : (fun _ : ℂ => (1 : ℂ)) =O[cobounded ℂ] p.eval := by
    simpa only [eval_one] using
      (Polynomial.isBigO_cobounded_of_degree_le (P := (1 : ℂ[X])) (Q := p)
        (by simpa only [degree_one] using (zero_le_degree_iff.mpr hp)))
  simpa only [one_mul] using (hpoly.mul (isBigO_refl f (cobounded ℂ))).orderLE h

end TauCeti
