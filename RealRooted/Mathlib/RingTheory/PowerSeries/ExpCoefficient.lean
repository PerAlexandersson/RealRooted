/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.Exp

import Mathlib.Tactic.TypeStar

/-!
# Factorial coefficients of rescaled formal exponentials
-/

public section

namespace PowerSeries

/-- Over a characteristic-zero field the rescaled exponential coefficient has
the ordinary factorial normalization. -/
theorem coeff_rescale_exp {R : Type*} [Field R] [Algebra ℚ R]
    (a : R) (n : ℕ) :
    coeff n (rescale a (exp R)) = a ^ n / (n.factorial : R) := by
  rw [coeff_rescale, coeff_exp, map_div₀, map_one, map_natCast, mul_one_div]

end PowerSeries
