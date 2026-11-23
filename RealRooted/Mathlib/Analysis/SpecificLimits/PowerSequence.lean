/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Powers with a growing denominator

A positive power in the denominator makes the sequence
`(c / (n+1)^a)^n` summable for every real constant `c`.
-/

public section

open Filter Topology

namespace Real

/-- Raising a constant divided by a positive power of `n+1` to the nth power
gives an absolutely summable sequence, including zero or negative constants. -/
theorem summable_const_div_rpow_pow {a : ℝ} (ha : 0 < a) (c : ℝ) :
    Summable (fun n : ℕ => (c / ((n : ℝ) + 1) ^ a) ^ n) := by
  have htop : Tendsto (fun n : ℕ => ((n : ℝ) + 1) ^ a) atTop atTop :=
    (tendsto_rpow_atTop ha).comp
      (tendsto_atTop_add_const_right atTop 1 (tendsto_natCast_atTop_atTop (R := ℝ)))
  have hlim := htop.const_div_atTop |c|
  apply Summable.of_norm_bounded_eventually_nat
    (summable_geometric_of_abs_lt_one (by norm_num : |(1 / 2 : ℝ)| < 1))
  filter_upwards [hlim.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with n hn
  have hden : 0 < ((n : ℝ) + 1) ^ a := rpow_pos_of_pos (by positivity) a
  simp only [Real.norm_eq_abs, abs_pow, abs_div, abs_of_pos hden]
  exact pow_le_pow_left₀ (by positivity) hn.le n

end Real
