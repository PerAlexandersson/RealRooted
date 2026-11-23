/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
import RealRooted.Mathlib.Analysis.SpecificLimits.WeightedSum
import RealRooted.Mathlib.Analysis.SpecialFunctions.Choose

/-!
# Regularity of falling-factorial weights

The finite Jensen weights `(n)_k / n^k` decrease with `k`, vanish past `n`,
and tend to one for each fixed `k`. They therefore preserve ordinary
conditionally convergent series.
-/

public section

open Finset Filter Topology

namespace Nat

/-- The normalized falling factorial is decreasing in its lower index. The
convention at `n = 0` uses the usual zero inverse. -/
theorem antitone_descFactorial_div_pow (n : ℕ) :
    Antitone (fun k => (n.descFactorial k : ℝ) / (n : ℝ) ^ k) := by
  apply antitone_nat_of_succ_le
  intro k
  by_cases hn : n = 0
  · subst n
    cases k <;> simp
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  rw [descFactorial_succ, Nat.cast_mul, pow_succ]
  calc
    ((n - k : ℕ) : ℝ) * n.descFactorial k / ((n : ℝ) ^ k * n) =
        (((n - k : ℕ) : ℝ) / n) * ((n.descFactorial k : ℝ) / (n : ℝ) ^ k) := by ring
    _ ≤ 1 * ((n.descFactorial k : ℝ) / (n : ℝ) ^ k) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact (div_le_one hnpos).mpr (by exact_mod_cast Nat.sub_le n k)
    _ = _ := one_mul _

/-- Falling-factorial finite means preserve the sum of a conditionally
convergent ordinary series in a real normed vector space. -/
theorem tendsto_sum_descFactorial_smul {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {u : ℕ → E} {a : E}
    (hu : Tendsto (fun n => ∑ k ∈ range n, u k) atTop (𝓝 a)) :
    Tendsto (fun n => ∑ k ∈ range (n + 1),
      ((n.descFactorial k : ℝ) / (n : ℝ) ^ k) • u k) atTop (𝓝 a) := by
  apply tendsto_weighted_series_of_antitone antitone_descFactorial_div_pow
    (fun n => by simp) _ tendsto_descFactorial_div_pow_atTop hu
  intro n
  rw [descFactorial_eq_zero_iff_lt.mpr (Nat.lt_succ_self n)]
  simp

end Nat
