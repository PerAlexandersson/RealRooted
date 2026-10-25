/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.Topology.Algebra.Polynomial

/-!
# Continuity of translated real polynomials

`Polynomial.continuous_coeff_comp_X_add_C` states that, for a real polynomial `p` and an index `i`,
the map `r ↦ (p.comp (X + C r)).coeff i` is continuous on `ℝ`.
-/

@[expose] public section

open Polynomial

namespace Polynomial

/-- Every coefficient of a translated real polynomial varies continuously
with the translation parameter. -/
theorem continuous_coeff_comp_X_add_C (p : ℝ[X]) (i : ℕ) :
    Continuous fun r : ℝ ↦ (p.comp (X + C r)).coeff i := by
  rw [show (fun r : ℝ ↦ (p.comp (X + C r)).coeff i) =
      fun r : ℝ ↦ ∑ n ∈ p.support,
        (C (p.coeff n) * (X + C r) ^ n).coeff i by
    funext r
    rw [Polynomial.comp_eq_sum_left, Polynomial.sum_def,
      Polynomial.finsetSum_coeff]]
  apply continuous_finsetSum p.support
  intro n _hn
  simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_add_C_pow]
  fun_prop

end Polynomial
