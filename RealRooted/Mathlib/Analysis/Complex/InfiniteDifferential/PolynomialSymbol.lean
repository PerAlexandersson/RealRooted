/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import RealRooted.Mathlib.Analysis.Complex.InfiniteDifferential.Basic
public import RealRooted.Mathlib.Analysis.Calculus.IteratedDeriv.Polynomial
import RealRooted.Mathlib.Analysis.Complex.PolynomialLimitCoeff

/-!
# Polynomial symbols are finite differential operators
-/

public section

open Polynomial

namespace Complex

/-- A polynomial symbol has a finite differential series for every target,
without any differentiability or growth assumptions on the target. -/
theorem infiniteDifferentialApply_polynomial (P : ℂ[X]) (f : ℂ → ℂ) :
    infiniteDifferentialApply (fun z ↦ P.eval z) f = P.differentialApply f := by
  ext z
  simp only [infiniteDifferentialApply, Polynomial.iteratedDeriv_fun_eval,
    Polynomial.eval_zero_iterate_derivative]
  have hterm (n : ℕ) :
      ((n.factorial : ℂ) * P.coeff n) * iteratedDeriv n f z / n.factorial =
        P.coeff n * iteratedDeriv n f z := by
    have hn : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
    field_simp [hn]
  simp_rw [hterm]
  rw [tsum_eq_sum (s := Finset.range (P.natDegree + 1)) (fun n hn ↦ ?_)]
  · rfl
  · have hd : P.natDegree < n := Nat.lt_of_not_ge (by
      simpa only [Finset.mem_range, Nat.lt_succ_iff] using hn)
    rw [coeff_eq_zero_of_natDegree_lt hd, zero_mul]

end Complex
