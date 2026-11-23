/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import RealRooted.Mathlib.RingTheory.Polynomial.Laguerre.Basic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Rodrigues identities for natural generalized Laguerre parameters

The division-free identity is valid at every real argument, including zero,
and for every real exponential rate. Its normalized form matches equations
(2.19)--(2.20) of Zhang, arXiv:1506.07012v13, for the natural parameters used
in his two-index hierarchy. The repository polynomial already includes `k!`.
-/

public section

open Finset

namespace Polynomial

/-- The exponential-polynomial Rodrigues derivative equals the monic,
sign-reversed generalized Laguerre evaluation, including at argument zero. -/
theorem iteratedDeriv_exp_mul_pow_eq_generalizedLaguerre
    (k m : ℕ) (c x : ℝ) :
    iteratedDeriv k (fun y : ℝ ↦ Real.exp (-c * y) * y ^ (k + m)) x =
      Real.exp (-c * x) * x ^ m * (generalizedLaguerre k (m : ℝ)).eval (-c * x) := by
  have he : ContDiffAt ℝ k (fun y : ℝ ↦ Real.exp (-c * y)) x := by fun_prop
  have hp : ContDiffAt ℝ k (fun y : ℝ ↦ y ^ (k + m)) x := by fun_prop
  rw [iteratedDeriv_fun_mul he hp]
  simp only [iteratedDeriv_exp_const_mul, iteratedDeriv_pow,
    generalizedLaguerre, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X, mul_sum]
  apply sum_congr rfl
  intro j hj
  have hjk : j ≤ k := Nat.lt_succ_iff.mp (mem_range.mp hj)
  have hpoch : (ascPochhammer ℝ (k - j)).eval ((m : ℝ) + j + 1) =
      ((k + m).descFactorial (k - j) : ℝ) := by
    rw [show (m : ℝ) + j + 1 = ((m + j + 1 : ℕ) : ℝ) by push_cast; ring,
      ascPochhammer_nat_eq_natCast_descFactorial]
    rw [show m + j + 1 + (k - j) - 1 = k + m by lia]
  rw [hpoch, show k + m - (k - j) = m + j by lia, pow_add, mul_pow]
  ring

/-- The normalized Rodrigues formula. The factorial is already included
in `generalizedLaguerre`, so no additional factor occurs on the right. -/
theorem generalizedLaguerre_eval_eq_rodrigues
    (k m : ℕ) (c : ℝ) {x : ℝ} (hx : x ≠ 0) :
    (generalizedLaguerre k (m : ℝ)).eval (-c * x) =
      Real.exp (c * x) / x ^ m *
        iteratedDeriv k (fun y : ℝ ↦ Real.exp (-c * y) * y ^ (k + m)) x := by
  rw [iteratedDeriv_exp_mul_pow_eq_generalizedLaguerre, neg_mul, Real.exp_neg]
  field_simp [hx, Real.exp_ne_zero]

end Polynomial
