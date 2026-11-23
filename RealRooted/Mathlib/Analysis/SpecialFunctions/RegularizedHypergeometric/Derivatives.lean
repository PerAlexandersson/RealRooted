/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import TauCeti.Analysis.SpecialFunctions.RegularizedHypergeometric

/-!
# Taylor derivatives of regularized hypergeometric functions

The coefficient identity uses the actual entire function and is valid at
lower parameters that are nonpositive integers.
-/

public section

open scoped Nat

namespace Complex

/-- In the entire parameter range, the actual Taylor derivatives of a
regularized hypergeometric function are its normalized coefficients. -/
theorem iteratedDeriv_regularizedHGFun_zero {a b : Multiset ℂ}
    (hab : a.card ≤ b.card) (k : ℕ) :
    iteratedDeriv k (regularizedHGFun a b) 0 =
      (k.factorial : ℂ) * regularizedHGFunCoeff a b k := by
  have hp : 0 < (regularizedHGFunSeries a b).radius := by
    rw [radius_regularizedHGFunSeries_eq_top hab]
    simp
  have h := ((regularizedHGFunSeries a b).hasFPowerSeriesOnBall hp).factorial_smul 1 k
  simp only [FormalMultilinearSeries.apply_eq_prod_smul_coeff, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul, nsmul_eq_mul, one_pow,
    one_mul] at h
  rw [← iteratedDeriv_eq_iteratedFDeriv] at h
  have heq : (regularizedHGFunSeries a b).sum = regularizedHGFun a b := by
    funext z
    exact (regularizedHGFun.eq_def a b z).symm
  rw [heq] at h
  simpa only [regularizedHGFunSeries_coeff] using h.symm

/-- The derivatives of the entire regularized `₀F₁` at zero are reciprocal
Gamma values, including parameters at Gamma poles. -/
theorem iteratedDeriv_regularizedHGFun_zero_singleton (b : ℂ) (k : ℕ) :
    iteratedDeriv k (regularizedHGFun 0 {b}) 0 = (Gamma (b + k))⁻¹ := by
  rw [iteratedDeriv_regularizedHGFun_zero (by simp), regularizedHGFunCoeff_zero_singleton,
    mul_inv_rev, mul_left_comm, mul_inv_cancel₀ (by exact_mod_cast k.factorial_ne_zero),
    mul_one]

end Complex
