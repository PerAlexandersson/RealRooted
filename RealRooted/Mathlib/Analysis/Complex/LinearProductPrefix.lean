/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import TauCeti.Analysis.Complex.GrowthOrder
import RealRooted.Mathlib.Analysis.Complex.LinearProductAnalytic
import RealRooted.Mathlib.Analysis.Complex.GrowthOrder.OfBound
import TauCeti.Analysis.Normed.Ring.InfiniteProd

/-!
# Prefixes and growth of real linear canonical products

These identities keep the canonical product totalization visible. Summability
supplies actual convergence for the prefix factorization and growth estimate.
-/

public section

open Polynomial

namespace Complex

/-- Summable signed real slopes give an entire product of order at most one. -/
theorem orderLE_tprod_one_add_ofReal_mul {a : ℕ → ℝ} (ha : Summable a) :
    TauCeti.OrderLE (fun z : ℂ => ∏' j, (1 + (a j : ℂ) * z)) 1 := by
  apply TauCeti.orderLE_of_norm_le_mul_exp_rpow (B := 1) (C := ∑' j, ‖a j‖)
  intro z
  have hs : Summable (fun j => ‖(a j : ℂ) * z‖) := by
    simpa only [norm_mul, norm_real] using ha.norm.mul_right ‖z‖
  simpa only [norm_mul, norm_real, tsum_mul_right, Real.rpow_one, one_mul] using
    TauCeti.norm_tprod_one_add_le_exp_tsum hs

/-- A finite prefix factors from the actual convergent product, even at a zero. -/
theorem tprod_one_add_eq_prefix_mul_tail {a : ℕ → ℝ} (ha : Summable a) (n : ℕ) :
    (fun z : ℂ => ∏' j, (1 + (a j : ℂ) * z)) =
      fun z => ((∏ j ∈ Finset.range n, (1 + C (a j) * X : ℝ[X])).map ofRealHom).eval z *
        ∏' j : ℕ, (1 + (a (j + n) : ℂ) * z) := by
  ext z
  have ht := (hasProdLocallyUniformlyOn_one_add_ofReal_mul
    ((summable_nat_add_iff n).mpr ha)).hasProd (Set.mem_univ z)
  have h := ht.multipliable.prod_mul_tprod_nat_mul'
    (f := fun j => (1 + (a j : ℂ) * z)) (k := n)
  simpa only [Polynomial.map_prod, Polynomial.map_add, Polynomial.map_one,
    Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X, eval_prod, eval_add,
    eval_one, eval_mul, eval_C, eval_X, ofRealHom_eq_coe] using h.symm

/-- If a linear product is not a polynomial, its nonzero slopes have infinite
support. Finite and empty supports give finite polynomial products. -/
theorem infinite_support_of_tprod_ne_polynomial {a : ℕ → ℝ}
    (hpoly : ∀ p : ℂ[X],
      (fun z : ℂ => ∏' j, (1 + (a j : ℂ) * z)) ≠ fun z => p.eval z) :
    (Function.support a).Infinite := by
  classical
  intro hfin
  let s := hfin.toFinset
  let P : ℂ[X] := ∏ j ∈ s, (1 + C (a j : ℂ) * X)
  apply hpoly P
  ext z
  rw [tprod_eq_prod (s := s)]
  · simp only [P, eval_prod, eval_add, eval_one, eval_mul, eval_C, eval_X]
  · intro j hj
    have hj' : a j = 0 := by
      by_contra h
      exact hj (hfin.mem_toFinset.mpr h)
    simp only [hj', ofReal_zero, zero_mul, add_zero]

end Complex
