/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import RealRooted.Mathlib.Algebra.MvPolynomial.PDeriv

/-!
# Partial derivatives of finite products

This file gives the finite-product Leibniz rule for multivariate
polynomials.
-/

@[expose] public section

open scoped BigOperators

namespace MvPolynomial

/-- The partial derivative of a finite product is the sum obtained by
marking one factor at a time. -/
theorem pderiv_finsetProd {σ R ι : Type*} [CommSemiring R]
    [DecidableEq ι] (u : σ) (s : Finset ι)
    (f : ι → MvPolynomial σ R) :
    pderiv u (∏ i ∈ s, f i) =
      ∑ i ∈ s, (∏ j ∈ s.erase i, f j) * pderiv u (f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Derivation.leibniz, ih,
        Finset.sum_insert ha, Finset.erase_insert ha, smul_eq_mul,
        smul_eq_mul, Finset.mul_sum, add_comm]
      congr 1
      refine Finset.sum_congr rfl fun i hi => ?_
      have hai : a ≠ i := fun h => ha (h ▸ hi)
      rw [Finset.erase_insert_of_ne hai,
        Finset.prod_insert (by simp [ha]), mul_assoc]

end MvPolynomial
