/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.Algebra.MvPolynomial.Degrees

/-!
# Additional total-degree bounds

This file contains Mathlib-shaped compatibility lemmas for multivariate
polynomial degrees.
-/

@[expose] public section

open scoped BigOperators

namespace MvPolynomial

/-- Total degree is at most the sum of the coordinatewise degrees. -/
theorem totalDegree_le_sum_degreeOf {σ R : Type*} [Fintype σ] [CommSemiring R]
    (p : MvPolynomial σ R) :
    p.totalDegree ≤ ∑ i, p.degreeOf i := by
  classical
  rw [totalDegree]
  apply Finset.sup_le
  intro d hd
  calc
    d.sum (fun _ e => e) = ∑ i, d i := by
      rw [Finsupp.sum_fintype]
      intro
      rfl
    _ ≤ ∑ i, p.degreeOf i :=
      Finset.sum_le_sum fun i _ => le_degreeOf_of_mem_support i hd

/-- A variable outside the range of `f` does not occur in `rename f P`. -/
theorem degreeOf_rename_eq_zero_of_notMem_range {σ τ R : Type*} [CommSemiring R]
    (f : σ → τ) (P : MvPolynomial σ R) {j : τ} (hj : j ∉ Set.range f) :
    (rename f P).degreeOf j = 0 := by
  apply Nat.eq_zero_of_le_zero
  rw [degreeOf_le_iff]
  intro d hd
  obtain ⟨u, hu, -⟩ := coeff_rename_ne_zero f P d (mem_support_iff.mp hd)
  rw [← hu, Finsupp.mapDomain_of_notMem_range u j hj]

end MvPolynomial
