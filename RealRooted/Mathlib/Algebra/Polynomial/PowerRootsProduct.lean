/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Homogeneous products over roots of `X^n + 1`

Roots are counted with multiplicity. The product identity includes a zero
scaling parameter, so it needs no division by the evaluation argument.
-/

public section

open Polynomial

namespace Polynomial

/-- Homogenizing the monic factorization of `X^n + 1` gives `u^n + t^n`.
This holds over any algebraically closed field, including multiple roots. -/
theorem prod_roots_X_pow_add_one_sub_mul {K : Type*} [Field K] [IsAlgClosed K]
    {n : ℕ} (hn : n ≠ 0) (u t : K) :
    (((X ^ n + 1 : K[X]).roots).map fun r ↦ u - r * t).prod = u ^ n + t ^ n := by
  let p : K[X] := X ^ n + 1
  have hm : p.Monic := by simpa only [p, C_1] using monic_X_pow_add_C (1 : K) hn
  have hc : p.roots.card = n := by
    rw [← (IsAlgClosed.splits p).natDegree_eq_card_roots]
    simpa only [p, C_1] using (natDegree_X_pow_add_C (n := n) (r := (1 : K)))
  have heval (w : K) : (p.roots.map fun r ↦ w - r).prod = w ^ n + 1 := by
    rw [← (IsAlgClosed.splits p).eval_eq_prod_roots_of_monic hm]
    simp only [p, eval_add, eval_pow, eval_X, eval_one]
  change (p.roots.map fun r ↦ u - r * t).prod = u ^ n + t ^ n
  by_cases ht : t = 0
  · simp only [ht, mul_zero, sub_zero, Multiset.map_const', Multiset.prod_replicate,
      hc, zero_pow hn, add_zero]
  · calc
      _ = (p.roots.map fun r ↦ t * (u / t - r)).prod := by
        congr 1
        apply Multiset.map_congr rfl
        intro r _
        field_simp [ht]
      _ = t ^ n * ((u / t) ^ n + 1) := by
        rw [Multiset.prod_map_mul, Multiset.map_const', Multiset.prod_replicate, hc, heval]
      _ = u ^ n + t ^ n := by
        rw [div_pow]
        field_simp [ht]

end Polynomial
