/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Basic.Real.Basic
import RealRooted.Mathlib.RingTheory.Polynomial.Pochhammer

import Mathlib.Algebra.Polynomial.Eval.SMul
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Polynomials vanishing on a window of consecutive integers

A real polynomial of degree below `k` which vanishes at `k` consecutive integers is zero.  Hence
the first `k` coefficients of a polynomial expanded in the binomial basis
`Polynomial.descPochhammerBasis` are determined by the values of the polynomial at `k` consecutive
integers.

## Main statements

* `Polynomial.eq_zero_of_natDegree_lt_of_eval_nat_add_eq_zero`
* `Polynomial.eq_zero_of_sum_choose_eq_zero_on_window`
-/

public section

open scoped BigOperators
open Polynomial

namespace Polynomial

/-- A polynomial of degree below `k` which vanishes at `k` consecutive
integers is zero. -/
theorem eq_zero_of_natDegree_lt_of_eval_nat_add_eq_zero
    {q : ℝ[X]} {k N₀ : ℕ} (hdeg : q.natDegree < k)
    (h : ∀ t < k, q.eval (N₀ + t : ℝ) = 0) : q = 0 := by
  apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero q
    (f := fun i : Fin k ↦ (N₀ + i : ℝ))
  · intro i j hij
    apply Fin.ext
    norm_num at hij ⊢
    exact hij
  · intro i
    exact h i i.2
  · simpa using hdeg

/-- Consecutive values determine a linear combination of the first `k`
binomial-coefficient functions. -/
theorem eq_zero_of_sum_choose_eq_zero_on_window
    (v : ℕ → ℝ) {k N₀ : ℕ}
    (h : ∀ t < k,
      ∑ j ∈ Finset.range k, ((N₀ + t).choose j : ℝ) * v j = 0) :
    ∀ j < k, v j = 0 := by
  by_cases hk0 : k = 0
  · subst k
    simp
  let q : ℝ[X] := ∑ j ∈ Finset.range k,
    (v j / (j.factorial : ℝ)) • descPochhammerBasis ℝ j
  have hdeg : q.natDegree < k := by
    refine lt_of_le_of_lt
      (natDegree_sum_le_of_forall_le _ _ fun j hj ↦ ?_) (Nat.pred_lt hk0)
    refine (natDegree_smul_le _ _).trans ?_
    rw [descPochhammerBasis_apply, descPochhammer_natDegree]
    exact Nat.le_pred_of_lt (Finset.mem_range.mp hj)
  have hq : q = 0 := by
    refine eq_zero_of_natDegree_lt_of_eval_nat_add_eq_zero
      (N₀ := N₀) hdeg ?_
    intro t ht
    rw [show q.eval (N₀ + t : ℝ) =
        ∑ j ∈ Finset.range k, ((N₀ + t).choose j : ℝ) * v j by
      simp only [q, eval_finsetSum, eval_smul, descPochhammerBasis_apply]
      apply Finset.sum_congr rfl
      intro j _
      change (v j / (j.factorial : ℝ)) *
        (descPochhammer ℝ j).eval (N₀ + t : ℝ) = _
      rw [← Nat.cast_add]
      rw [descPochhammer_eval_eq_descFactorial]
      rw [Nat.descFactorial_eq_factorial_mul_choose]
      field_simp [Nat.factorial_ne_zero]
      rw [Nat.cast_mul]
      ring]
    exact h t ht
  intro j hj
  have hre := congrArg (fun p : ℝ[X] ↦ (descPochhammerBasis ℝ).repr p j) hq
  simp only [q, map_sum, Finsupp.coe_finsetSum, Finset.sum_apply,
    map_smul, Module.Basis.repr_self, Finsupp.smul_single,
    Finsupp.single_apply] at hre
  simpa [Finset.mem_range.mpr hj, Nat.factorial_ne_zero] using hre

end Polynomial
