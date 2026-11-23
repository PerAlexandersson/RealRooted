/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.Basic.Real.Basic

/-!
# Degree growth of products of nonconstant linear factors

Zero slopes contribute constant factors. Infinite nonzero-slope support is
therefore enough for the prefix degrees to tend to infinity.
-/

public section

open Filter

namespace Polynomial

/-- Every real linear factor `1 + aX` splits, including the constant case. -/
theorem splits_one_add_C_mul_X (a : ℝ) : (1 + C a * X : ℝ[X]).Splits :=
  Splits.of_natDegree_le_one ((natDegree_add_le _ _).trans
    (max_le (by simp) ((natDegree_C_mul_le _ _).trans (by simp))))

/-- Every factor `1 + aX` is nonzero, including `a = 0`. -/
theorem one_add_C_mul_X_ne_zero (a : ℝ) : (1 + C a * X : ℝ[X]) ≠ 0 := by
  intro h
  have h0 := congrArg (fun p : ℝ[X] => p.eval 0) h
  simp at h0

/-- Any subset of nonzero slopes supplies a lower bound on the product degree. -/
theorem card_le_natDegree_prod_one_add {s t : Finset ℕ} {a : ℕ → ℝ}
    (ht : t ⊆ s) (ha : ∀ j ∈ t, a j ≠ 0) :
    t.card ≤ (∏ j ∈ s, (1 + C (a j) * X : ℝ[X])).natDegree := by
  rw [natDegree_prod s (fun j => (1 + C (a j) * X : ℝ[X]))
    (fun j _ => one_add_C_mul_X_ne_zero (a j))]
  calc
    _ = ∑ j ∈ t, (1 + C (a j) * X : ℝ[X]).natDegree := by
      symm
      calc
        _ = ∑ _j ∈ t, 1 := Finset.sum_congr rfl fun j hj => by
          simpa only [add_comm, C_1] using natDegree_linear (b := (1 : ℝ)) (ha j hj)
        _ = _ := by simp
    _ ≤ _ := Finset.sum_le_sum_of_subset ht

/-- Infinite nonzero-slope support forces the finite product degrees to diverge. -/
theorem tendsto_natDegree_prod_one_add {a : ℕ → ℝ}
    (ha : (Function.support a).Infinite) :
    Tendsto (fun n => (∏ j ∈ Finset.range n,
      (1 + C (a j) * X : ℝ[X])).natDegree) atTop atTop := by
  refine tendsto_atTop.mpr fun N => ?_
  obtain ⟨s, hs, hcard⟩ := ha.exists_subset_card_eq N
  filter_upwards [eventually_ge_atTop (s.sup id + 1)] with n hn
  rw [← hcard]
  apply card_le_natDegree_prod_one_add
  · intro j hj
    apply Finset.mem_range.mpr
    exact (Nat.lt_succ_of_le (Finset.le_sup (f := id) hj)).trans_le hn
  · intro j hj
    exact hs hj

end Polynomial
