/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import RealRooted.CombinatorialExamples.ZigzagEulerian.Definitions
import Mathlib.RingTheory.Polynomial.SmallDegreeVieta
public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# The initial zig-zag Eulerian rows

This records the splitness and simple negative roots of the first four actual
permutation sums, as in the small cases of `thm:zigzagEulerian`.
-/

public section

open Polynomial

namespace RealRooted.ZigzagEulerian

private theorem zigzagEulerianPolynomial_three_root_properties :
    (zigzagEulerianPolynomial 3).natDegree = 1 ∧
      (zigzagEulerianPolynomial 3).Splits ∧
      (zigzagEulerianPolynomial 3).roots.Nodup ∧
      ∀ r ∈ (zigzagEulerianPolynomial 3).roots, r < 0 := by
  have hrow : zigzagEulerianPolynomial 3 = X + 1 := by
    rw [zigzagEulerianPolynomial_three]
    ring
  have hroots : (zigzagEulerianPolynomial 3).roots = {-1} := by
    rw [hrow]
    simpa using (Polynomial.roots_X_add_C (1 : ℝ))
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hrow]
    simp
  · rw [hrow]
    simpa [add_comm] using (Polynomial.Splits.X_add_C (1 : ℝ))
  · rw [hroots]
    simp
  · intro r hr
    rw [hroots] at hr
    simp only [Multiset.mem_singleton] at hr
    linarith

private theorem zigzagEulerianPolynomial_four_root_properties :
    (zigzagEulerianPolynomial 4).natDegree = 2 ∧
      (zigzagEulerianPolynomial 4).Splits ∧
      (zigzagEulerianPolynomial 4).roots.Nodup ∧
      ∀ r ∈ (zigzagEulerianPolynomial 4).roots, r < 0 := by
  have hrow : zigzagEulerianPolynomial 4 =
      C (1 : ℝ) * X ^ 2 + C (3 : ℝ) * X + C (1 : ℝ) := by
    rw [zigzagEulerianPolynomial_four]
    norm_num only [map_one, map_ofNat]
    ring
  have hroots : (zigzagEulerianPolynomial 4).roots =
      {(-3 - Real.sqrt 5) / 2, (-3 + Real.sqrt 5) / 2} := by
    rw [hrow]
    apply (Polynomial.roots_quadratic_eq_pair_iff_of_ne_zero (by norm_num : (1 : ℝ) ≠ 0)).2
    constructor
    · ring
    · nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)]
  have hsqrt : (Real.sqrt 5) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hsqrt_nonneg : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  have hsqrt_lt : Real.sqrt 5 < 3 := by nlinarith
  have hneq : (-3 - Real.sqrt 5) / 2 ≠ (-3 + Real.sqrt 5) / 2 := by
    intro h
    have h' := congrArg (fun x : ℝ => 2 * x) h
    have h'' : -3 - Real.sqrt 5 = -3 + Real.sqrt 5 := by
      field_simp at h'
      linarith
    linarith [Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 5)]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hrow]
    exact Polynomial.natDegree_quadratic (by norm_num : (1 : ℝ) ≠ 0)
  · apply Polynomial.splits_iff_card_roots.mpr
    rw [hroots, hrow, Polynomial.natDegree_quadratic (by norm_num : (1 : ℝ) ≠ 0)]
    simp
  · rw [hroots]
    simp [hneq]
  · intro r hr
    rw [hroots] at hr
    have hr' : r = (-3 - Real.sqrt 5) / 2 ∨ r = (-3 + Real.sqrt 5) / 2 := by
      simpa using hr
    rcases hr' with hleft | hright
    · rw [hleft]
      exact div_neg_of_neg_of_pos (by linarith) (by norm_num)
    · rw [hright]
      exact div_neg_of_neg_of_pos (by linarith) (by norm_num)

/-- The first four actual zig-zag Eulerian rows have the expected degree,
split over `ℝ`, and have distinct strictly negative roots. The root condition
is vacuous for the constant rows `n = 1, 2`.
-/
theorem zigzagEulerianPolynomial_small_roots {n : ℕ} (hn : 1 ≤ n) (hn4 : n ≤ 4) :
    (zigzagEulerianPolynomial n).natDegree = n - 2 ∧
      (zigzagEulerianPolynomial n).Splits ∧
      (zigzagEulerianPolynomial n).roots.Nodup ∧
      ∀ r ∈ (zigzagEulerianPolynomial n).roots, r < 0 := by
  interval_cases n
  · simp [zigzagEulerianPolynomial_one]
  · simp [zigzagEulerianPolynomial_two]
  · simpa using zigzagEulerianPolynomial_three_root_properties
  · simpa using zigzagEulerianPolynomial_four_root_properties

end RealRooted.ZigzagEulerian
