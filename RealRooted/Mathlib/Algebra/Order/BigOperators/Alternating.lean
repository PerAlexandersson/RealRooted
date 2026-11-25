/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
import Mathlib.Data.Rat.Cast.Order
import RealRooted.Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs

/-!
# Finite alternating-sum bounds

This Mathlib-shaped shim gives elementary finite truncation bounds for an
alternating sum of nonnegative decreasing terms.
-/

public section

namespace Finset

/-- A finite alternating sum of nonnegative decreasing terms is nonnegative. -/
theorem alternating_sum_range_nonneg {R : Type*} [CommRing R] [LinearOrder R]
    [IsStrictOrderedRing R] :
    ∀ (N : ℕ) (T : ℕ → R), (∀ i, T (i + 1) ≤ T i) →
      (∀ i, 0 ≤ T i) → 0 ≤ ∑ i ∈ range N, (-1 : R) ^ i * T i := by
  intro N T hanti hnn
  exact sum_range_neg_one_pow_mul_nonneg_of_antitone N (antitone_nat_of_succ_le hanti) hnn

/-- A finite alternating sum of nonnegative decreasing terms is at most its
first term. -/
theorem alternating_sum_range_le_head {R : Type*} [CommRing R] [LinearOrder R]
    [IsStrictOrderedRing R]
    (N : ℕ) (T : ℕ → R) (hanti : ∀ i, T (i + 1) ≤ T i)
    (hnn : ∀ i, 0 ≤ T i) (hN : 1 ≤ N) :
    ∑ i ∈ range N, (-1 : R) ^ i * T i ≤ T 0 := by
  exact sum_range_neg_one_pow_mul_le_of_antitone (by lia)
    (antitone_nat_of_succ_le hanti) hnn

/-- A finite alternating sum of nonnegative decreasing terms is at least its
first two terms. -/
theorem head_sub_le_alternating_sum_range {R : Type*} [CommRing R] [LinearOrder R]
    [IsStrictOrderedRing R]
    (N : ℕ) (T : ℕ → R) (hanti : ∀ i, T (i + 1) ≤ T i)
    (hnn : ∀ i, 0 ≤ T i) (hN : 2 ≤ N) :
    T 0 - T 1 ≤ ∑ i ∈ range N, (-1 : R) ^ i * T i := by
  exact sub_le_sum_range_neg_one_pow_mul_of_antitone hN (antitone_nat_of_succ_le hanti) hnn

end Finset
