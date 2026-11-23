/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic.TypeStar

/-!
# Fixed finite coefficient sums for powers of a formal series

If a formal series starts with `1 + X^p * ψ`, each fixed coefficient of its
`m`th power is a sum with a bound independent of `m`. This finite identity
is useful for rescaled differential-operator limits.
-/

public section

open Finset

namespace PowerSeries

variable {R : Type*} [CommSemiring R]

/-- Extending the finite binomial sum adds only zero binomial coefficients. -/
private theorem sum_choose_truncated (m q : ℕ) (f : ℕ → R) :
    ∑ k ∈ range (m + 1), (if k ≤ q then (m.choose k : R) * f k else 0) =
      ∑ k ∈ range (q + 1), (m.choose k : R) * f k := by
  by_cases hmq : m ≤ q
  · calc
      _ = ∑ k ∈ range (m + 1), (m.choose k : R) * f k := by
        apply sum_congr rfl
        intro k hk
        rw [ite_eq_left ((Nat.lt_succ_iff.mp (mem_range.mp hk)).trans hmq)]
      _ = _ := by
        apply sum_subset (range_subset_range.mpr (Nat.add_le_add_right hmq 1))
        intro k _ hk
        have hmk : m < k := by
          simp only [mem_range] at hk
          lia
        simp [Nat.choose_eq_zero_of_lt hmk]
  · have hqm : q ≤ m := (lt_of_not_ge hmq).le
    symm
    calc
      _ = ∑ k ∈ range (q + 1),
          (if k ≤ q then (m.choose k : R) * f k else 0) := by
        apply sum_congr rfl
        intro k hk
        rw [ite_eq_left (Nat.lt_succ_iff.mp (mem_range.mp hk))]
      _ = _ := by
        apply sum_subset (range_subset_range.mpr (Nat.add_le_add_right hqm 1))
        intro k _ hk
        have hkq : ¬ k ≤ q := by
          simp only [mem_range] at hk
          lia
        exact ite_eq_right hkq

/-- Every fixed coefficient of `(1 + X^p * ψ)^m` is a binomial sum whose
length depends only on that coefficient, including `m = 0`. -/
theorem coeff_one_add_X_pow_mul_pow (ψ : PowerSeries R) {p : ℕ} (hp : 0 < p)
    (m j : ℕ) :
    coeff j ((1 + X ^ p * ψ) ^ m) =
      ∑ k ∈ range (j / p + 1),
        (m.choose k : R) * coeff (j - p * k) (ψ ^ k) := by
  calc
    _ = ∑ k ∈ range (m + 1),
        (if k ≤ j / p then (m.choose k : R) * coeff (j - p * k) (ψ ^ k) else 0) := by
      rw [add_comm (1 : PowerSeries R), add_pow, map_sum]
      apply sum_congr rfl
      intro k _
      have hiff : p * k ≤ j ↔ k ≤ j / p := by
        simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le hp).symm
      simp only [one_pow, mul_one, mul_pow, ← pow_mul, coeff_mul_natCast,
        coeff_X_pow_mul', hiff]
      split_ifs <;> simp [mul_comm]
    _ = _ := sum_choose_truncated m (j / p) _

end PowerSeries
