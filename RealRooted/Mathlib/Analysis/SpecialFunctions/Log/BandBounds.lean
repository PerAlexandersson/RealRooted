/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import RealRooted.Mathlib.Topology.Algebra.InfiniteSum.FiberMajorant
import RealRooted.Mathlib.Analysis.SpecialFunctions.Log.Weights
import Mathlib.Analysis.PSeries
import Mathlib.Tactic.IntervalCases

/-!
# Weighted finite head and tail estimates from logarithmic band counts

The indexing function records a unit-height band. These lemmas retain arbitrary
nonnegative masses, so analytic zero multiplicities need no enumeration.
For tails, band `k` denotes the actual height band `k + N + 1`.
-/

public section

namespace Real

/-- The positive logarithmic reciprocal-square majorant is summable over the naturals. -/
theorem summable_one_add_log_natCast_div_sq :
    Summable (fun n : ℕ ↦ (1 + log n) / (n : ℝ) ^ 2) := by
  have hlog : Summable (fun n : ℕ ↦ log n / (n : ℝ) ^ 2) := by
    apply summable_log_natCast_div_sub_one_sq.of_nonneg_of_le
      (fun n ↦ div_nonneg (log_natCast_nonneg n) (sq_nonneg _))
    intro n
    rcases Nat.lt_or_ge n 2 with hn | hn
    · interval_cases n <;> simp
    have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
    exact div_le_div_of_nonneg_left (log_natCast_nonneg n)
      (by nlinarith : 0 < ((n : ℝ) - 1) ^ 2) (by nlinarith)
  exact ((summable_one_div_nat_pow.mpr (by norm_num : 1 < 2)).add hlog).congr
    (fun n ↦ by ring)

end Real

namespace Finset

/-- Summing logarithmic band counts against a reciprocal-height weight gives a logarithmic-square
head bound. The pointwise inequality can use a complex norm in its denominator. -/
theorem sum_le_log_mul_one_add_log_of_fiber_bound {ι : Type*}
    (s : Finset ι) (bin : ι → ℕ) (w v : ι → ℝ) {C : ℝ} (hC : 0 ≤ C) (N : ℕ)
    (hbin : ∀ i ∈ s, bin i ∈ Icc 1 N)
    (hv : ∀ i ∈ s, v i ≤ w i * (2 / (bin i : ℝ)))
    (hB : ∀ n ∈ Icc 1 N, ∑ i ∈ s with bin i = n, w i ≤ C * Real.log n) :
    ∑ i ∈ s, v i ≤ 2 * C * (Real.log N * (1 + Real.log N)) := by
  classical
  calc
    ∑ i ∈ s, v i ≤ ∑ n ∈ Icc 1 N, (C * Real.log n) * (2 / (n : ℝ)) :=
      sum_le_sum_mul_of_fiber_le s (Icc 1 N) bin w v _ _ hbin
        (fun n _ ↦ by positivity) hv hB
    _ = 2 * C * (∑ n ∈ Icc 1 N, Real.log n / (n : ℝ)) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro n _
      ring
    _ ≤ 2 * C * (Real.log N * (1 + Real.log N)) :=
      mul_le_mul_of_nonneg_left (Real.sum_Icc_log_natCast_div_le N) (by positivity)

/-- Summing logarithmic band counts against a reciprocal-square weight gives a `log N / N`
tail bound. The index `bin i` is the offset from the first omitted band `N + 1`. -/
theorem sum_le_log_add_div_of_fiber_bound {ι : Type*}
    (s : Finset ι) (bin : ι → ℕ) (w v : ι → ℝ) {C : ℝ} (hC : 0 ≤ C)
    {N : ℕ} (hN : 1 ≤ N)
    (hv : ∀ i ∈ s, v i ≤ w i * (4 / (bin i + N + 1 : ℝ) ^ 2))
    (hB : ∀ n ∈ s.image bin, ∑ i ∈ s with bin i = n, w i ≤ C * Real.log (n + N + 1 : ℕ)) :
    ∑ i ∈ s, v i ≤ 4 * C * ((Real.log N + 2) / N) := by
  classical
  have hsum : Summable (fun n : ℕ ↦
      4 * C * ((1 + Real.log (n + N + 1 : ℕ)) / (n + N + 1 : ℝ) ^ 2)) := by
    have hs := Real.summable_one_add_log_natCast_div_sq.comp_injective
      (i := fun n : ℕ ↦ n + (N + 1)) (fun _ _ h ↦ Nat.add_right_cancel h)
    simpa only [Nat.cast_add, Nat.cast_one, Nat.add_assoc, Function.comp_def, add_assoc] using
      hs.mul_left (4 * C)
  calc
    ∑ i ∈ s, v i ≤ ∑ n ∈ s.image bin,
        (C * Real.log (n + N + 1 : ℕ)) * (4 / (n + N + 1 : ℝ) ^ 2) :=
      sum_le_sum_mul_of_fiber_le s (s.image bin) bin w v _ _
        (fun i hi ↦ mem_image_of_mem bin hi) (fun n _ ↦ by positivity) hv hB
    _ ≤ ∑ n ∈ s.image bin,
        4 * C * ((1 + Real.log (n + N + 1 : ℕ)) / (n + N + 1 : ℝ) ^ 2) := by
      apply sum_le_sum
      intro n _
      have hden : 0 ≤ (n + N + 1 : ℝ) ^ 2 := sq_nonneg _
      calc
        (C * Real.log (n + N + 1 : ℕ)) * (4 / (n + N + 1 : ℝ) ^ 2) =
            4 * C * (Real.log (n + N + 1 : ℕ) / (n + N + 1 : ℝ) ^ 2) := by ring
        _ ≤ 4 * C * ((1 + Real.log (n + N + 1 : ℕ)) / (n + N + 1 : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (by linarith) hden)
            (by positivity)
    _ ≤ ∑' n : ℕ,
        4 * C * ((1 + Real.log (n + N + 1 : ℕ)) / (n + N + 1 : ℝ) ^ 2) :=
      hsum.sum_le_tsum _ (fun n _ ↦ by positivity)
    _ = 4 * C * (∑' n : ℕ,
        (1 + Real.log (n + N + 1 : ℕ)) / (n + N + 1 : ℝ) ^ 2) := tsum_mul_left
    _ ≤ 4 * C * ((Real.log N + 2) / N) :=
      mul_le_mul_of_nonneg_left (Real.tsum_one_add_log_div_sq_add_le hN) (by positivity)

end Finset
