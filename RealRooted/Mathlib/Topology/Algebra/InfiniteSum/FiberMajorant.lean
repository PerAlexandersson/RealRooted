/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.Normed.Group.InfiniteSum

/-!
# Summability from weighted finite-fiber bounds

The hypotheses bound every finite part of each fiber. Thus neither an enumeration
of the index type nor separately supplied finiteness of the fibers is needed.
The finite comparison applies equally to a head or a tail of the family.
-/

public section

namespace Finset

/-- A weighted finite family is bounded by the corresponding bounds for its fibers. -/
theorem sum_le_sum_mul_of_fiber_le {ι κ : Type*} [DecidableEq κ]
    (s : Finset ι) (t : Finset κ) (bin : ι → κ) (w v : ι → ℝ) (B W : κ → ℝ)
    (hmap : ∀ i ∈ s, bin i ∈ t)
    (hW : ∀ n ∈ t, 0 ≤ W n)
    (hv : ∀ i ∈ s, v i ≤ w i * W (bin i))
    (hB : ∀ n ∈ t, ∑ i ∈ s with bin i = n, w i ≤ B n) :
    ∑ i ∈ s, v i ≤ ∑ n ∈ t, B n * W n := by
  classical
  rw [← sum_fiberwise_of_maps_to hmap]
  apply sum_le_sum
  intro n hn
  calc
    ∑ i ∈ s with bin i = n, v i ≤ ∑ i ∈ s with bin i = n, w i * W n := by
      apply sum_le_sum
      intro i hi
      have hi' := mem_filter.mp hi
      simpa only [hi'.2] using hv i hi'.1
    _ = (∑ i ∈ s with bin i = n, w i) * W n := by rw [sum_mul]
    _ ≤ B n * W n := mul_le_mul_of_nonneg_right (hB n hn) (hW n hn)

end Finset

/-- Finite-fiber bounds with a summable majorant imply summability of a nonnegative family. -/
theorem summable_of_finite_fiber_majorant {ι κ : Type*}
    (bin : ι → κ) (w v : ι → ℝ) (B W : κ → ℝ)
    (hv0 : ∀ i, 0 ≤ v i) (hB0 : ∀ n, 0 ≤ B n) (hW0 : ∀ n, 0 ≤ W n)
    (hv : ∀ i, v i ≤ w i * W (bin i))
    (hB : ∀ n (s : Finset ι), (∀ i ∈ s, bin i = n) → ∑ i ∈ s, w i ≤ B n)
    (hsum : Summable (fun n ↦ B n * W n)) : Summable v := by
  classical
  apply summable_of_sum_le hv0 (c := ∑' n, B n * W n)
  intro s
  calc
    ∑ i ∈ s, v i ≤ ∑ n ∈ s.image bin, B n * W n := by
      apply Finset.sum_le_sum_mul_of_fiber_le s (s.image bin) bin w v B W
      · exact fun i hi ↦ Finset.mem_image_of_mem bin hi
      · exact fun n _ ↦ hW0 n
      · exact fun i _ ↦ hv i
      · intro n _
        exact hB n _ (fun i hi ↦ (Finset.mem_filter.mp hi).2)
    _ ≤ ∑' n, B n * W n :=
      hsum.sum_le_tsum _ (fun n _ ↦ mul_nonneg (hB0 n) (hW0 n))

/-- The total mass satisfies the same finite-fiber majorant. -/
theorem tsum_le_tsum_of_finite_fiber_majorant {ι κ : Type*}
    (bin : ι → κ) (w v : ι → ℝ) (B W : κ → ℝ)
    (hv0 : ∀ i, 0 ≤ v i) (hB0 : ∀ n, 0 ≤ B n) (hW0 : ∀ n, 0 ≤ W n)
    (hv : ∀ i, v i ≤ w i * W (bin i))
    (hB : ∀ n (s : Finset ι), (∀ i ∈ s, bin i = n) → ∑ i ∈ s, w i ≤ B n)
    (hsum : Summable (fun n ↦ B n * W n)) :
    ∑' i, v i ≤ ∑' n, B n * W n := by
  classical
  apply Real.tsum_le_of_sum_le hv0
  intro s
  calc
    ∑ i ∈ s, v i ≤ ∑ n ∈ s.image bin, B n * W n := by
      apply Finset.sum_le_sum_mul_of_fiber_le s (s.image bin) bin w v B W
      · exact fun i hi ↦ Finset.mem_image_of_mem bin hi
      · exact fun n _ ↦ hW0 n
      · exact fun i _ ↦ hv i
      · intro n _
        exact hB n _ (fun i hi ↦ (Finset.mem_filter.mp hi).2)
    _ ≤ ∑' n, B n * W n :=
      hsum.sum_le_tsum _ (fun n _ ↦ mul_nonneg (hB0 n) (hW0 n))
