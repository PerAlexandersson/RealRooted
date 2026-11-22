/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Algebra.Module.BigOperators

/-!
# Regular finite weighted means

Nonnegative finite weighted means preserve sequence limits when each fixed
weight tends to zero and the total mass tends to one. Summation by parts gives
a regularity theorem for decreasing weights on a convergent series. The
series hypothesis is convergence of ordinary partial sums, so conditional
convergence is allowed.
-/

public section

open Finset Filter Topology

private theorem tendsto_weighted_mean_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {w : ℕ → ℕ → ℝ} {s : ℕ → E} {r : ℕ → ℕ}
    (hr : Tendsto r atTop atTop)
    (hw : ∀ n k, 0 ≤ w n k) (hb : ∀ n, ∑ k ∈ range (r n), w n k ≤ 1)
    (hc : ∀ k, Tendsto (fun n => w n k) atTop (𝓝 0))
    (hs : Tendsto s atTop (𝓝 0)) :
    Tendsto (fun n => ∑ k ∈ range (r n), w n k • s k) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop] at hs ⊢
  intro ε hε
  obtain ⟨N, hN⟩ := hs (ε / 2) (by positivity)
  have hfinite : Tendsto (fun n => ∑ k ∈ range N, w n k * ‖s k‖) atTop (𝓝 0) := by
    simpa using tendsto_finsetSum (range N) fun k _ => (hc k).mul_const ‖s k‖
  obtain ⟨M, hM⟩ := Metric.tendsto_atTop.mp hfinite (ε / 2) (by positivity)
  obtain ⟨K, hK⟩ := eventually_atTop.mp (hr.eventually (eventually_ge_atTop N))
  refine ⟨max K M, fun n hn => ?_⟩
  have hNn : N ≤ r n := hK n ((le_max_left K M).trans hn)
  have hMn : M ≤ n := (le_max_right K M).trans hn
  have hprefix : ∑ k ∈ range N, w n k * ‖s k‖ < ε / 2 := by
    exact lt_of_le_of_lt (le_abs_self _) (by simpa [Real.dist_eq] using hM n hMn)
  have htail : ∑ k ∈ Ico N (r n), w n k * ‖s k‖ ≤ ε / 2 := by
    calc
      _ ≤ ∑ k ∈ Ico N (r n), w n k * (ε / 2) := by
        apply sum_le_sum
        intro k hk
        apply mul_le_mul_of_nonneg_left _ (hw n k)
        have hkbound : ‖s k‖ < ε / 2 := by
          simpa only [dist_zero_right] using hN k (mem_Ico.mp hk).1
        exact hkbound.le
      _ = (∑ k ∈ Ico N (r n), w n k) * (ε / 2) := (sum_mul _ _ _).symm
      _ ≤ 1 * (ε / 2) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        refine le_trans (sum_le_sum_of_subset_of_nonneg ?_ ?_) (hb n)
        · exact fun k hk => mem_range.mpr (mem_Ico.mp hk).2
        · exact fun k _ _ => hw n k
      _ = ε / 2 := one_mul _
  rw [dist_zero_right]
  calc
    _ ≤ ∑ k ∈ range (r n), ‖w n k • s k‖ := norm_sum_le _ _
    _ = ∑ k ∈ range (r n), w n k * ‖s k‖ := by
      apply sum_congr rfl
      intro k _
      rw [norm_smul, Real.norm_of_nonneg (hw n k)]
    _ = (∑ k ∈ range N, w n k * ‖s k‖) +
        ∑ k ∈ Ico N (r n), w n k * ‖s k‖ := (sum_range_add_sum_Ico _ hNn).symm
    _ < ε := by linarith

/-- Finite nonnegative weighted means preserve limits when the rows have mass
at most one, their masses tend to one, and each fixed weight tends to zero. -/
theorem tendsto_weighted_mean_of_tendsto {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {w : ℕ → ℕ → ℝ} {s : ℕ → E} {r : ℕ → ℕ} {a : E}
    (hr : Tendsto r atTop atTop)
    (hw : ∀ n k, 0 ≤ w n k) (hb : ∀ n, ∑ k ∈ range (r n), w n k ≤ 1)
    (hc : ∀ k, Tendsto (fun n => w n k) atTop (𝓝 0))
    (hm : Tendsto (fun n => ∑ k ∈ range (r n), w n k) atTop (𝓝 1))
    (hs : Tendsto s atTop (𝓝 a)) :
    Tendsto (fun n => ∑ k ∈ range (r n), w n k • s k) atTop (𝓝 a) := by
  have hz := tendsto_weighted_mean_zero hr hw hb hc
    (show Tendsto (fun n => s n - a) atTop (𝓝 0) by simpa using hs.sub_const a)
  have ht := hz.add (hm.smul_const a)
  simpa only [smul_sub, sum_sub_distrib, ← sum_smul, sub_add_cancel, one_smul,
    zero_add] using ht

/-- Finite decreasing weights tending pointwise to one preserve the sum of an
ordinary convergent series. The convergence may be conditional. -/
theorem tendsto_weighted_series_of_antitone {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {κ : ℕ → ℕ → ℝ} {u : ℕ → E} {a : E}
    (hκ : ∀ n, Antitone (κ n)) (hb : ∀ n, κ n 0 ≤ 1)
    (hz : ∀ n, κ n (n + 1) = 0)
    (hc : ∀ k, Tendsto (fun n => κ n k) atTop (𝓝 1))
    (hu : Tendsto (fun n => ∑ k ∈ range n, u k) atTop (𝓝 a)) :
    Tendsto (fun n => ∑ k ∈ range (n + 1), κ n k • u k) atTop (𝓝 a) := by
  let w : ℕ → ℕ → ℝ := fun n k => κ n k - κ n (k + 1)
  have hm (n : ℕ) : ∑ k ∈ range (n + 1), w n k = κ n 0 := by
    dsimp [w]
    rw [sum_range_sub']
    simp [hz]
  have ht := tendsto_weighted_mean_of_tendsto (r := fun n => n + 1)
    (w := w) (s := fun k => ∑ i ∈ range (k + 1), u i)
    (tendsto_add_atTop_nat 1)
    (fun n k => sub_nonneg.mpr (hκ n (Nat.le_succ k)))
    (fun n => by rw [hm]; exact hb n)
    (fun k => by simpa [w] using (hc k).sub (hc (k + 1)))
    (by simpa only [hm] using hc 0)
    (hu.comp (tendsto_add_atTop_nat 1))
  convert ht using 1
  ext n
  have hp := sum_range_by_parts (κ n) u (n + 2)
  rw [show n + 2 - 1 = n + 1 by lia, sum_range_succ] at hp
  simp only [hz n, zero_smul, add_zero, zero_sub] at hp
  rw [hp, ← sum_neg_distrib]
  apply sum_congr rfl
  intro k _
  rw [← neg_smul, neg_sub]
