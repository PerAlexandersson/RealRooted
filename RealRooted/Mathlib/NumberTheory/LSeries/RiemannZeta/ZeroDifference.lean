/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import Mathlib.Analysis.Analytic.Order
public import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.Nonvanishing
import RealRooted.Mathlib.NumberTheory.LSeries.RiemannZeta.ZeroSumBounds
import RealRooted.Mathlib.NumberTheory.LSeries.RiemannZeta.RiemannHypothesis
import RealRooted.Mathlib.Analysis.MellinInversion.FiniteDifference
import Mathlib.Analysis.Normed.Group.InfiniteSum

/-!
# Finite differences of the multiplicity-weighted zeta zero series

The reciprocal-norm bound controls the head, and the quadratic-denominator
bound controls the tail. The cutoff is an arbitrary integer at least four.
The estimates apply to forward and backward differences on the same
multiplicative neighborhood, with no simplicity assumption on the zeros.
-/

public section

open Complex Set

namespace RiemannHypothesis

private theorem sum_order_mul_norm_le {K A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (N : ℕ) (F : ℂ → ℂ)
    (hhead : ∀ s : Finset ℂ, (∀ ρ ∈ s, riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ |ρ.im| ≤ N) →
      ∑ ρ ∈ s, (analyticOrderNatAt riemannZeta ρ : ℝ) / ‖ρ‖ ≤ K * (1 + Real.log N) ^ 2)
    (htail : ∀ s : Finset ℂ, (∀ ρ ∈ s, riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ (N : ℝ) < |ρ.im|) →
      ∑ ρ ∈ s, (analyticOrderNatAt riemannZeta ρ : ℝ) / ‖ρ * (ρ + 1)‖ ≤
        K * ((1 + Real.log N) / N))
    (s : Finset ℂ) (hs : ∀ ρ ∈ s, riemannZeta ρ = 0 ∧ 0 < ρ.re)
    (hF : ∀ ρ ∈ s, ‖F ρ‖ ≤ A / ‖ρ‖ ∧ ‖F ρ‖ ≤ B / ‖ρ * (ρ + 1)‖) :
    ∑ ρ ∈ s, ‖(analyticOrderNatAt riemannZeta ρ : ℂ) * F ρ‖ ≤
      K * (A * (1 + Real.log N) ^ 2 + B * ((1 + Real.log N) / N)) := by
  classical
  let lo := s.filter (fun ρ ↦ |ρ.im| ≤ (N : ℝ))
  let hi := s.filter (fun ρ ↦ ¬ |ρ.im| ≤ (N : ℝ))
  have hlo : (∑ ρ ∈ lo, ‖(analyticOrderNatAt riemannZeta ρ : ℂ) * F ρ‖) ≤
      A * (K * (1 + Real.log N) ^ 2) := by
    calc
      _ ≤ ∑ ρ ∈ lo, A * ((analyticOrderNatAt riemannZeta ρ : ℝ) / ‖ρ‖) := by
        apply Finset.sum_le_sum
        intro ρ hρ
        have hρs := (Finset.mem_filter.mp hρ).1
        rw [norm_mul, Complex.norm_natCast]
        calc
          _ ≤ (analyticOrderNatAt riemannZeta ρ : ℝ) * (A / ‖ρ‖) :=
            mul_le_mul_of_nonneg_left (hF ρ hρs).1 (Nat.cast_nonneg _)
          _ = _ := by ring
      _ = A * ∑ ρ ∈ lo, (analyticOrderNatAt riemannZeta ρ : ℝ) / ‖ρ‖ := by rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left (hhead lo (by
        intro ρ hρ
        obtain ⟨hρs, hheight⟩ := Finset.mem_filter.mp hρ
        exact ⟨(hs ρ hρs).1, (hs ρ hρs).2, hheight⟩)) hA
  have hhi : (∑ ρ ∈ hi, ‖(analyticOrderNatAt riemannZeta ρ : ℂ) * F ρ‖) ≤
      B * (K * ((1 + Real.log N) / N)) := by
    calc
      _ ≤ ∑ ρ ∈ hi, B * ((analyticOrderNatAt riemannZeta ρ : ℝ) / ‖ρ * (ρ + 1)‖) := by
        apply Finset.sum_le_sum
        intro ρ hρ
        have hρs := (Finset.mem_filter.mp hρ).1
        rw [norm_mul, Complex.norm_natCast]
        calc
          _ ≤ (analyticOrderNatAt riemannZeta ρ : ℝ) * (B / ‖ρ * (ρ + 1)‖) :=
            mul_le_mul_of_nonneg_left (hF ρ hρs).2 (Nat.cast_nonneg _)
          _ = _ := by ring
      _ = B * ∑ ρ ∈ hi, (analyticOrderNatAt riemannZeta ρ : ℝ) / ‖ρ * (ρ + 1)‖ := by
        rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left (htail hi (by
        intro ρ hρ
        obtain ⟨hρs, hheight⟩ := Finset.mem_filter.mp hρ
        exact ⟨(hs ρ hρs).1, (hs ρ hρs).2, lt_of_not_ge hheight⟩)) hB
  rw [← Finset.sum_filter_add_sum_filter_not s (fun ρ ↦ |ρ.im| ≤ N)]
  change (∑ ρ ∈ lo, _) + (∑ ρ ∈ hi, _) ≤ _
  calc
    _ ≤ A * (K * (1 + Real.log N) ^ 2) + B * (K * ((1 + Real.log N) / N)) :=
      add_le_add hlo hhi
    _ = _ := by ring

/-- Under RH, all finite differences on a multiplicative neighborhood have a summable
multiplicity-weighted zero series, with a quantitative head/tail estimate. -/
theorem exists_tsum_norm_riemannZeta_difference_le (hRH : RiemannHypothesis) :
    ∃ K : ℝ, 0 < K ∧ ∀ N : ℕ, 4 ≤ N → ∀ x h y z : ℝ,
      0 < x → 0 < h → y ∈ Icc (x / 2) (2 * x) → z ∈ Icc (x / 2) (2 * x) →
      |y - z| ≤ h →
      let f := fun ρ : {ρ : ℂ // riemannZeta ρ = 0 ∧ 0 < ρ.re} ↦
        (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℂ) *
          (((y : ℂ) ^ ((ρ : ℂ) + 1) / ((ρ : ℂ) * ((ρ : ℂ) + 1)) -
            (z : ℂ) ^ ((ρ : ℂ) + 1) / ((ρ : ℂ) * ((ρ : ℂ) + 1))) / (h : ℂ))
      Summable (fun ρ ↦ ‖f ρ‖) ∧
        (∑' ρ, ‖f ρ‖) ≤ K * (2 * x ^ (1 / 2 : ℝ) * (1 + Real.log N) ^ 2 +
          (8 * x ^ (3 / 2 : ℝ) / h) * ((1 + Real.log N) / N)) := by
  classical
  obtain ⟨K, hK, hbound⟩ := hRH.exists_sum_riemannZeta_order_head_tail_le
  refine ⟨K, hK, fun N hN x h y z hx hh hy hz hyz ↦ ?_⟩
  dsimp only
  let F (ρ : ℂ) : ℂ :=
    ((y : ℂ) ^ (ρ + 1) / (ρ * (ρ + 1)) - (z : ℂ) ^ (ρ + 1) / (ρ * (ρ + 1))) / (h : ℂ)
  let Z := {ρ : ℂ // riemannZeta ρ = 0 ∧ 0 < ρ.re}
  let e : Z ↪ ℂ := ⟨Subtype.val, Subtype.val_injective⟩
  let A : ℝ := 2 * x ^ (1 / 2 : ℝ)
  let B : ℝ := 8 * x ^ (3 / 2 : ℝ) / h
  have hfinite (u : Finset Z) :
      (∑ ρ ∈ u, ‖(analyticOrderNatAt riemannZeta (ρ : ℂ) : ℂ) * F ρ‖) ≤
        K * (A * (1 + Real.log N) ^ 2 + B * ((1 + Real.log N) / N)) := by
    have hs : ∀ ρ ∈ u.map e, riemannZeta ρ = 0 ∧ 0 < ρ.re := by
      intro ρ hρ
      obtain ⟨a, _, rfl⟩ := Finset.mem_map.mp hρ
      exact a.property
    have hf : ∀ ρ ∈ u.map e, ‖F ρ‖ ≤ A / ‖ρ‖ ∧ ‖F ρ‖ ≤ B / ‖ρ * (ρ + 1)‖ := by
      intro ρ hρ
      have hzeta := hs ρ hρ
      have hρ1 : ρ ≠ 1 := by
        intro heq
        exact riemannZeta_one_ne_zero (heq ▸ hzeta.1)
      have hhalf := hRH.re_eq_half_of_riemannZeta_eq_zero_of_re_pos hzeta.2 hzeta.1 hρ1
      have hm := norm_sub_cpow_div_mul_add_one_div_le_min (s := ρ) hx hh
        (by rw [hhalf]; norm_num) (by rw [hhalf]; norm_num) hy hz hyz
      have hm' := le_min_iff.mp hm
      constructor
      · simpa only [F, A, hhalf] using hm'.1
      · calc
          ‖F ρ‖ ≤ 8 * x ^ (ρ.re + 1) / (h * ‖ρ‖ * ‖ρ + 1‖) := hm'.2
          _ = B / ‖ρ * (ρ + 1)‖ := by
            rw [hhalf, norm_mul]
            norm_num only [show (1 / 2 : ℝ) + 1 = 3 / 2 by norm_num]
            dsimp [B]
            ring
    have hh' := sum_order_mul_norm_le (K := K) (A := A) (B := B)
      (by dsimp [A]; positivity) (by dsimp [B]; positivity)
      N F (hbound N hN).1 (hbound N hN).2 (u.map e) hs hf
    simpa [e] using hh'
  exact ⟨summable_of_sum_le (fun ρ ↦ norm_nonneg _) hfinite,
    Real.tsum_le_of_sum_le (fun ρ ↦ norm_nonneg _) hfinite⟩

end RiemannHypothesis
