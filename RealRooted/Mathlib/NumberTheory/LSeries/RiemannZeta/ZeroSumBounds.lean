/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import Mathlib.Analysis.Analytic.Order
public import Mathlib.NumberTheory.LSeries.RiemannZeta
import RealRooted.Mathlib.NumberTheory.LSeries.RiemannZeta.ZeroSum
import RealRooted.Mathlib.Analysis.SpecialFunctions.Log.BandBounds
import Mathlib.Algebra.Order.Floor.Ring

/-!
# Multiplicity-weighted head and tail estimates for zeta zeros under RH

The finitely many zeros with absolute height at most four contribute a fixed
constant to the reciprocal-norm head. The high zeros are grouped into unit
bands. The quadratic-denominator tail has the sharp order `log N / N`.
-/

public section

open Complex Set

namespace RiemannHypothesis

private theorem ceil_abs_im_bounds {ρ : ℂ} (hρ : 4 < |ρ.im|) :
    5 ≤ ⌈|ρ.im|⌉₊ ∧
    (⌈|ρ.im|⌉₊ : ℝ) / 2 ≤ ‖ρ‖ ∧
    (⌈|ρ.im|⌉₊ : ℝ) ^ 2 / 4 ≤ ‖ρ * (ρ + 1)‖ ∧
    (⌈|ρ.im|⌉₊ : ℝ) - 1 < |ρ.im| ∧ |ρ.im| ≤ ⌈|ρ.im|⌉₊ := by
  have hn : 5 ≤ ⌈|ρ.im|⌉₊ := by
    have : 4 < ⌈|ρ.im|⌉₊ := Nat.lt_ceil.mpr hρ
    lia
  have hc := Nat.ceil_lt_add_one (abs_nonneg ρ.im)
  have hhalf : (⌈|ρ.im|⌉₊ : ℝ) / 2 ≤ |ρ.im| := by linarith
  have hsq : (⌈|ρ.im|⌉₊ : ℝ) ^ 2 / 4 ≤ |ρ.im| ^ 2 := by
    convert pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (⌈|ρ.im|⌉₊ : ℝ) / 2) hhalf 2 using 1
    ring
  exact ⟨hn, hhalf.trans (abs_im_le_norm ρ),
    hsq.trans (TauCeti.sq_abs_im_le_norm_mul_add_one ρ),
    by linarith, Nat.le_ceil _⟩

private theorem sum_order_div_norm_high_le {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ n : ℕ, 4 ≤ n → ∀ s : Finset ℂ,
      (∀ ρ ∈ s, riemannZeta ρ = 0 ∧ 0 < ρ.re ∧
        (n : ℝ) - 1 < |ρ.im| ∧ |ρ.im| ≤ n) →
      (∑ ρ ∈ s, (analyticOrderNatAt riemannZeta ρ : ℝ)) ≤ C * Real.log n)
    (N : ℕ) (s : Finset ℂ)
    (hs : ∀ ρ ∈ s, riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ 4 < |ρ.im| ∧ |ρ.im| ≤ N) :
    ∑ ρ ∈ s, (analyticOrderNatAt riemannZeta ρ : ℝ) / ‖ρ‖ ≤
      2 * C * (Real.log N * (1 + Real.log N)) := by
  classical
  apply Finset.sum_le_log_mul_one_add_log_of_fiber_bound s
    (fun ρ ↦ ⌈|ρ.im|⌉₊) (fun ρ ↦ (analyticOrderNatAt riemannZeta ρ : ℝ))
    (fun ρ ↦ (analyticOrderNatAt riemannZeta ρ : ℝ) / ‖ρ‖) hC N
  · intro ρ hρ
    obtain ⟨_, _, hh, hN⟩ := hs ρ hρ
    exact Finset.mem_Icc.mpr ⟨by have := (ceil_abs_im_bounds hh).1; lia,
      Nat.ceil_le.mpr hN⟩
  · intro ρ hρ
    have hc := ceil_abs_im_bounds (hs ρ hρ).2.2.1
    have hn : (0 : ℝ) < ⌈|ρ.im|⌉₊ := by exact_mod_cast lt_of_lt_of_le (by norm_num : 0 < 5) hc.1
    calc
      (analyticOrderNatAt riemannZeta ρ : ℝ) / ‖ρ‖ ≤
          (analyticOrderNatAt riemannZeta ρ : ℝ) / ((⌈|ρ.im|⌉₊ : ℝ) / 2) :=
        div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity) hc.2.1
      _ = (analyticOrderNatAt riemannZeta ρ : ℝ) * (2 / (⌈|ρ.im|⌉₊ : ℝ)) := by
        field_simp
  · intro n hn
    by_cases hn4 : 4 ≤ n
    · apply hb n hn4
      intro ρ hρ
      obtain ⟨hρs, heq⟩ := Finset.mem_filter.mp hρ
      obtain ⟨hz, hre, hh, _⟩ := hs ρ hρs
      exact ⟨hz, hre, by simpa only [heq] using (ceil_abs_im_bounds hh).2.2.2⟩
    · have hempty : s.filter (fun ρ ↦ ⌈|ρ.im|⌉₊ = n) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro ρ hρ
        obtain ⟨hρs, heq⟩ := Finset.mem_filter.mp hρ
        have hh := (ceil_abs_im_bounds (hs ρ hρs).2.2.1).1
        lia
      rw [hempty, Finset.sum_empty]
      exact mul_nonneg hC (Real.log_natCast_nonneg n)

private theorem sum_order_div_norm_mul_add_one_tail_le {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ n : ℕ, 4 ≤ n → ∀ s : Finset ℂ,
      (∀ ρ ∈ s, riemannZeta ρ = 0 ∧ 0 < ρ.re ∧
        (n : ℝ) - 1 < |ρ.im| ∧ |ρ.im| ≤ n) →
      (∑ ρ ∈ s, (analyticOrderNatAt riemannZeta ρ : ℝ)) ≤ C * Real.log n)
    {N : ℕ} (hN : 4 ≤ N) (s : Finset ℂ)
    (hs : ∀ ρ ∈ s, riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ (N : ℝ) < |ρ.im|) :
    ∑ ρ ∈ s, (analyticOrderNatAt riemannZeta ρ : ℝ) / ‖ρ * (ρ + 1)‖ ≤
      4 * C * ((Real.log N + 2) / N) := by
  classical
  let bin (ρ : ℂ) : ℕ := ⌈|ρ.im|⌉₊ - (N + 1)
  have hn4 : (4 : ℝ) ≤ N := by exact_mod_cast hN
  have hceil (ρ : ℂ) (hρ : ρ ∈ s) : N + 1 ≤ ⌈|ρ.im|⌉₊ := by
    have := Nat.lt_ceil.mpr (hs ρ hρ).2.2
    lia
  have hbin (ρ : ℂ) (hρ : ρ ∈ s) : bin ρ + N + 1 = ⌈|ρ.im|⌉₊ := by
    have := hceil ρ hρ
    dsimp [bin]
    lia
  apply Finset.sum_le_log_add_div_of_fiber_bound s bin
    (fun ρ ↦ (analyticOrderNatAt riemannZeta ρ : ℝ))
    (fun ρ ↦ (analyticOrderNatAt riemannZeta ρ : ℝ) / ‖ρ * (ρ + 1)‖) hC (by lia : 1 ≤ N)
  · intro ρ hρ
    have hc := ceil_abs_im_bounds (by linarith [(hs ρ hρ).2.2])
    have hn : (0 : ℝ) < ⌈|ρ.im|⌉₊ := by exact_mod_cast lt_of_lt_of_le (by norm_num : 0 < 5) hc.1
    have heq : (bin ρ : ℝ) + N + 1 = ⌈|ρ.im|⌉₊ := by exact_mod_cast hbin ρ hρ
    rw [heq]
    calc
      (analyticOrderNatAt riemannZeta ρ : ℝ) / ‖ρ * (ρ + 1)‖ ≤
          (analyticOrderNatAt riemannZeta ρ : ℝ) / ((⌈|ρ.im|⌉₊ : ℝ) ^ 2 / 4) :=
        div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity) hc.2.2.1
      _ = (analyticOrderNatAt riemannZeta ρ : ℝ) * (4 / (⌈|ρ.im|⌉₊ : ℝ) ^ 2) := by
        field_simp
  · intro n hn
    apply hb (n + N + 1) (by lia)
    intro ρ hρ
    obtain ⟨hρs, heq⟩ := Finset.mem_filter.mp hρ
    obtain ⟨hz, hre, hh⟩ := hs ρ hρs
    have hband := (ceil_abs_im_bounds (by linarith : 4 < |ρ.im|)).2.2.2
    have hceil' : ⌈|ρ.im|⌉₊ = n + N + 1 := by rw [← hbin ρ hρs, heq]
    exact ⟨hz, hre, by simpa only [hceil'] using hband⟩

/-- A common positive constant bounds the reciprocal-norm head and quadratic-denominator tail
of every finite set of positive-real-part zeta zeros under RH, retaining multiplicities. -/
theorem exists_sum_riemannZeta_order_head_tail_le (hRH : RiemannHypothesis) :
    ∃ K : ℝ, 0 < K ∧ ∀ N : ℕ, 4 ≤ N →
      (∀ s : Finset ℂ, (∀ ρ ∈ s, riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ |ρ.im| ≤ N) →
        ∑ ρ ∈ s, (analyticOrderNatAt riemannZeta ρ : ℝ) / ‖ρ‖ ≤ K * (1 + Real.log N) ^ 2) ∧
      (∀ s : Finset ℂ, (∀ ρ ∈ s, riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ (N : ℝ) < |ρ.im|) →
        ∑ ρ ∈ s, (analyticOrderNatAt riemannZeta ρ : ℝ) / ‖ρ * (ρ + 1)‖ ≤
          K * ((1 + Real.log N) / N)) := by
  classical
  obtain ⟨C, hC, hb⟩ := hRH.exists_sum_riemannZeta_order_band_le_log
  let low := (TauCeti.finite_riemannZeta_pos_zero_height_le 4).toFinset
  let L : ℝ := ∑ ρ ∈ low, (analyticOrderNatAt riemannZeta ρ : ℝ) / ‖ρ‖
  have hL : 0 ≤ L := Finset.sum_nonneg (fun _ _ ↦ by positivity)
  refine ⟨L + 8 * C + 1, by positivity, fun N hN ↦ ?_⟩
  have hlog : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by lia)
  constructor
  · intro s hs
    have hlo : (∑ ρ ∈ s.filter (fun ρ ↦ |ρ.im| ≤ 4),
        (analyticOrderNatAt riemannZeta ρ : ℝ) / ‖ρ‖) ≤ L := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro ρ hρ
        obtain ⟨hρs, hheight⟩ := Finset.mem_filter.mp hρ
        exact (TauCeti.finite_riemannZeta_pos_zero_height_le 4).mem_toFinset.mpr
          ⟨(hs ρ hρs).1, (hs ρ hρs).2.1, hheight⟩
      · exact fun _ _ _ ↦ by positivity
    have hhi := sum_order_div_norm_high_le hC.le hb N
      (s.filter (fun ρ ↦ ¬ |ρ.im| ≤ 4)) (by
        intro ρ hρ
        obtain ⟨hρs, hheight⟩ := Finset.mem_filter.mp hρ
        exact ⟨(hs ρ hρs).1, (hs ρ hρs).2.1, lt_of_not_ge hheight, (hs ρ hρs).2.2⟩)
    rw [← Finset.sum_filter_add_sum_filter_not s (fun ρ ↦ |ρ.im| ≤ 4)]
    have hsq : 1 ≤ (1 + Real.log N) ^ 2 := by nlinarith
    have hLH : L ≤ L * (1 + Real.log N) ^ 2 := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hsq hL
    have hCH : 2 * C * (Real.log N * (1 + Real.log N)) ≤
        2 * C * (1 + Real.log N) ^ 2 :=
      mul_le_mul_of_nonneg_left (by nlinarith :
        Real.log N * (1 + Real.log N) ≤ (1 + Real.log N) ^ 2) (by positivity)
    have hCK : 2 * C ≤ 8 * C + 1 := by linarith
    have hCK' := mul_le_mul_of_nonneg_right hCK (sq_nonneg (1 + Real.log N))
    nlinarith
  · intro s hs
    have ht := sum_order_div_norm_mul_add_one_tail_le hC.le hb hN s hs
    have hlog' : Real.log N + 2 ≤ 2 * (1 + Real.log N) := by linarith
    have hdiv := div_le_div_of_nonneg_right hlog' hN0.le
    have hK : 8 * C ≤ L + 8 * C + 1 := by linarith
    have hK' := mul_le_mul_of_nonneg_right hK
      (div_nonneg (by positivity : 0 ≤ 1 + Real.log N) hN0.le)
    calc
      _ ≤ 4 * C * ((Real.log N + 2) / N) := ht
      _ ≤ 8 * C * ((1 + Real.log N) / N) := by
        convert mul_le_mul_of_nonneg_left hdiv (by positivity : 0 ≤ 4 * C) using 1
        ring
      _ ≤ _ := hK'

end RiemannHypothesis
