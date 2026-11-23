/-
Copyright (c) 2026 Steve Hubbard, RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steve Hubbard, RealRooted contributors
-/
module

public import Mathlib.NumberTheory.LSeries.ZetaZeros
public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Topology.Algebra.InfiniteSum.Real
import RealRooted.Mathlib.NumberTheory.LSeries.RiemannZeta.ZeroWindow
import RealRooted.Mathlib.Topology.Algebra.InfiniteSum.FiberMajorant
import RealRooted.Mathlib.Analysis.SpecialFunctions.Log.Weights
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Algebra.Order.Floor.Ring

/-!
# Absolute convergence of the integrated zeta zero series under RH

Zeros are counted with their full analytic multiplicities. A band
`n - 1 < |Im ρ| ≤ n` is covered by the two fixed-width windows centered at
`n` and `-n`. The compact low-height part is finite unconditionally by
Mathlib's zeta-zero discreteness theorem.

The unit-band argument follows Steve Hubbard's `goldbach-lean`, revision
`da5cf9edad7896290771dfcab8feee2906399e3d`,
`entries/dudek2014/LeanLab/PNTPort/ExplicitPsi1/ZeroSum.lean` (Apache-2.0).
-/

public section

open Complex Set Filter

namespace TauCeti

/-- Positive-real-part zeta zeros below any fixed absolute height form a finite set. -/
theorem finite_riemannZeta_pos_zero_height_le (T : ℝ) :
    {ρ : ℂ | riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ |ρ.im| ≤ T}.Finite := by
  have hc : IsCompact ((Icc (0 : ℝ) 1) ×ℂ Icc (-T) T) :=
    isCompact_Icc.reProdIm isCompact_Icc
  apply hc.inter_riemannZetaZeros_finite.subset
  intro ρ hρ
  have hre : ρ.re < 1 := by
    by_contra h
    exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp h) hρ.1
  exact ⟨⟨⟨hρ.2.1.le, hre.le⟩, abs_le.mp hρ.2.2⟩, hρ.1⟩

/-- The denominator of the once-integrated zero contribution dominates the square of its height. -/
theorem sq_abs_im_le_norm_mul_add_one (ρ : ℂ) : |ρ.im| ^ 2 ≤ ‖ρ * (ρ + 1)‖ := by
  rw [norm_mul, pow_two]
  exact mul_le_mul (abs_im_le_norm ρ)
    (by simpa using abs_im_le_norm (ρ + 1)) (abs_nonneg _) (norm_nonneg _)

end TauCeti

namespace RiemannHypothesis

open TauCeti

/-- The total multiplicity in an absolute unit-height band is logarithmically bounded under RH. -/
theorem exists_sum_riemannZeta_order_band_le_log (hRH : RiemannHypothesis) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 4 ≤ n → ∀ s : Finset ℂ,
      (∀ ρ ∈ s, riemannZeta ρ = 0 ∧ 0 < ρ.re ∧
        (n : ℝ) - 1 < |ρ.im| ∧ |ρ.im| ≤ n) →
      (∑ ρ ∈ s, (analyticOrderNatAt riemannZeta ρ : ℝ)) ≤ C * Real.log n := by
  classical
  obtain ⟨C, hC, hb⟩ := hRH.exists_sum_riemannZetaZeroWindow_order_wide_le_log
  refine ⟨2 * C, by positivity, fun n hn s hs ↦ ?_⟩
  have hn4 : (4 : ℝ) ≤ n := by exact_mod_cast hn
  obtain ⟨hp, hpb⟩ := hb n (by simpa using hn4)
  obtain ⟨hm, hmb⟩ := hb (-(n : ℝ)) (by simpa using hn4)
  have hsub : s ⊆ hp.toFinset ∪ hm.toFinset := by
    intro ρ hρ
    obtain ⟨hz, hre, hlo, hhi⟩ := hs ρ hρ
    simp only [Finset.mem_union, Set.Finite.mem_toFinset, mem_riemannZetaZeroWindow]
    by_cases hi : 0 ≤ ρ.im
    · left
      rw [abs_of_nonneg hi] at hlo hhi
      exact ⟨hz, hre, abs_le.mpr ⟨by linarith, by linarith⟩⟩
    · right
      rw [abs_of_neg (lt_of_not_ge hi)] at hlo hhi
      exact ⟨hz, hre, abs_le.mpr ⟨by linarith, by linarith⟩⟩
  have hu := Finset.sum_union_inter (s₁ := hp.toFinset) (s₂ := hm.toFinset)
    (f := fun ρ ↦ (analyticOrderNatAt riemannZeta ρ : ℝ))
  have hnonneg : 0 ≤ ∑ ρ ∈ hp.toFinset ∩ hm.toFinset,
      (analyticOrderNatAt riemannZeta ρ : ℝ) := Finset.sum_nonneg (fun _ _ ↦ Nat.cast_nonneg _)
  have hsum : (∑ ρ ∈ s, (analyticOrderNatAt riemannZeta ρ : ℝ)) ≤
      ∑ ρ ∈ hp.toFinset ∪ hm.toFinset, (analyticOrderNatAt riemannZeta ρ : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun ρ _ _ ↦ Nat.cast_nonneg (analyticOrderNatAt riemannZeta ρ))
  simp only [abs_neg, abs_of_nonneg (show (0 : ℝ) ≤ n from Nat.cast_nonneg n)] at hpb hmb
  linarith

/-- Under RH the multiplicity-weighted once-integrated zeta zero series is absolutely summable. -/
theorem summable_riemannZeta_order_div_norm_mul_add_one (hRH : RiemannHypothesis) :
    Summable (fun ρ : {ρ : ℂ // riemannZeta ρ = 0 ∧ 0 < ρ.re} ↦
      (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) / ‖(ρ : ℂ) * ((ρ : ℂ) + 1)‖) := by
  classical
  let Z := {ρ : ℂ // riemannZeta ρ = 0 ∧ 0 < ρ.re}
  let low : Set Z := {ρ | |(ρ : ℂ).im| ≤ 4}
  have hlow : low.Finite := by
    have hf := (finite_riemannZeta_pos_zero_height_le 4).preimage
      (f := fun ρ : Z ↦ (ρ : ℂ)) Subtype.val_injective.injOn
    apply hf.subset
    intro ρ hρ
    exact ⟨ρ.property.1, ρ.property.2, hρ⟩
  apply hlow.summable_compl_iff.mp
  let H := (lowᶜ : Set Z)
  let e : H ↪ ℂ := ⟨fun ρ ↦ ((ρ : Z) : ℂ),
    fun a b hab ↦ Subtype.ext (Subtype.ext hab)⟩
  let bin (ρ : H) : ℕ := ⌈|(e ρ).im|⌉₊
  have hlarge (ρ : H) : 4 < |(e ρ).im| := lt_of_not_ge ρ.property
  have hbin (ρ : H) : 5 ≤ bin ρ := by
    have h4 : 4 < bin ρ := Nat.lt_ceil.mpr (by simpa using hlarge ρ)
    lia
  have hband (ρ : H) : (bin ρ : ℝ) - 1 < |(e ρ).im| ∧ |(e ρ).im| ≤ bin ρ := by
    have hb5 := hbin ρ
    have hb := (Nat.ceil_eq_iff (by lia : bin ρ ≠ 0)).mp (show ⌈|(e ρ).im|⌉₊ = bin ρ from rfl)
    rw [Nat.cast_sub (by lia)] at hb
    simpa only [Nat.cast_one] using hb
  obtain ⟨C, hC, hb⟩ := hRH.exists_sum_riemannZeta_order_band_le_log
  let w (ρ : H) : ℝ := analyticOrderNatAt riemannZeta (e ρ)
  let v (ρ : H) : ℝ := w ρ / ‖e ρ * (e ρ + 1)‖
  let B (n : ℕ) : ℝ := C * Real.log n
  let W (n : ℕ) : ℝ := (((n : ℝ) - 1) ^ 2)⁻¹
  change Summable v
  apply summable_of_finite_fiber_majorant bin w v B W
  · exact fun ρ ↦ by dsimp [v, w]; positivity
  · exact fun n ↦ mul_nonneg hC.le (Real.log_natCast_nonneg n)
  · exact fun n ↦ inv_nonneg.mpr (sq_nonneg _)
  · intro ρ
    have hn : (5 : ℝ) ≤ bin ρ := by exact_mod_cast hbin ρ
    have hd : 0 < ((bin ρ : ℝ) - 1) ^ 2 := by nlinarith
    have hden : ((bin ρ : ℝ) - 1) ^ 2 ≤ ‖e ρ * (e ρ + 1)‖ := by
      calc
        ((bin ρ : ℝ) - 1) ^ 2 ≤ |(e ρ).im| ^ 2 :=
          pow_le_pow_left₀ (by linarith) (hband ρ).1.le 2
        _ ≤ ‖e ρ * (e ρ + 1)‖ := sq_abs_im_le_norm_mul_add_one _
    exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hd hden
  · intro n s hs
    by_cases hn : 4 ≤ n
    · have hh := hb n hn (s.map e) (by
        intro ρ hρ
        obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hρ
        have heq := hs a ha
        exact ⟨a.val.property.1, a.val.property.2, by simpa [heq] using hband a⟩)
      simpa only [Finset.sum_map] using hh
    · have hempty : s = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro ρ hρ
        have := hbin ρ
        rw [hs ρ hρ] at this
        lia
      rw [hempty, Finset.sum_empty]
      exact mul_nonneg hC.le (Real.log_natCast_nonneg n)
  · simpa only [B, W, div_eq_mul_inv, mul_assoc] using
      Real.summable_log_natCast_div_sub_one_sq.mul_left C

end RiemannHypothesis
