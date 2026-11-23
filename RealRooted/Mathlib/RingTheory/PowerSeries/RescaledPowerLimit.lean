/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.Expand
public import Mathlib.RingTheory.PowerSeries.Exp
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import RealRooted.Mathlib.RingTheory.PowerSeries.PowerCoefficient
import RealRooted.Mathlib.Analysis.SpecialFunctions.ChooseRpow

/-!
# Coefficient limits of rescaled powers of a formal series

For `φ = 1 + X^p * ψ`, the series `φ(m^(-1/p) X)^m` tends coefficientwise
to `exp(ψ(0) X^p)`. The proof uses fixed finite binomial sums and does not
assume that either formal series has a positive convergence radius.
-/

public section

open Filter Topology Finset

namespace PowerSeries

/-- Only the critical binomial index survives after rescaling. -/
private theorem tendsto_power_coefficient_term (ψ : PowerSeries ℝ) {p : ℕ}
    (hp : 0 < p) (j k : ℕ) (hk : k ≤ j / p) :
    Tendsto (fun m : ℕ ↦ (m.choose k : ℝ) * (m : ℝ) ^ (-((j : ℝ) / p)) *
      coeff (j - p * k) (ψ ^ k)) atTop
      (𝓝 (if p * k = j then constantCoeff ψ ^ k / k.factorial else 0)) := by
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp
  by_cases hpk : p * k = j
  · have hu : (j : ℝ) / p = k := by
      rw [← hpk, Nat.cast_mul]
      field_simp [hpR.ne']
    have h := (Nat.tendsto_choose_mul_rpow_atTop k).mul_const
      (coeff (j - p * k) (ψ ^ k))
    have hsub : j - p * k = 0 := by lia
    rw [hu, ite_eq_left hpk]
    simpa only [hsub, coeff_zero_eq_constantCoeff, map_pow, one_div,
      div_eq_mul_inv, mul_one, one_mul, mul_comm] using h
  · have hle : p * k ≤ j :=
      (Nat.mul_le_mul_left p hk).trans (Nat.mul_div_le j p)
    have hlt : p * k < j := lt_of_le_of_ne hle hpk
    have hu : (k : ℝ) < (j : ℝ) / p := by
      apply (lt_div_iff₀ hpR).mpr
      exact_mod_cast (by simpa only [Nat.mul_comm] using hlt)
    have h := (Nat.tendsto_choose_mul_rpow_atTop_of_lt k hu).mul_const
      (coeff (j - p * k) (ψ ^ k))
    simpa only [ite_eq_right hpk, zero_mul] using h

/-- The critical-index sum records the divisibility of the output degree. -/
private theorem sum_critical_coefficients (b : ℝ) {p : ℕ} (hp : 0 < p) (j : ℕ) :
    (∑ k ∈ range (j / p + 1),
      (if p * k = j then b ^ k / k.factorial else 0)) =
      if p ∣ j then b ^ (j / p) / (j / p).factorial else 0 := by
  by_cases hdiv : p ∣ j
  · have hmul : p * (j / p) = j := Nat.mul_div_cancel' hdiv
    rw [ite_eq_left hdiv, Finset.sum_eq_single (j / p)]
    · simp [hmul]
    · intro k _ hk
      have hne : p * k ≠ j := by
        intro h
        exact hk (Nat.eq_of_mul_eq_mul_left hp (h.trans hmul.symm))
      exact ite_eq_right hne
    · simp
  · rw [ite_eq_right hdiv]
    apply Finset.sum_eq_zero
    intro k _
    have hne : p * k ≠ j := fun h ↦ hdiv ⟨k, h.symm⟩
    exact ite_eq_right hne

/-- The explicit coefficient limit of a rescaled formal power. -/
theorem tendsto_coeff_rescaled_one_add_X_pow_mul (ψ : PowerSeries ℝ) {p : ℕ}
    (hp : 0 < p) (j : ℕ) :
    Tendsto (fun m : ℕ ↦ coeff j
      ((rescale ((m : ℝ) ^ (-(p : ℝ)⁻¹)) (1 + X ^ p * ψ)) ^ m)) atTop
      (𝓝 (if p ∣ j then constantCoeff ψ ^ (j / p) / (j / p).factorial else 0)) := by
  have hscale (m : ℕ) : ((m : ℝ) ^ (-(p : ℝ)⁻¹)) ^ j =
      (m : ℝ) ^ (-((j : ℝ) / p)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg m)]
    congr 1
    ring
  have heq : (fun m : ℕ ↦ coeff j
      ((rescale ((m : ℝ) ^ (-(p : ℝ)⁻¹)) (1 + X ^ p * ψ)) ^ m)) =
      (fun m : ℕ ↦ ∑ k ∈ range (j / p + 1),
        (m.choose k : ℝ) * (m : ℝ) ^ (-((j : ℝ) / p)) *
          coeff (j - p * k) (ψ ^ k)) := by
    funext m
    rw [← map_pow, coeff_rescale, hscale,
      coeff_one_add_X_pow_mul_pow ψ hp, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [heq]
  have h := tendsto_finsetSum (range (j / p + 1))
    (fun k hk ↦ tendsto_power_coefficient_term ψ hp j k
      (Nat.lt_succ_iff.mp (mem_range.mp hk)))
  rwa [sum_critical_coefficients (constantCoeff ψ) hp j] at h

/-- The rescaled formal powers converge coefficientwise to the formal
exponential of their first possible nonconstant term. -/
theorem tendsto_coeff_rescale_pow_exp (ψ : PowerSeries ℝ) {p : ℕ}
    (hp : 0 < p) (j : ℕ) :
    Tendsto (fun m : ℕ ↦ coeff j
      ((rescale ((m : ℝ) ^ (-(p : ℝ)⁻¹)) (1 + X ^ p * ψ)) ^ m)) atTop
      (𝓝 (coeff j (expand p hp.ne'
        (rescale (constantCoeff ψ) (exp ℝ))))) := by
  simpa only [coeff_expand, coeff_rescale, coeff_exp, map_div₀, map_one,
    map_natCast, mul_one_div] using tendsto_coeff_rescaled_one_add_X_pow_mul ψ hp j

end PowerSeries
