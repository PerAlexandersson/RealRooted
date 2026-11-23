/-
Copyright (c) 2026 Steve Hubbard, RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steve Hubbard, RealRooted contributors
-/
module

import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.NumberTheory.Harmonic.Bounds
import TauCeti.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Logarithmically weighted head and tail estimates

The reciprocal-square summability argument is adapted from Steve Hubbard's
`goldbach-lean`, revision `da5cf9edad7896290771dfcab8feee2906399e3d`,
`entries/dudek2014/LeanLab/PNTPort/ExplicitPsi1/ZeroSum.lean` (Apache-2.0).
The head bound uses the harmonic sum. The tail bound uses the integral test.
-/

public section

open Set MeasureTheory

namespace Real

/-- The logarithmic unit-band majorant is summable. Its first two terms are zero. -/
theorem summable_log_natCast_div_sub_one_sq :
    Summable (fun n : ℕ ↦ log n / ((n : ℝ) - 1) ^ 2) := by
  have hs : Summable (fun n : ℕ ↦ 8 * ((n : ℝ) ^ (3 / 2 : ℝ))⁻¹) :=
    (summable_nat_rpow_inv.mpr (by norm_num)).mul_left 8
  refine Summable.of_nonneg_of_le (fun n ↦ div_nonneg (log_natCast_nonneg n) (sq_nonneg _))
    (fun n ↦ ?_) hs
  rcases Nat.lt_or_ge n 2 with hn | hn
  · interval_cases n <;> simp
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hlog := log_le_rpow_div hn0.le (by norm_num : (0 : ℝ) < 1 / 2)
  have hsq : (n : ℝ) ^ 2 / 4 ≤ ((n : ℝ) - 1) ^ 2 := by nlinarith
  have hpow : (n : ℝ) ^ (2 : ℝ) =
      (n : ℝ) ^ (1 / 2 : ℝ) * (n : ℝ) ^ (3 / 2 : ℝ) := by
    rw [← rpow_add hn0]
    norm_num
  have hp3 : 0 < (n : ℝ) ^ (3 / 2 : ℝ) := rpow_pos_of_pos hn0 _
  have hd : 0 < ((n : ℝ) - 1) ^ 2 := by nlinarith
  rw [div_le_iff₀ hd]
  calc
    log n ≤ (n : ℝ) ^ (1 / 2 : ℝ) * 2 := by linarith
    _ = 8 * ((n : ℝ) ^ (3 / 2 : ℝ))⁻¹ * ((n : ℝ) ^ 2 / 4) := by
      rw [← rpow_two, hpow]
      field_simp
      ring
    _ ≤ 8 * ((n : ℝ) ^ (3 / 2 : ℝ))⁻¹ * ((n : ℝ) - 1) ^ 2 := by gcongr

/-- A logarithmic harmonic head has at most quadratic logarithmic growth, including `N = 0`. -/
theorem sum_Icc_log_natCast_div_le (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, log n / (n : ℝ) ≤ log N * (1 + log N) := by
  calc
    ∑ n ∈ Finset.Icc 1 N, log n / (n : ℝ) ≤
        ∑ n ∈ Finset.Icc 1 N, log N * (n : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro n hn
      obtain ⟨hn1, hnN⟩ := Finset.mem_Icc.mp hn
      rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right
        (log_le_log (by exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hn1) (by exact_mod_cast hnN))
        (by positivity)
    _ = log N * (harmonic N : ℝ) := by
      rw [← Finset.mul_sum]
      congr 1
      simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    _ ≤ log N * (1 + log N) :=
      mul_le_mul_of_nonneg_left (harmonic_le_one_add_log N) (log_natCast_nonneg N)

private theorem hasDerivAt_one_add_log_div_sq {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun t : ℝ ↦ (1 + log t) / t ^ 2) (-(1 + 2 * log x) / x ^ 3) x := by
  have hd : HasDerivAt (fun t : ℝ ↦ 1 + log t) x⁻¹ x :=
    (hasDerivAt_log hx.ne').const_add 1
  have hs : HasDerivAt (fun t : ℝ ↦ t ^ 2) (2 * x) x := by
    simpa using hasDerivAt_pow 2 x
  have h : HasDerivAt (fun t : ℝ ↦ (1 + log t) / t ^ 2)
      ((x⁻¹ * x ^ 2 - (1 + log x) * (2 * x)) / (x ^ 2) ^ 2) x :=
    hd.div hs (pow_ne_zero 2 hx.ne')
  convert h using 1
  field_simp
  ring

/-- A convenient positive decreasing majorant for `log t / t²`. -/
theorem antitoneOn_one_add_log_div_sq :
    AntitoneOn (fun t : ℝ ↦ (1 + log t) / t ^ 2) (Ici 1) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 1)
  · intro x hx
    exact (hasDerivAt_one_add_log_div_sq
      (lt_of_lt_of_le zero_lt_one hx)).continuousAt.continuousWithinAt
  · intro x hx
    exact (hasDerivAt_one_add_log_div_sq
      (lt_of_lt_of_le zero_lt_one (interior_subset hx))).hasDerivWithinAt
  · intro x hx
    have hx1 : 1 ≤ x := interior_subset hx
    exact div_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (by linarith [log_nonneg hx1])) (by positivity)

private theorem one_add_log_div_sq_eq (x : ℝ) :
    (1 + log x) / x ^ 2 = x ^ (-2 : ℝ) + x ^ (-2 : ℝ) * log x := by
  rw [show (-2 : ℝ) = -(2 : ℕ) by norm_num, rpow_neg_natCast]
  simp only [zpow_neg, zpow_natCast]
  ring

/-- The tail of the logarithmic reciprocal-square majorant is `O(log N / N)`. -/
theorem tsum_one_add_log_div_sq_add_le {N : ℕ} (hN : 1 ≤ N) :
    ∑' n : ℕ, (1 + log (n + N + 1 : ℕ)) / (n + N + 1 : ℝ) ^ 2 ≤
      (log N + 2) / N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hpow := integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hN0
  have hlog := TauCeti.integrableOn_Ioi_rpow_mul_log_of_lt
    (by norm_num : (-2 : ℝ) < -1) hN0
  have hint : IntegrableOn (fun t : ℝ ↦ (1 + log t) / t ^ 2) (Ioi (N : ℝ)) := by
    simp_rw [one_add_log_div_sq_eq]
    exact hpow.add hlog
  have hval : (∫ t in Ioi (N : ℝ), (1 + log t) / t ^ 2) = (log N + 2) / N := by
    simp_rw [one_add_log_div_sq_eq]
    rw [integral_add hpow hlog, integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hN0,
      TauCeti.integral_Ioi_rpow_mul_log_of_lt (by norm_num : (-2 : ℝ) < -1) hN0]
    norm_num [rpow_neg_one]
    ring
  have hbound :=
    (antitoneOn_one_add_log_div_sq.mono (Ici_subset_Ici.mpr hN1)).tsum_comp_add_le_integral
    N hint (fun t ht ↦ div_nonneg (by linarith [log_nonneg (hN1.trans ht.le)]) (sq_nonneg t))
  rw [hval] at hbound
  simpa only [Nat.cast_add, Nat.cast_one] using hbound

end Real
