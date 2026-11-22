/-
Copyright (c) 2026 Steve Hubbard, RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steve Hubbard, RealRooted contributors
-/
module

public import Mathlib.NumberTheory.LSeries.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import TauCeti.Analysis.MellinInversion
import TauCeti.NumberTheory.LSeries.Continuity

/-!
# The first Riesz mean of a Dirichlet series

An absolutely convergent Dirichlet series on a positive vertical line has a first-order
Perron formula with the continuous weight `max (1 - n / x) 0`. The kernel is
`1 / (s * (s + 1))`, whose Mellin inversion is already available in TauCeti.

The interchange argument is adapted and generalized from Steve Hubbard's
`goldbach-lean`, commit `da5cf9edad7896290771dfcab8feee2906399e3d`,
`entries/dudek2014/LeanLab/PNTPort/ZetaZeros/Perron1.lean` (Apache-2.0).
The arithmetic input here is arbitrary; no hypothesis about zeta zeros is used.
-/

public section

open Complex Filter MeasureTheory
open scoped Real

namespace LSeries

/-- The continuous first-order cutoff turns an infinite series into a finite weighted sum,
including an integer endpoint with weight zero. -/
theorem tsum_mul_max_one_sub_eq_sum (f : ℕ → ℂ) {x : ℝ} (hx : 0 < x) :
    ∑' n : ℕ, f n * (max (1 - (n : ℝ) / x) 0 : ℝ) =
      ∑ n ∈ Finset.Iic ⌊x⌋₊, f n * (1 - (n : ℝ) / x : ℝ) := by
  rw [tsum_eq_sum (s := Finset.Iic ⌊x⌋₊) ?_]
  · refine Finset.sum_congr rfl fun n hn ↦ ?_
    have hnx : (n : ℝ) ≤ x := (Nat.le_floor_iff hx.le).mp (Finset.mem_Iic.mp hn)
    rw [max_eq_left (sub_nonneg.mpr ((div_le_one hx).mpr hnx))]
  · intro n hn
    have hxn : x < n := Nat.lt_of_floor_lt (by simpa using hn)
    rw [max_eq_right (sub_nonpos.mpr ((le_div_iff₀ hx).mpr (by linarith)))]
    simp

private theorem integral_riesz_inverse {c y : ℝ} (hc : 0 < c) (hy : 0 < y) :
    ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
        (∫ t : ℝ, (y : ℂ) ^ (-((c : ℂ) + t * I)) *
          (((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1))⁻¹) =
      (max (1 - y) 0 : ℝ) := by
  have h := TauCeti.mellinInv_inv_mul_add_one hc hy
  simpa only [mellinInv, smul_eq_mul, Complex.real_smul, one_div, Complex.ofReal_inv] using h

private theorem cpow_div_neg {n x : ℝ} (hn : 0 < n) (hx : 0 < x) (s : ℂ) :
    ((n / x : ℝ) : ℂ) ^ (-s) = (x : ℂ) ^ s / (n : ℂ) ^ s := by
  rw [div_eq_mul_inv, Complex.ofReal_mul, mul_cpow_ofReal_nonneg hn.le (inv_nonneg.mpr hx.le),
    Complex.ofReal_inv, inv_cpow_ofReal_nonneg hx.le, cpow_neg, cpow_neg, inv_inv]
  ring

/-- Absolute convergence of a Dirichlet series makes its first-order Perron integrand
integrable on every positive vertical line of summability, including a boundary line. -/
theorem integrable_mul_cpow_div_mul_add_one {f : ℕ → ℂ} {x c : ℝ}
    (hx : 0 < x) (hc : 0 < c) (hf : LSeriesSummable f (c : ℂ)) :
    Integrable (fun t : ℝ ↦ LSeries f ((c : ℂ) + t * I) *
      (x : ℂ) ^ ((c : ℂ) + t * I) /
        (((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1))) := by
  have hcont : Continuous fun t : ℝ ↦
      LSeries f ((c : ℂ) + t * I) * (x : ℂ) ^ ((c : ℂ) + t * I) :=
    (TauCeti.LSeries.continuous_vertical f c).mul
      (Continuous.const_cpow (by fun_prop) (Or.inl (Complex.ofReal_ne_zero.2 hx.ne')))
  simp only [div_eq_mul_inv]
  refine (TauCeti.verticalIntegrable_inv_mul_add_one hc.ne' (by linarith)).bdd_mul
    (c := (∑' n, ‖LSeries.term f (c : ℂ) n‖) * x ^ c) hcont.aestronglyMeasurable ?_
  refine Eventually.of_forall fun t ↦ ?_
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp only [add_re, mul_re, ofReal_re, ofReal_im, I_re, I_im, mul_zero, zero_mul, sub_zero,
    add_zero]
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hx.le _)
  have ht := hf.of_re_le_re (s' := (c : ℂ) + t * I) (by simp)
  exact (norm_tsum_le_tsum_norm ht.norm).trans
    (ht.norm.tsum_le_tsum (LSeries.norm_term_le_of_re_le_re f (by simp)) hf.norm)

/-- The first-order Perron formula for an absolutely convergent Dirichlet series.
The zeroth coefficient is assumed zero because `LSeries` discards it. -/
theorem tsum_mul_max_one_sub_eq_integral {f : ℕ → ℂ} (hf0 : f 0 = 0)
    {x c : ℝ} (hx : 0 < x) (hc : 0 < c) (hf : LSeriesSummable f (c : ℂ)) :
    ∑' n : ℕ, f n * (max (1 - (n : ℝ) / x) 0 : ℝ) =
      ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
        ∫ t : ℝ, LSeries f ((c : ℂ) + t * I) * (x : ℂ) ^ ((c : ℂ) + t * I) /
          (((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1)) := by
  let K : ℝ → ℂ := fun t ↦ (((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1))⁻¹
  let F : ℕ → ℝ → ℂ := fun n t ↦
    f n * (((n / x : ℝ) : ℂ) ^ (-((c : ℂ) + t * I)) * K t)
  have hK : Integrable K :=
    TauCeti.verticalIntegrable_inv_mul_add_one hc.ne' (by linarith)
  have hnorm (n : ℕ) (t : ℝ) :
      ‖F n t‖ = ‖f n‖ * ((n / x : ℝ) ^ (-c)) * ‖K t‖ := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [F, hf0]
    have hnx : 0 < (n / x : ℝ) := div_pos (Nat.cast_pos.2 hn) hx
    simp only [F, norm_mul]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hnx]
    simp [mul_assoc]
  have hint (n : ℕ) : Integrable (F n) := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [F, hf0]
    have hnx : 0 < (n / x : ℝ) := div_pos (Nat.cast_pos.2 hn) hx
    have hcont : Continuous fun t : ℝ ↦
        ((n / x : ℝ) : ℂ) ^ (-((c : ℂ) + t * I)) :=
      Continuous.const_cpow (by fun_prop) (Or.inl (Complex.ofReal_ne_zero.2 hnx.ne'))
    apply Integrable.const_mul
    refine hK.bdd_mul (c := (n / x : ℝ) ^ (-c)) hcont.aestronglyMeasurable ?_
    exact Eventually.of_forall fun t ↦ by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hnx]
      simp
  have hsum : Summable fun n ↦ ∫ t, ‖F n t‖ := by
    simp_rw [hnorm, integral_const_mul]
    apply Summable.mul_right
    refine (hf.norm.mul_left (x ^ c)).congr fun n ↦ ?_
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hf0]
    rw [LSeries.term_of_ne_zero hn.ne', norm_div, norm_natCast_cpow_of_pos hn, ofReal_re,
      Real.div_rpow (by positivity) hx.le, Real.rpow_neg (by positivity), Real.rpow_neg hx.le]
    field_simp
  have hleft (n : ℕ) :
      ∫ t, F n t = ((2 * Real.pi : ℝ) : ℂ) *
        (f n * (max (1 - (n : ℝ) / x) 0 : ℝ)) := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [F, hf0]
    have h := integral_riesz_inverse hc (div_pos (Nat.cast_pos.2 hn) hx)
    have hpi : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast mul_ne_zero two_ne_zero Real.pi_ne_zero
    simp only [F, integral_const_mul]
    rw [(inv_mul_eq_iff_eq_mul₀ hpi).mp h]
    ring
  have hright (t : ℝ) :
      ∑' n, F n t = LSeries f ((c : ℂ) + t * I) * (x : ℂ) ^ ((c : ℂ) + t * I) * K t := by
    simp only [F, LSeries]
    rw [← tsum_mul_right, ← tsum_mul_right]
    refine tsum_congr fun n ↦ ?_
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hf0]
    rw [LSeries.term_of_ne_zero hn.ne', cpow_div_neg (Nat.cast_pos.2 hn) hx]
    push_cast
    ring
  have h := integral_tsum_of_summable_integral_norm hint hsum
  simp_rw [hleft, hright] at h
  rw [tsum_mul_left] at h
  have hpi : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast mul_ne_zero two_ne_zero Real.pi_ne_zero
  change _ = ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
    ∫ t : ℝ, LSeries f ((c : ℂ) + t * I) * (x : ℂ) ^ ((c : ℂ) + t * I) * K t
  rw [← h, inv_mul_cancel_left₀ hpi]

/-- The finite-sum form of the first-order Perron formula. -/
theorem sum_mul_one_sub_eq_integral {f : ℕ → ℂ} (hf0 : f 0 = 0)
    {x c : ℝ} (hx : 0 < x) (hc : 0 < c) (hf : LSeriesSummable f (c : ℂ)) :
    ∑ n ∈ Finset.Iic ⌊x⌋₊, f n * (1 - (n : ℝ) / x : ℝ) =
      ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
        ∫ t : ℝ, LSeries f ((c : ℂ) + t * I) * (x : ℂ) ^ ((c : ℂ) + t * I) /
          (((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1)) := by
  rw [← tsum_mul_max_one_sub_eq_sum f hx]
  exact tsum_mul_max_one_sub_eq_integral hf0 hx hc hf

end LSeries
