/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.Analysis.Analytic.Order
import RealRooted.Mathlib.NumberTheory.Chebyshev.Riesz
import RealRooted.Mathlib.NumberTheory.LSeries.RiemannZeta.RieszContour
import RealRooted.Mathlib.NumberTheory.LSeries.RiemannZeta.HorizontalDecay
import RealRooted.Mathlib.NumberTheory.LSeries.RiemannZeta.RiemannHypothesis
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The integrated explicit formula on a positive left line

Under RH the smoothed Perron contour can be shifted from `Re s = 2` to
`Re s = 9 / 20`. The horizontal integrals vanish along symmetric good heights,
the vertical integrals converge absolutely, and the finite multiplicity-weighted
zero sums converge to the full integrated zero series.

The resulting explicit formula retains the left-line integral. Staying in the
positive half-plane avoids the trivial zeros and the poles of the Riesz kernel
at `0` and `-1`.
-/

public section

open Complex Set Filter MeasureTheory
open scoped Topology Interval

namespace RiemannHypothesis

/-- Raising the real-base kernel exponent by one only multiplies by a fixed constant. -/
private theorem integrable_mul_cpow_add_one {F : ℂ → ℂ} {x c : ℂ}
    (hx : x ≠ 0)
    (hf : Integrable (fun t : ℝ ↦ F (c + t * I) * x ^ (c + t * I) /
      ((c + t * I) * (c + t * I + 1)))) :
    Integrable (fun t : ℝ ↦ F (c + t * I) * x ^ (c + t * I + 1) /
      ((c + t * I) * (c + t * I + 1))) := by
  convert hf.mul_const x using 1
  funext t
  rw [cpow_add _ _ hx, cpow_one]
  ring

/-- Both vertical integrals of the full smoothed kernel are absolutely convergent under RH. -/
theorem integrable_riesz_vertical_edges (hRH : RiemannHypothesis)
    {x : ℝ} (hx : 0 < x) :
    let f : ℂ → ℂ := fun s ↦
      -logDeriv riemannZeta s * (x : ℂ) ^ (s + 1) / (s * (s + 1))
    Integrable (fun u : ℝ ↦ f (2 + u * I)) ∧
      Integrable (fun u : ℝ ↦ f ((9 / 20 : ℂ) + u * I)) := by
  dsimp only
  constructor
  · apply integrable_mul_cpow_add_one (F := fun s ↦ -logDeriv riemannZeta s)
      (c := 2) (Complex.ofReal_ne_zero.mpr hx.ne')
    simpa only [logDeriv_apply, neg_div, ofReal_ofNat] using
      Chebyshev.integrable_logDeriv_riemannZeta_mul_cpow hx (by norm_num : (1 : ℝ) < 2)
  · apply integrable_mul_cpow_add_one (F := fun s ↦ -logDeriv riemannZeta s)
      (c := 9 / 20) (Complex.ofReal_ne_zero.mpr hx.ne')
    convert (hRH.integrable_logDeriv_riemannZeta_mul_cpow hx).neg using 1
    ext t
    simp only [Pi.neg_apply, neg_mul, neg_div]

/-- Shifting the integrated Perron contour leaves the positive left-line integral. -/
theorem integral_riesz_right_sub_left_eq_zero_sum (hRH : RiemannHypothesis)
    {x : ℝ} (hx : 1 ≤ x) :
    let f : ℂ → ℂ := fun s ↦
      -logDeriv riemannZeta s * (x : ℂ) ^ (s + 1) / (s * (s + 1))
    (∫ u : ℝ, f (2 + u * I)) - (∫ u : ℝ, f ((9 / 20 : ℂ) + u * I)) =
      2 * Real.pi * ((x : ℂ) ^ (2 : ℕ) / 2 -
        ∑' ρ : {ρ : ℂ // riemannZeta ρ = 0 ∧ 0 < ρ.re},
          (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℂ) * (x : ℂ) ^ ((ρ : ℂ) + 1) /
            ((ρ : ℂ) * ((ρ : ℂ) + 1))) := by
  classical
  let f : ℂ → ℂ := fun s ↦
    -logDeriv riemannZeta s * (x : ℂ) ^ (s + 1) / (s * (s + 1))
  let R := ∫ u : ℝ, f (2 + u * I)
  let L := ∫ u : ℝ, f ((9 / 20 : ℂ) + u * I)
  let Z := ∑' ρ : {ρ : ℂ // riemannZeta ρ = 0 ∧ 0 < ρ.re},
    (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℂ) * (x : ℂ) ^ ((ρ : ℂ) + 1) /
      ((ρ : ℂ) * ((ρ : ℂ) + 1))
  have hx₀ : 0 < x := by linarith
  obtain ⟨C, _, t, ht, htend, hgood, hedge⟩ :=
    hRH.exists_good_height_seq_tendsto_integral_zero
  have htpos (n : ℕ) : 0 < t n :=
    lt_of_lt_of_le (by positivity : (0 : ℝ) < (n : ℝ) + 5) (ht n).1
  have htop : Tendsto (fun n ↦ ∫ σ : ℝ in (9 / 20 : ℝ)..2,
      f (σ + (t n : ℝ) * I)) atTop (𝓝 0) := by
    simpa only [f, mul_comm I] using hedge x hx t (fun n ↦ abs_of_pos (htpos n))
  have hbottom : Tendsto (fun n ↦ ∫ σ : ℝ in (9 / 20 : ℝ)..2,
      f (σ + (-t n : ℝ) * I)) atTop (𝓝 0) := by
    simpa only [f, mul_comm I] using hedge x hx (fun n ↦ -t n)
      (fun n ↦ by rw [abs_neg, abs_of_pos (htpos n)])
  obtain ⟨hr, hl⟩ := hRH.integrable_riesz_vertical_edges hx₀
  have hr_lim : Tendsto (fun n ↦ ∫ u : ℝ in -t n..t n, f (2 + u * I))
      atTop (𝓝 R) :=
    intervalIntegral_tendsto_integral hr (tendsto_neg_atTop_atBot.comp htend) htend
  have hl_lim : Tendsto (fun n ↦ ∫ u : ℝ in -t n..t n, f ((9 / 20 : ℂ) + u * I))
      atTop (𝓝 L) :=
    intervalIntegral_tendsto_integral hl (tendsto_neg_atTop_atBot.comp htend) htend
  have hboundary : Tendsto (fun n ↦
      (∫ σ : ℝ in (9 / 20 : ℝ)..2, f (σ + (-t n : ℝ) * I)) -
        (∫ σ : ℝ in (9 / 20 : ℝ)..2, f (σ + (t n : ℝ) * I)) +
        I * (∫ u : ℝ in -t n..t n, f (2 + u * I)) -
        I * (∫ u : ℝ in -t n..t n, f ((9 / 20 : ℂ) + u * I)))
      atTop (𝓝 (I * R - I * L)) := by
    simpa only [sub_self, zero_add] using
      ((hbottom.sub htop).add (hr_lim.const_mul I)).sub (hl_lim.const_mul I)
  have hsum := hRH.tendsto_sum_riesz_rectangle_order_mul_cpow_div htend hx₀
  have hres := (Tendsto.const_sub ((x : ℂ) ^ (2 : ℕ) / 2) hsum).const_mul
    (2 * (Real.pi : ℂ) * I)
  have heq : I * R - I * L = 2 * Real.pi * I * ((x : ℂ) ^ (2 : ℕ) / 2 - Z) := by
    apply tendsto_nhds_unique (hboundary.congr (fun n ↦ ?_)) hres
    exact hRH.integral_boundary_riesz_rectangle hx₀ (htpos n)
      (fun σ hσ u hu ↦ (hgood n σ hσ u hu).1)
  change R - L = 2 * Real.pi * ((x : ℂ) ^ (2 : ℕ) / 2 - Z)
  apply mul_left_cancel₀ I_ne_zero
  calc
    I * (R - L) = I * R - I * L := mul_sub _ _ _
    _ = 2 * Real.pi * I * ((x : ℂ) ^ (2 : ℕ) / 2 - Z) := heq
    _ = I * (2 * Real.pi * ((x : ℂ) ^ (2 : ℕ) / 2 - Z)) := by ring

/-- The integrated Chebyshev function equals the main term minus the zero series,
plus an absolutely convergent integral on the fixed positive left line. -/
theorem integral_psi_eq_main_sub_zero_sum_add_integral (hRH : RiemannHypothesis)
    {x : ℝ} (hx : 1 ≤ x) :
    ((∫ v in (0 : ℝ)..x, Chebyshev.psi v : ℝ) : ℂ) =
      (x : ℂ) ^ (2 : ℕ) / 2 -
        (∑' ρ : {ρ : ℂ // riemannZeta ρ = 0 ∧ 0 < ρ.re},
          (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℂ) * (x : ℂ) ^ ((ρ : ℂ) + 1) /
            ((ρ : ℂ) * ((ρ : ℂ) + 1))) +
        (2 * (Real.pi : ℂ))⁻¹ * ∫ u : ℝ,
          -logDeriv riemannZeta ((9 / 20 : ℂ) + u * I) *
            (x : ℂ) ^ ((9 / 20 : ℂ) + u * I + 1) /
              (((9 / 20 : ℂ) + u * I) * ((9 / 20 : ℂ) + u * I + 1)) := by
  have hx₀ : 0 < x := by linarith
  have hxne : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx₀.ne'
  let f : ℂ → ℂ := fun s ↦
    -logDeriv riemannZeta s * (x : ℂ) ^ (s + 1) / (s * (s + 1))
  let R := ∫ u : ℝ, f (2 + u * I)
  let L := ∫ u : ℝ, f ((9 / 20 : ℂ) + u * I)
  let Z := ∑' ρ : {ρ : ℂ // riemannZeta ρ = 0 ∧ 0 < ρ.re},
    (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℂ) * (x : ℂ) ^ ((ρ : ℂ) + 1) /
      ((ρ : ℂ) * ((ρ : ℂ) + 1))
  have hR : R = (∫ u : ℝ,
      (-deriv riemannZeta (2 + u * I) / riemannZeta (2 + u * I)) *
        (x : ℂ) ^ ((2 : ℂ) + u * I) /
          (((2 : ℂ) + u * I) * ((2 : ℂ) + u * I + 1))) * x := by
    rw [← integral_mul_const]
    apply integral_congr_ae
    exact Eventually.of_forall fun u ↦ by
      dsimp only [f]
      rw [logDeriv_apply, cpow_add _ _ hxne, cpow_one]
      ring
  have hpsi : ((∫ v in (0 : ℝ)..x, Chebyshev.psi v : ℝ) : ℂ) =
      (2 * (Real.pi : ℂ))⁻¹ * R := by
    rw [Chebyshev.integral_psi_eq_integral hx₀ (by norm_num : (1 : ℝ) < 2), hR]
    push_cast
    ring
  have hshift : R - L = 2 * Real.pi * ((x : ℂ) ^ (2 : ℕ) / 2 - Z) :=
    hRH.integral_riesz_right_sub_left_eq_zero_sum hx
  have hpi : (2 * (Real.pi : ℂ)) ≠ 0 := by
    exact_mod_cast mul_ne_zero (two_ne_zero : (2 : ℝ) ≠ 0) Real.pi_ne_zero
  change _ = (x : ℂ) ^ (2 : ℕ) / 2 - Z + (2 * (Real.pi : ℂ))⁻¹ * L
  rw [hpsi]
  calc
    (2 * (Real.pi : ℂ))⁻¹ * R = (2 * (Real.pi : ℂ))⁻¹ * ((R - L) + L) := by ring
    _ = (2 * (Real.pi : ℂ))⁻¹ *
        (2 * Real.pi * ((x : ℂ) ^ (2 : ℕ) / 2 - Z) + L) := by rw [hshift]
    _ = (x : ℂ) ^ (2 : ℕ) / 2 - Z + (2 * (Real.pi : ℂ))⁻¹ * L := by
      rw [mul_add, inv_mul_cancel_left₀ hpi]

end RiemannHypothesis
