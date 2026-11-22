/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Meromorphic.Divisor
public import Mathlib.NumberTheory.LSeries.RiemannZeta
import RealRooted.Mathlib.NumberTheory.LSeries.RiemannZeta.ZeroCount
import TauCeti.Analysis.Complex.LocalLogDeriv
import Mathlib.Tactic.Lemma

/-!
# Local partial fractions for the logarithmic derivative of zeta

The logarithmic derivative of zeta, at distance at most `3 / 2` from `2 + I * t`,
is the sum of the nearby zero terms up to an unconditional error `O(log |t|)`.
The nearby zeros are those in the closed disk of radius `8 / 5`; their full
multiplicities are Mathlib's divisor values. The estimate assumes `3 ≤ |t|` and
that the evaluation point is not a zero.

The outer disk has radius `7 / 4`. The existing arbitrary-radius Landau lemma in
Tau Ceti applies directly using the linear growth bound on this disk and the
lower bound `‖ζ(2 + I * t)‖ ≥ 1 / 2`.

## References

* H. Davenport, *Multiplicative Number Theory*, 3rd ed., Chapter 15, formula (2).
* The corresponding local estimate in
  [Dudek2014, revision `da5cf9edad7896290771dfcab8feee2906399e3d`](https://github.com/sthubbar/goldbach-lean/blob/da5cf9edad7896290771dfcab8feee2906399e3d/entries/dudek2014/LeanLab/PNTPort/ZetaZeros/LocalPF.lean).
  The present proof applies Tau Ceti's general Landau lemma at a different centre.
-/

public section

open Complex Metric

namespace TauCeti

private lemma local_logDeriv_coefficient_le {d : ℝ} (hd : d ≤ 3 / 2) :
    4 * (8 / 5 + d) / (8 / 5 - d) ^ 2 +
      (8 / 5) / (((7 / 4) ^ 2 - (8 / 5) * d) * Real.log ((7 / 4) / (8 / 5))) ≤
        1240 + 3 / Real.log (35 / 32) := by
  have hL : 0 < Real.log (35 / 32) := Real.log_pos (by norm_num)
  have hgap : 0 < 8 / 5 - d := by linarith
  have hsq : (1 / 10 : ℝ) ^ 2 ≤ (8 / 5 - d) ^ 2 := by
    nlinarith [sq_nonneg (d - 3 / 2)]
  have hfirst : 4 * (8 / 5 + d) / (8 / 5 - d) ^ 2 ≤ 1240 := by
    rw [div_le_iff₀ (sq_pos_of_pos hgap)]
    nlinarith
  have hden : 0 < (7 / 4 : ℝ) ^ 2 - (8 / 5) * d := by linarith
  have hsecond : (8 / 5 : ℝ) /
      (((7 / 4) ^ 2 - (8 / 5) * d) * Real.log (35 / 32)) ≤
        3 / Real.log (35 / 32) := by
    rw [div_le_div_iff₀ (mul_pos hden hL) hL]
    have hnum : (8 / 5 : ℝ) ≤ 3 * ((7 / 4) ^ 2 - (8 / 5) * d) := by linarith
    nlinarith [mul_le_mul_of_nonneg_right hnum hL.le]
  rw [show (7 / 4 : ℝ) / (8 / 5) = 35 / 32 by norm_num]
  exact add_le_add hfirst hsecond

private lemma log_zeta_relative_bound_le {t : ℝ} (ht : 3 ≤ |t|) :
    Real.log (36 + 8 * |t|) ≤
      (1 + Real.log 20 / Real.log 3) * Real.log |t| := by
  have h3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have h20 : 0 < Real.log 20 := Real.log_pos (by norm_num)
  have ht0 : 0 < |t| := by linarith
  have hlt : Real.log 3 ≤ Real.log |t| := Real.log_le_log (by norm_num) ht
  have hconstant : Real.log 20 ≤ Real.log 20 / Real.log 3 * Real.log |t| := by
    rw [div_mul_eq_mul_div, le_div_iff₀ h3]
    exact mul_le_mul_of_nonneg_left hlt h20.le
  calc
    Real.log (36 + 8 * |t|) ≤ Real.log (20 * |t|) :=
      Real.log_le_log (by positivity) (by linarith)
    _ = Real.log 20 + Real.log |t| := Real.log_mul (by norm_num) ht0.ne'
    _ ≤ (1 + Real.log 20 / Real.log 3) * Real.log |t| := by nlinarith

/-- Uniform local partial fractions for zeta, with multiplicities and logarithmic error. -/
theorem exists_norm_logDeriv_riemannZeta_sub_divisor_le_log : ∃ C : ℝ, 0 < C ∧
    ∀ t : ℝ, 3 ≤ |t| → ∀ s : ℂ, ‖s - (2 + I * t)‖ ≤ 3 / 2 → riemannZeta s ≠ 0 →
      ‖logDeriv riemannZeta s -
        ∑ᶠ ρ, (MeromorphicOn.divisor riemannZeta
          (closedBall (2 + I * t) (8 / 5)) ρ : ℂ) / (s - ρ)‖ ≤ C * Real.log |t| := by
  have hL : 0 < Real.log (35 / 32) := Real.log_pos (by norm_num)
  have h3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have h20 : 0 < Real.log 20 := Real.log_pos (by norm_num)
  let K : ℝ := 1240 + 3 / Real.log (35 / 32)
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K * (1 + Real.log 20 / Real.log 3), by positivity, fun t ht s hs hζ ↦ ?_⟩
  have hf := analyticOnNhd_riemannZeta_closedBall ht
  have hbound : ∀ w ∈ sphere (2 + I * t) (7 / 4),
      ‖riemannZeta w‖ ≤ (36 + 8 * |t|) * ‖riemannZeta (2 + I * t)‖ := by
    intro w hw
    have hw' := norm_riemannZeta_le_on_closedBall ht (sphere_subset_closedBall hw)
    have hc := mul_le_mul_of_nonneg_left (half_le_norm_riemannZeta_two_add_mul_I t)
      (by positivity : 0 ≤ 36 + 8 * |t|)
    nlinarith
  have hland := hf.norm_logDeriv_sub_finsum_divisor_le (r := 8 / 5)
    (by norm_num) hbound (by linarith : ‖s - (2 + I * t)‖ < 8 / 5) hζ
  have hlog : 0 ≤ Real.log (36 + 8 * |t|) := Real.log_nonneg (by linarith [abs_nonneg t])
  have hcoef := local_logDeriv_coefficient_le hs
  have hmul := mul_le_mul_of_nonneg_right hcoef hlog
  have hlogbound := mul_le_mul_of_nonneg_left (log_zeta_relative_bound_le ht) hK.le
  exact hland.trans (hmul.trans (by simpa only [K, mul_assoc] using hlogbound))

end TauCeti
