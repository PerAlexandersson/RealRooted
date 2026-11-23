/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import Mathlib.Analysis.Meromorphic.Divisor
public import Mathlib.NumberTheory.LSeries.RiemannZeta
import RealRooted.Mathlib.NumberTheory.LSeries.RiemannZeta.ZeroCount
import TauCeti.Analysis.Complex.LocalLogDeriv
import Mathlib.Tactic.Lemma

/-!
# Local partial fractions for the logarithmic derivative of zeta

The logarithmic derivative of zeta, at distance at most `31 / 20` from `2 + I * t`,
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

private lemma local_logDeriv_coefficient_le {d : ℝ} (hd : d ≤ 31 / 20) :
    4 * (8 / 5 + d) / (8 / 5 - d) ^ 2 +
      (8 / 5) / (((7 / 4) ^ 2 - (8 / 5) * d) * Real.log ((7 / 4) / (8 / 5))) ≤
        5040 + 3 / Real.log (35 / 32) := by
  have hL : 0 < Real.log (35 / 32) := Real.log_pos (by norm_num)
  have hgap : 0 < 8 / 5 - d := by linarith
  have hsq : (1 / 20 : ℝ) ^ 2 ≤ (8 / 5 - d) ^ 2 := by
    nlinarith [sq_nonneg (d - 31 / 20)]
  have hfirst : 4 * (8 / 5 + d) / (8 / 5 - d) ^ 2 ≤ 5040 := by
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

/-- Uniform local partial fractions for zeta, with multiplicities and logarithmic error. -/
theorem exists_norm_logDeriv_riemannZeta_sub_divisor_le_log : ∃ C : ℝ, 0 < C ∧
    ∀ t : ℝ, 3 ≤ |t| → ∀ s : ℂ, ‖s - (2 + I * t)‖ ≤ 31 / 20 → riemannZeta s ≠ 0 →
      ‖logDeriv riemannZeta s -
        ∑ᶠ ρ, (MeromorphicOn.divisor riemannZeta
          (closedBall (2 + I * t) (8 / 5)) ρ : ℂ) / (s - ρ)‖ ≤ C * Real.log |t| := by
  have hL : 0 < Real.log (35 / 32) := Real.log_pos (by norm_num)
  obtain ⟨C, hC, hbound⟩ := exists_riemannZeta_relative_bound_log
  let K : ℝ := 5040 + 3 / Real.log (35 / 32)
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K * C, mul_pos hK hC, fun t ht s hs hζ ↦ ?_⟩
  obtain ⟨M, hM1, hlogBound, hbound⟩ := hbound t ht
  have hf := analyticOnNhd_riemannZeta_closedBall ht
  have hland := hf.norm_logDeriv_sub_finsum_divisor_le (r := 8 / 5)
    (by norm_num) hbound (by linarith : ‖s - (2 + I * t)‖ < 8 / 5) hζ
  have hcoef := local_logDeriv_coefficient_le hs
  have hmul := mul_le_mul_of_nonneg_right hcoef (Real.log_nonneg hM1)
  have hlogbound := mul_le_mul_of_nonneg_left hlogBound hK.le
  exact hland.trans (hmul.trans (by simpa only [K, mul_assoc] using hlogbound))

end TauCeti
