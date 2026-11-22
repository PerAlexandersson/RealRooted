/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import TauCeti.Analysis.Meromorphic.Counting.Basic
import RealRooted.Mathlib.NumberTheory.LSeries.RiemannZeta.Bounds
import TauCeti.Analysis.Meromorphic.Counting.Jensen
import TauCeti.Analysis.Analytic.IsolatedZeros
import TauCeti.NumberTheory.LSeries.RiemannZeta
import Mathlib.Tactic.Lemma

/-!
# Local zero counts for the Riemann zeta function

Jensen's inequality gives an unconditional logarithmic bound for the zeros in the disk
of radius `8 / 5` about `2 + I * t`, when `3 ≤ |t|`. Multiplicities are the positive
meromorphic divisor values in `TauCeti.zeroCount`. On these disks zeta is analytic and
somewhere nonzero, so the divisor counts its ordinary finite orders of vanishing.

The inner disk contains every zero of zeta with `1 / 2 ≤ Re ρ` and
`|Im ρ - t| ≤ 2 / 5`: nonvanishing on `Re s ≥ 1` also gives `Re ρ < 1`.
This is the right-half-plane step of the classical fixed-width zero-count estimate.
The proof uses the fractional-part growth bound and the Möbius Dirichlet series for
`1 / ζ`, followed directly by Tau Ceti's multiplicity-preserving Jensen theorem.

## References

* H. Davenport, *Multiplicative Number Theory*, 3rd ed., Chapter 15.
* The zero-window argument in
  [Dudek2014, revision `da5cf9edad7896290771dfcab8feee2906399e3d`](https://github.com/sthubbar/goldbach-lean/blob/da5cf9edad7896290771dfcab8feee2906399e3d/entries/dudek2014/LeanLab/PNTPort/ZetaZeros/Count.lean).
  The present proof uses the existing divisor APIs and a different disk centre.
-/

public section

open Complex Metric Set

namespace TauCeti

/-- Absolute convergence of the Möbius series bounds the reciprocal of zeta. -/
theorem norm_inv_riemannZeta_le {s : ℂ} (hs : 1 < s.re) :
    ‖(riemannZeta s)⁻¹‖ ≤ (riemannZeta s.re).re := by
  have hμ : LSeriesSummable (fun n ↦ (ArithmeticFunction.moebius n : ℂ)) s :=
    ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs
  have hsum := hasSum_nat_rpow_neg_riemannZeta_re hs
  have hterm (n : ℕ) :
      ‖LSeries.term (fun k ↦ (ArithmeticFunction.moebius k : ℂ)) s n‖ ≤
        (n : ℝ) ^ (-s.re) := by
    by_cases hn : n = 0
    · subst n
      simp [Real.zero_rpow (by linarith : -s.re ≠ 0)]
    · rw [LSeries.norm_term_eq, ite_eq_right hn, Real.rpow_neg (Nat.cast_nonneg n)]
      have hμn : ‖(ArithmeticFunction.moebius n : ℂ)‖ ≤ 1 := by
        norm_cast
        exact ArithmeticFunction.abs_moebius_le_one
      simpa only [one_div] using
        div_le_div_of_nonneg_right hμn (Real.rpow_nonneg (Nat.cast_nonneg n) s.re)
  have hbound : ‖LSeries (fun n ↦ (ArithmeticFunction.moebius n : ℂ)) s‖ ≤
      (riemannZeta s.re).re := by
    calc
      _ ≤ ∑' n, ‖LSeries.term (fun k ↦ (ArithmeticFunction.moebius k : ℂ)) s n‖ :=
        norm_tsum_le_tsum_norm hμ.norm
      _ ≤ ∑' n : ℕ, (n : ℝ) ^ (-s.re) :=
        hμ.norm.tsum_le_tsum hterm hsum.summable
      _ = _ := hsum.tsum_eq
  have hprod := LSeries_one_mul_Lseries_moebius hs
  rw [LSeries_one_eq_riemannZeta hs] at hprod
  have hnorm := congrArg norm hprod
  rw [norm_mul, norm_one] at hnorm
  have hpos : 0 < ‖riemannZeta s‖ :=
    norm_pos_iff.mpr (riemannZeta_ne_zero_of_one_lt_re hs)
  rw [norm_inv, ← one_div, div_le_iff₀ hpos]
  nlinarith [mul_le_mul_of_nonneg_left hbound (norm_nonneg (riemannZeta s))]

private def zeroCountCenter (t : ℝ) : ℂ := 2 + I * t

/-- On the vertical line through `2`, the norm of zeta is at least `1 / 2`. -/
theorem half_le_norm_riemannZeta_two_add_mul_I (t : ℝ) :
    1 / 2 ≤ ‖riemannZeta (2 + I * t)‖ := by
  have hc : 1 < (zeroCountCenter t).re := by simp [zeroCountCenter]
  have hi : ‖riemannZeta (zeroCountCenter t)‖⁻¹ ≤ 2 := by
    have h : ‖(riemannZeta (zeroCountCenter t))⁻¹‖ ≤ (riemannZeta (2 : ℂ)).re := by
      simpa [zeroCountCenter] using norm_inv_riemannZeta_le hc
    simpa only [norm_inv] using h.trans
      (riemannZeta_re_le_two (s := (2 : ℂ)) (by norm_num))
  have hp : 0 < ‖riemannZeta (zeroCountCenter t)‖ :=
    norm_pos_iff.mpr (riemannZeta_ne_zero_of_one_lt_re hc)
  have hm : 1 ≤ 2 * ‖riemannZeta (zeroCountCenter t)‖ :=
    (div_le_iff₀ hp).mp (by simpa only [one_div] using hi)
  change 1 / 2 ≤ ‖riemannZeta (zeroCountCenter t)‖
  linarith

private lemma zeta_disc_geometry {t : ℝ} (ht : 3 ≤ |t|) {s : ℂ}
    (hs : s ∈ closedBall (zeroCountCenter t) (7 / 4)) :
    1 / 4 ≤ s.re ∧ 1 ≤ ‖s - 1‖ ∧ ‖s‖ ≤ |t| + 4 := by
  have hd : ‖s - zeroCountCenter t‖ ≤ 7 / 4 := by
    simpa only [mem_closedBall, dist_eq_norm] using hs
  have hre : |s.re - 2| ≤ 7 / 4 := by
    simpa [zeroCountCenter] using (abs_re_le_norm (s - zeroCountCenter t)).trans hd
  have him : |s.im - t| ≤ 7 / 4 := by
    simpa [zeroCountCenter] using (abs_im_le_norm (s - zeroCountCenter t)).trans hd
  have ht' : |t| ≤ |s.im| + 7 / 4 := by
    calc
      |t| = |s.im - (s.im - t)| := by congr 1; ring
      _ ≤ |s.im| + |s.im - t| := abs_sub _ _
      _ ≤ |s.im| + 7 / 4 := by gcongr
  have hs1 : |s.im| ≤ ‖s - 1‖ := by simpa using abs_im_le_norm (s - 1)
  have hc : ‖zeroCountCenter t‖ ≤ 2 + |t| := by
    simpa [zeroCountCenter, norm_mul] using norm_add_le (2 : ℂ) (I * t)
  have hn : ‖s‖ ≤ |t| + 4 := by
    calc
      ‖s‖ = ‖(s - zeroCountCenter t) + zeroCountCenter t‖ := by rw [sub_add_cancel]
      _ ≤ ‖s - zeroCountCenter t‖ + ‖zeroCountCenter t‖ := norm_add_le _ _
      _ ≤ 7 / 4 + (2 + |t|) := add_le_add hd hc
      _ ≤ |t| + 4 := by linarith
  exact ⟨by linarith [(abs_le.mp hre).1], by linarith, hn⟩

/-- Zeta is analytic on the fixed outer disks used for counting and local partial fractions. -/
theorem analyticOnNhd_riemannZeta_closedBall {t : ℝ} (ht : 3 ≤ |t|) :
    AnalyticOnNhd ℂ riemannZeta (closedBall (2 + I * t) (7 / 4)) := by
  intro s hs
  apply analyticOn_riemannZeta
  change s ≠ 1
  intro h
  have hh := (zeta_disc_geometry ht hs).2.1
  norm_num [h] at hh

/-- A linear height bound for zeta on the fixed outer disks. -/
theorem norm_riemannZeta_le_on_closedBall {t : ℝ} (ht : 3 ≤ |t|) {s : ℂ}
    (hs : s ∈ closedBall (2 + I * t) (7 / 4)) :
    ‖riemannZeta s‖ ≤ 18 + 4 * |t| := by
  obtain ⟨hre, h1, hn⟩ := zeta_disc_geometry ht hs
  have hpos : 0 < s.re := by linarith
  have hi : ‖s - 1‖⁻¹ ≤ 1 := by
    simpa only [one_div, inv_one] using
      one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) h1
  have hq : ‖s‖ / s.re ≤ 4 * (|t| + 4) := by
    rw [div_le_iff₀ hpos]
    nlinarith [abs_nonneg t]
  have hz := norm_riemannZeta_le_of_re_pos hpos
  linarith

/-- Zeta has only finitely many zeros in the disks used for the local count. -/
theorem finite_zeros_riemannZeta_closedBall {t : ℝ} (ht : 3 ≤ |t|) :
    {z ∈ closedBall (2 + I * t) (8 / 5) | riemannZeta z = 0}.Finite := by
  have hf := analyticOnNhd_riemannZeta_closedBall ht
  exact hf.finite_setOf_mem_and_eq_zero_of_isCompact
    (convex_closedBall _ _).isPreconnected (mem_closedBall_self (by norm_num))
    (riemannZeta_ne_zero_of_one_lt_re (by simp))
    (isCompact_closedBall _ _) (closedBall_subset_closedBall (by norm_num))

/-- An explicit Jensen bound for the zeros in a fixed disk, counted with multiplicity. -/
theorem zeroCount_riemannZeta_closedBall_le {t : ℝ} (ht : 3 ≤ |t|) :
    (zeroCount riemannZeta (closedBall (2 + I * t) (7 / 4))
      (closedBall (2 + I * t) (8 / 5)) : ℝ) ≤
        Real.log (20 * |t|) / Real.log (35 / 32) := by
  have hf := analyticOnNhd_riemannZeta_closedBall ht
  have hc : riemannZeta (zeroCountCenter t) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by simp [zeroCountCenter])
  have hj := hf.zeroCount_le (r := 8 / 5) (by norm_num) (by norm_num)
    (by linarith [abs_nonneg t] : 1 ≤ 18 + 4 * |t|) hc
    (fun s hs ↦ norm_riemannZeta_le_on_closedBall ht (sphere_subset_closedBall hs))
    (closedBall (zeroCountCenter t) (7 / 4)) Subset.rfl
  have hp : 0 < ‖riemannZeta (zeroCountCenter t)‖ := norm_pos_iff.mpr hc
  have hq : (18 + 4 * |t|) / ‖riemannZeta (zeroCountCenter t)‖ ≤ 20 * |t| := by
    rw [div_le_iff₀ hp]
    dsimp [zeroCountCenter]
    nlinarith [half_le_norm_riemannZeta_two_add_mul_I t]
  have hlog : Real.log ((18 + 4 * |t|) / ‖riemannZeta (zeroCountCenter t)‖) ≤
      Real.log (20 * |t|) := Real.log_le_log (by positivity) hq
  have hden : 0 < Real.log (35 / 32) := Real.log_pos (by norm_num)
  have heq : (7 / 4 : ℝ) / (8 / 5) = 35 / 32 := by norm_num
  rw [heq] at hj
  exact hj.trans (div_le_div_of_nonneg_right hlog hden.le)

/-- The multiplicity count in fixed disks at height `t` is `O(log |t|)`, unconditionally. -/
theorem exists_zeroCount_riemannZeta_closedBall_le_log : ∃ C : ℝ, 0 < C ∧
    ∀ t : ℝ, 3 ≤ |t| →
      (zeroCount riemannZeta (closedBall (2 + I * t) (7 / 4))
        (closedBall (2 + I * t) (8 / 5)) : ℝ) ≤ C * Real.log |t| := by
  have h3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have h20 : 0 < Real.log 20 := Real.log_pos (by norm_num)
  have hd : 0 < Real.log (35 / 32) := Real.log_pos (by norm_num)
  refine ⟨(1 + Real.log 20 / Real.log 3) / Real.log (35 / 32), by positivity,
    fun t ht ↦ (zeroCount_riemannZeta_closedBall_le ht).trans ?_⟩
  have ht0 : 0 < |t| := by linarith
  have hlt : Real.log 3 ≤ Real.log |t| := Real.log_le_log (by norm_num) ht
  have hconstant : Real.log 20 ≤ Real.log 20 / Real.log 3 * Real.log |t| := by
    rw [div_mul_eq_mul_div, le_div_iff₀ h3]
    exact mul_le_mul_of_nonneg_left hlt h20.le
  rw [Real.log_mul (by norm_num : (20 : ℝ) ≠ 0) ht0.ne']
  rw [div_mul_eq_mul_div]
  exact div_le_div_of_nonneg_right (by nlinarith) hd.le

end TauCeti
