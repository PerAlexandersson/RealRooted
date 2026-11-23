/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Continuous tests from finite atomic moment convergence

For finite weighted sums supported on `[0, 1]`, convergence of all monomial
moments to uniform moments implies convergence against every continuous test
function when the total variation is eventually bounded. For nonnegative
weights the zeroth-moment convergence supplies that bound automatically.
-/

public section

open MeasureTheory Filter
open scoped Topology Polynomial

namespace Finset

variable {ι κ : Type*} {l : Filter κ}

/-- Convergence of monomial moments implies convergence of every polynomial test. -/
theorem tendsto_sum_mul_eval_of_tendsto_sum_mul_pow
    (s : κ → Finset ι) (r w : κ → ι → ℝ)
    (hmom : ∀ k : ℕ, Tendsto (fun j ↦ ∑ i ∈ s j, w j i * r j i ^ k)
      l (𝓝 (1 / ((k : ℝ) + 1)))) (p : ℝ[X]) :
    Tendsto (fun j ↦ ∑ i ∈ s j, w j i * p.eval (r j i))
      l (𝓝 (∫ t in (0 : ℝ)..1, p.eval t)) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    have heq (j : κ) : (∑ i ∈ s j, w j i * (p + q).eval (r j i)) =
        (∑ i ∈ s j, w j i * p.eval (r j i)) + ∑ i ∈ s j, w j i * q.eval (r j i) := by
      simp only [Polynomial.eval_add, mul_add, Finset.sum_add_distrib]
    simp_rw [heq]
    have hint : (∫ t in (0 : ℝ)..1, (p + q).eval t) =
        (∫ t in (0 : ℝ)..1, p.eval t) + ∫ t in (0 : ℝ)..1, q.eval t := by
      simp only [Polynomial.eval_add]
      exact intervalIntegral.integral_add (p.continuous.intervalIntegrable 0 1)
        (q.continuous.intervalIntegrable 0 1)
    rw [hint]
    exact hp.add hq
  | monomial n c =>
    have heq (j : κ) : (∑ i ∈ s j, w j i * (Polynomial.monomial n c).eval (r j i)) =
        c * ∑ i ∈ s j, w j i * r j i ^ n := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [Polynomial.eval_monomial]
      ring
    have hint : (∫ t in (0 : ℝ)..1, (Polynomial.monomial n c).eval t) =
        c * (1 / ((n : ℝ) + 1)) := by
      simp only [Polynomial.eval_monomial]
      rw [intervalIntegral.integral_const_mul, integral_pow]
      simp only [one_pow, zero_pow (Nat.succ_ne_zero n), sub_zero]
    simp_rw [heq]
    rw [hint]
    exact (hmom n).const_mul c

private theorem abs_sum_mul_sub_le (s : Finset ι) (w f g : ι → ℝ) {ε : ℝ}
    (h : ∀ i ∈ s, |f i - g i| ≤ ε) :
    |(∑ i ∈ s, w i * f i) - ∑ i ∈ s, w i * g i| ≤ ε * ∑ i ∈ s, |w i| := by
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i ∈ s, |w i * f i - w i * g i| := abs_sum_le_sum_abs _ _
    _ = ∑ i ∈ s, |w i| * |f i - g i| := by simp_rw [← mul_sub, abs_mul]
    _ ≤ ∑ i ∈ s, |w i| * ε :=
      Finset.sum_le_sum fun i hi ↦ mul_le_mul_of_nonneg_left (h i hi) (abs_nonneg _)
    _ = ε * ∑ i ∈ s, |w i| := by rw [← Finset.sum_mul, mul_comm]

private theorem abs_integral_eval_sub_le {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc (0 : ℝ) 1)) (p : ℝ[X]) {ε : ℝ}
    (hp : ∀ t ∈ Set.Icc (0 : ℝ) 1, |p.eval t - f t| ≤ ε) :
    |(∫ t in (0 : ℝ)..1, p.eval t) - ∫ t in (0 : ℝ)..1, f t| ≤ ε := by
  rw [← intervalIntegral.integral_sub (p.continuous.intervalIntegrable 0 1)
    (hf.intervalIntegrable_of_Icc zero_le_one)]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 1) (f := fun t ↦ p.eval t - f t) (C := ε) (by
      intro t ht
      have ht' : t ∈ Set.Icc (0 : ℝ) 1 := by
        exact Set.Ioc_subset_Icc_self (by simpa only [Set.uIoc_of_le zero_le_one] using ht)
      simpa only [Real.norm_eq_abs] using hp t ht')
  simpa only [Real.norm_eq_abs, sub_zero, abs_one, mul_one] using h

/-- Moment convergence gives convergence against continuous tests when the finite atomic
sums are supported on `[0, 1]` and their total variation is eventually bounded.
This version permits signed weights. -/
theorem tendsto_sum_mul_of_moments_of_abs_sum_le
    (s : κ → Finset ι) (r w : κ → ι → ℝ)
    (hr : ∀ᶠ j in l, ∀ i ∈ s j, r j i ∈ Set.Icc (0 : ℝ) 1)
    {M : ℝ} (hM : ∀ᶠ j in l, ∑ i ∈ s j, |w j i| ≤ M)
    (hmom : ∀ k : ℕ, Tendsto (fun j ↦ ∑ i ∈ s j, w j i * r j i ^ k)
      l (𝓝 (1 / ((k : ℝ) + 1))))
    {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc (0 : ℝ) 1)) :
    Tendsto (fun j ↦ ∑ i ∈ s j, w j i * f (r j i))
      l (𝓝 (∫ t in (0 : ℝ)..1, f t)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  let η := ε / (4 * (|M| + 1))
  have hη : 0 < η := by dsimp [η]; positivity
  have hηmul : η * (|M| + 1) = ε / 4 := by
    dsimp [η]
    have hM1 : |M| + 1 ≠ 0 := by positivity
    field_simp [hM1]
  obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn 0 1 f hf η hη
  have hpoly := tendsto_sum_mul_eval_of_tendsto_sum_mul_pow s r w hmom p
  have hclose := (Metric.tendsto_nhds.mp hpoly) (ε / 2) (by positivity)
  have hint := abs_integral_eval_sub_le hf p (fun t ht ↦ (hp t ht).le)
  filter_upwards [hr, hM, hclose] with j hj hmass hjpoly
  rw [Real.dist_eq] at hjpoly ⊢
  have hsum : |(∑ i ∈ s j, w j i * f (r j i)) -
      ∑ i ∈ s j, w j i * p.eval (r j i)| ≤ η * |M| := by
    calc
      _ ≤ η * ∑ i ∈ s j, |w j i| := abs_sum_mul_sub_le (s j) (w j)
        (fun i ↦ f (r j i)) (fun i ↦ p.eval (r j i)) (by
          intro i hi
          simpa only [abs_sub_comm] using (hp (r j i) (hj i hi)).le)
      _ ≤ η * M := mul_le_mul_of_nonneg_left hmass hη.le
      _ ≤ η * |M| := mul_le_mul_of_nonneg_left (le_abs_self M) hη.le
  calc
    _ ≤ |(∑ i ∈ s j, w j i * f (r j i)) - ∑ i ∈ s j, w j i * p.eval (r j i)| +
        |(∑ i ∈ s j, w j i * p.eval (r j i)) - ∫ t in (0 : ℝ)..1, f t| := abs_sub_le _ _ _
    _ ≤ |(∑ i ∈ s j, w j i * f (r j i)) - ∑ i ∈ s j, w j i * p.eval (r j i)| +
        (|(∑ i ∈ s j, w j i * p.eval (r j i)) - ∫ t in (0 : ℝ)..1, p.eval t| +
          |(∫ t in (0 : ℝ)..1, p.eval t) - ∫ t in (0 : ℝ)..1, f t|) :=
      add_le_add le_rfl (abs_sub_le _ _ _)
    _ < η * |M| + (ε / 2 + η) :=
      add_lt_add_of_le_of_lt hsum (add_lt_add_of_lt_of_le hjpoly hint)
    _ < ε := by nlinarith

/-- For nonnegative finite atomic weights on `[0, 1]`, convergence of every monomial moment
to its uniform value implies convergence against every continuous test function.
The zeroth-moment limit supplies the eventual total-mass bound. -/
theorem tendsto_sum_mul_of_tendsto_sum_mul_pow
    (s : κ → Finset ι) (r w : κ → ι → ℝ)
    (hr : ∀ᶠ j in l, ∀ i ∈ s j, r j i ∈ Set.Icc (0 : ℝ) 1)
    (hw : ∀ᶠ j in l, ∀ i ∈ s j, 0 ≤ w j i)
    (hmom : ∀ k : ℕ, Tendsto (fun j ↦ ∑ i ∈ s j, w j i * r j i ^ k)
      l (𝓝 (1 / ((k : ℝ) + 1))))
    {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc (0 : ℝ) 1)) :
    Tendsto (fun j ↦ ∑ i ∈ s j, w j i * f (r j i))
      l (𝓝 (∫ t in (0 : ℝ)..1, f t)) := by
  have hmass : Tendsto (fun j ↦ ∑ i ∈ s j, w j i) l (𝓝 (1 : ℝ)) := by
    simpa only [pow_zero, mul_one, Nat.cast_zero, zero_add, div_one] using hmom 0
  have hupper : ∀ᶠ j in l, (∑ i ∈ s j, w j i) < (2 : ℝ) :=
    hmass.eventually (gt_mem_nhds (by norm_num : (1 : ℝ) < 2))
  have hvariation : ∀ᶠ j in l, ∑ i ∈ s j, |w j i| ≤ (2 : ℝ) := by
    filter_upwards [hw, hupper] with j hj hbound
    calc
      _ = ∑ i ∈ s j, w j i := Finset.sum_congr rfl fun i hi ↦ abs_of_nonneg (hj i hi)
      _ ≤ 2 := hbound.le
  exact tendsto_sum_mul_of_moments_of_abs_sum_le s r w hr hvariation hmom hf

end Finset
