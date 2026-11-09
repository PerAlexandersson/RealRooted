/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import RealRooted.LaguerreInequalities.Forms

/-!
# Critical points where both Laguerre forms are nonnegative

Let `f` be a real polynomial whose Laguerre forms `L₁ f` and `L₂ f` are nonnegative on `ℝ`, and
let `ρ` be a critical point of `f` that is not a root of `f`.  We show `f ρ * f'' ρ < 0`.  Thus
`ρ` is a simple root of `f'`, at which `f` has a local maximum with positive value or a local
minimum with negative value.

Write `f' = (X - ρ) ^ (j + 1) * h` with `h ρ ≠ 0`.  Then `L₁ f = (X - ρ) ^ j * K₁` with
`K₁ ρ = -(j + 1) * f ρ * h ρ`.  Since `(t - ρ) ^ j * K₁ t ≥ 0` for all `t` and `K₁ ρ ≠ 0`,
the exponent `j` is even and `f ρ * h ρ < 0` (`RealRooted.even_and_pos_of_pow_mul_nonneg`).
If `j = 0` we are done, because `f'' ρ = h ρ`.  If `j = k + 2` then
`12 * L₂ f = (X - ρ) ^ k * K₂` with `K₂ ρ = (k + 1) (k + 2) (k + 3) * f ρ * h ρ < 0`, which
contradicts the same sign lemma for `L₂ f`: near a critical point of order at least `5` the
second form is negative on one side of `ρ` or at `ρ` itself, although its value at `ρ` need not
be negative.
-/

public section

open Polynomial

noncomputable section

namespace RealRooted

/-- If `(t - ρ) ^ k * K t` is nonnegative for all `t` and `K ρ ≠ 0`, then `k` is even and
`K ρ` is positive. -/
theorem even_and_pos_of_pow_mul_nonneg {K : ℝ[X]} {ρ : ℝ} {k : ℕ} (hK : K.eval ρ ≠ 0)
    (h : ∀ t : ℝ, 0 ≤ (t - ρ) ^ k * K.eval t) : Even k ∧ 0 < K.eval ρ := by
  have hc : Continuous fun t => K.eval t * K.eval ρ := K.continuous.mul continuous_const
  have hpos : 0 < K.eval ρ * K.eval ρ := mul_self_pos.mpr hK
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp
    ((hc.tendsto ρ).eventually (lt_mem_nhds hpos))
  have hε : 0 < δ / 2 := by positivity
  have hnear (s : ℝ) (hs : |s| = δ / 2) : 0 < K.eval (ρ + s) * K.eval ρ := by
    refine hball ?_
    rw [Real.dist_eq, add_sub_cancel_left, hs]
    linarith
  have hplus := hnear (δ / 2) (abs_of_pos hε)
  have hK₁ : 0 ≤ K.eval (ρ + δ / 2) := by
    have := h (ρ + δ / 2)
    rw [add_sub_cancel_left] at this
    exact nonneg_of_mul_nonneg_right this (pow_pos hε k)
  have hKpos : 0 < K.eval ρ := by
    rcases lt_or_gt_of_ne hK with hneg | hpos'
    · nlinarith
    · exact hpos'
  refine ⟨?_, hKpos⟩
  rcases Nat.even_or_odd k with he | ho
  · exact he
  exfalso
  have hminus := hnear (-(δ / 2)) (by rw [abs_neg, abs_of_pos hε])
  have hK₂ := h (ρ + -(δ / 2))
  rw [add_sub_cancel_left] at hK₂
  have hneg : (-(δ / 2)) ^ k < 0 := by
    rw [ho.neg_pow]
    have := pow_pos hε k
    linarith
  have := nonpos_of_mul_nonneg_right hK₂ hneg
  nlinarith

/-- Differentiating `(X - ρ) ^ (n + 1) * P` gives `(X - ρ) ^ n * P'` with
`P' ρ = (n + 1) * P ρ`. -/
private theorem exists_derivative_X_sub_C_pow_succ_mul (ρ : ℝ) (n : ℕ) (P : ℝ[X]) :
    ∃ P' : ℝ[X], derivative ((X - C ρ) ^ (n + 1) * P) = (X - C ρ) ^ n * P' ∧
      P'.eval ρ = ((n : ℝ) + 1) * P.eval ρ := by
  refine ⟨C ((n : ℝ) + 1) * P + (X - C ρ) * derivative P, ?_, by simp⟩
  simp only [derivative_mul, derivative_pow, map_sub, derivative_X, derivative_C,
    sub_zero, mul_one, Nat.add_sub_cancel]
  push_cast
  ring

/-- Writing `f' = (X - ρ) ^ (j + 1) * h`, the first Laguerre form of `f` is
`(X - ρ) ^ j * K` with `K ρ = -f ρ * (j + 1) * h ρ`. -/
private theorem exists_laguerreForm_eq_pow_mul {f h P₁ : ℝ[X]} {ρ : ℝ} {j : ℕ}
    (hfd : derivative f = (X - C ρ) ^ (j + 1) * h)
    (hf2 : derivative (derivative f) = (X - C ρ) ^ j * P₁) :
    ∃ K : ℝ[X], laguerreForm f = (X - C ρ) ^ j * K ∧ K.eval ρ = -(f.eval ρ * P₁.eval ρ) := by
  refine ⟨(X - C ρ) ^ (j + 2) * h ^ 2 - f * P₁, ?_, by simp⟩
  rw [laguerreForm, hf2, hfd]
  ring

/-- Writing `f' = (X - ρ) ^ (k + 3) * h`, the second Laguerre form of `f` is
`(X - ρ) ^ k * K / 12` with `K ρ = f ρ * (k + 1) * (k + 2) * (k + 3) * h ρ`. -/
private theorem exists_secondLaguerreForm_eq_pow_mul {f h : ℝ[X]} {ρ : ℝ} {k : ℕ}
    (hfd : derivative f = (X - C ρ) ^ (k + 2 + 1) * h) :
    ∃ K : ℝ[X], secondLaguerreForm f = C (1 / 12) * ((X - C ρ) ^ k * K) ∧
      K.eval ρ = f.eval ρ * ((k : ℝ) + 1) * ((k : ℝ) + 2) * ((k : ℝ) + 3) * h.eval ρ := by
  obtain ⟨P₁, hf2, hP₁⟩ := exists_derivative_X_sub_C_pow_succ_mul ρ (k + 2) h
  have hf2' : derivative (derivative f) = (X - C ρ) ^ (k + 1 + 1) * P₁ := by
    rw [hfd, hf2]
  obtain ⟨P₂, hf3, hP₂⟩ := exists_derivative_X_sub_C_pow_succ_mul ρ (k + 1) P₁
  have hf3' : derivative (derivative (derivative f)) = (X - C ρ) ^ (k + 1) * P₂ := by
    rw [hf2', hf3]
  obtain ⟨P₃, hf4, hP₃⟩ := exists_derivative_X_sub_C_pow_succ_mul ρ k P₂
  have hf4' : derivative (derivative (derivative (derivative f))) = (X - C ρ) ^ k * P₃ := by
    rw [hf3', hf4]
  refine ⟨3 * (X - C ρ) ^ (k + 4) * P₁ ^ 2 - 4 * (X - C ρ) ^ (k + 4) * h * P₂ + f * P₃, ?_, ?_⟩
  · rw [secondLaguerreForm, hf4', hf3', hf2', hfd]
    ring
  · simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C, sub_self, hP₃, hP₂, hP₁]
    push_cast
    ring

/-- At a critical point `ρ` of `f` that is not a root, nonnegativity of both Laguerre forms
forces `f ρ * f'' ρ < 0`.  In particular `ρ` is a simple root of `f'`. -/
theorem eval_mul_eval_derivative_derivative_neg_of_forms_nonneg {f : ℝ[X]}
    (hf' : derivative f ≠ 0) (h₁ : ∀ t : ℝ, 0 ≤ (laguerreForm f).eval t)
    (h₂ : ∀ t : ℝ, 0 ≤ (secondLaguerreForm f).eval t) {ρ : ℝ}
    (hρ : (derivative f).eval ρ = 0) (hfρ : f.eval ρ ≠ 0) :
    f.eval ρ * (derivative (derivative f)).eval ρ < 0 := by
  obtain ⟨h, hfd, hdvd⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd (derivative f) hf' ρ
  have hh : h.eval ρ ≠ 0 := fun h0 => hdvd (dvd_iff_isRoot.mpr h0)
  have hm : rootMultiplicity ρ (derivative f) ≠ 0 :=
    ((rootMultiplicity_pos hf').mpr hρ).ne'
  obtain ⟨j, hj⟩ : ∃ j, rootMultiplicity ρ (derivative f) = j + 1 :=
    ⟨_, (Nat.succ_pred_eq_of_ne_zero hm).symm⟩
  rw [hj] at hfd
  obtain ⟨P₁, hf2, hP₁⟩ := exists_derivative_X_sub_C_pow_succ_mul ρ j h
  have hf2' : derivative (derivative f) = (X - C ρ) ^ j * P₁ := by rw [hfd]; exact hf2
  obtain ⟨K, hK, hKρ⟩ := exists_laguerreForm_eq_pow_mul hfd hf2'
  have hP₁ρ : Even j ∧ f.eval ρ * P₁.eval ρ < 0 := by
    have hKne : K.eval ρ ≠ 0 := by
      rw [hKρ, hP₁]
      have : (j : ℝ) + 1 ≠ 0 := by positivity
      simp [hfρ, hh, this]
    obtain ⟨hev, hpos⟩ := even_and_pos_of_pow_mul_nonneg hKne fun t => by
      have := h₁ t
      rwa [hK, eval_mul, eval_pow, eval_sub, eval_X, eval_C] at this
    rw [hKρ] at hpos
    exact ⟨hev, by linarith⟩
  obtain ⟨hev, hneg⟩ := hP₁ρ
  rcases Nat.eq_zero_or_pos j with rfl | hjpos
  · have : (derivative (derivative f)).eval ρ = P₁.eval ρ := by simp [hf2']
    rwa [this]
  · exfalso
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 2 := by
      obtain ⟨r, hr⟩ := hev
      exact ⟨j - 2, by lia⟩
    obtain ⟨K₂, hK₂, hK₂ρ⟩ := exists_secondLaguerreForm_eq_pow_mul (h := h) hfd
    have hpos : (0 : ℝ) < ((k : ℝ) + 1) * ((k : ℝ) + 2) * ((k : ℝ) + 3) := by positivity
    have hah : f.eval ρ * h.eval ρ < 0 := by
      rw [hP₁] at hneg
      have hj1 : (0 : ℝ) < ((k + 2 : ℕ) : ℝ) + 1 := by positivity
      nlinarith
    have hK₂ne : K₂.eval ρ ≠ 0 := by
      rw [hK₂ρ]
      have : f.eval ρ * ((k : ℝ) + 1) * ((k : ℝ) + 2) * ((k : ℝ) + 3) * h.eval ρ =
          (f.eval ρ * h.eval ρ) * (((k : ℝ) + 1) * ((k : ℝ) + 2) * ((k : ℝ) + 3)) := by ring
      rw [this]
      exact (mul_neg_of_neg_of_pos hah hpos).ne
    obtain ⟨-, hK₂pos⟩ := even_and_pos_of_pow_mul_nonneg hK₂ne fun t => by
      have := h₂ t
      rw [hK₂, eval_mul, eval_C, eval_mul, eval_pow, eval_sub, eval_X, eval_C] at this
      linarith
    rw [hK₂ρ] at hK₂pos
    nlinarith

end RealRooted
