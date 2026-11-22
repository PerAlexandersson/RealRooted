/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import RealRooted.Mathlib.Analysis.Complex.HeatOperator.Bounds
import RealRooted.Mathlib.Analysis.Complex.GrowthOrder.Derivative
import Mathlib.Data.Nat.Choose.Basic

/-!
# Bounds for infinite differential symbols below order two

The even-derivative heat estimate gives a geometric bound for the product of
two derivative sequences divided by a factorial. Applying the same estimate
to the first derivatives also controls the odd terms.
-/

public section

namespace Complex

/-- Even derivative products admit a common geometric bound on spatial disks. -/
private theorem exists_even_differential_bound {φ f : ℂ → ℂ} {ρ σ : ℝ}
    (hφ : Differentiable ℂ φ) (hoφ : TauCeti.OrderLE φ ρ) (hρ : ρ < 2)
    (hf : Differentiable ℂ f) (hof : TauCeti.OrderLE f σ) (hσ : σ < 2)
    {R : ℝ} (hR : 0 ≤ R) :
    ∃ M > 0, ∀ n N : ℕ, 2 * n ≤ N → ∀ z : ℂ, ‖z‖ ≤ R →
      ‖iteratedDeriv (2 * n) φ 0 * iteratedDeriv (2 * n) f z / (N.factorial : ℂ)‖ ≤
        M * (1 / 2 : ℝ) ^ (2 * n) := by
  obtain ⟨A, hA, hφb⟩ := exists_heat_term_bound hφ hoφ hρ
    (T := 1) (R := 0) (by positivity) le_rfl
  obtain ⟨B, hB, hfb⟩ := exists_heat_term_bound hf hof hσ (T := 1) (by positivity) hR
  refine ⟨A * B, mul_pos hA hB, fun n N hN z hz => ?_⟩
  have ha : ‖iteratedDeriv (2 * n) φ 0‖ / n.factorial ≤ A * (1 / 2 : ℝ) ^ n := by
    simpa only [one_pow, one_div, norm_mul, norm_inv, norm_natCast, inv_mul_eq_div, norm_div]
      using hφb n 1 0 (by simp) (by simp)
  have hb : ‖iteratedDeriv (2 * n) f z‖ / n.factorial ≤ B * (1 / 2 : ℝ) ^ n := by
    simpa only [one_pow, one_div, norm_mul, norm_inv, norm_natCast, inv_mul_eq_div, norm_div]
      using hfb n 1 z (by simp) hz
  have hfac : (n.factorial : ℝ) ^ 2 ≤ N.factorial := by
    have hnat : n.factorial * n.factorial ≤ N.factorial :=
      (Nat.le_of_dvd (Nat.factorial_pos _)
        (Nat.factorial_mul_factorial_dvd_factorial_add n n)).trans
        (Nat.factorial_le (by lia : n + n ≤ N))
    simpa only [pow_two, Nat.cast_mul] using (Nat.cast_le (α := ℝ)).mpr hnat
  have hratio : (n.factorial : ℝ) ^ 2 / N.factorial ≤ 1 :=
    (div_le_one (by positivity)).mpr hfac
  have hn : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  simp only [norm_div, norm_mul, norm_natCast]
  calc
    _ = (‖iteratedDeriv (2 * n) φ 0‖ / n.factorial *
        (‖iteratedDeriv (2 * n) f z‖ / n.factorial)) *
        ((n.factorial : ℝ) ^ 2 / N.factorial) := by field_simp
    _ ≤ (A * (1 / 2 : ℝ) ^ n * (B * (1 / 2 : ℝ) ^ n)) * 1 :=
      mul_le_mul (mul_le_mul ha hb (by positivity) (by positivity)) hratio
        (by positivity) (by positivity)
    _ = _ := by rw [show 2 * n = n + n by lia, pow_add]; ring

/-- On every spatial disk, an infinite differential series whose symbol and
target both have order below two has a geometric majorant. -/
theorem exists_infinite_differential_term_bound {φ f : ℂ → ℂ} {ρ σ : ℝ}
    (hφ : Differentiable ℂ φ) (hoφ : TauCeti.OrderLE φ ρ) (hρ : ρ < 2)
    (hf : Differentiable ℂ f) (hof : TauCeti.OrderLE f σ) (hσ : σ < 2)
    {R : ℝ} (hR : 0 ≤ R) :
    ∃ M > 0, ∀ n : ℕ, ∀ z : ℂ, ‖z‖ ≤ R →
      ‖iteratedDeriv n φ 0 * iteratedDeriv n f z / (n.factorial : ℂ)‖ ≤
        M * (1 / 2 : ℝ) ^ n := by
  obtain ⟨A, hA, ha⟩ := exists_even_differential_bound hφ hoφ hρ hf hof hσ hR
  have hφ' := (hφ.contDiff (n := ⊤)).differentiable_iteratedDeriv 1 (WithTop.coe_lt_top _)
  have hf' := (hf.contDiff (n := ⊤)).differentiable_iteratedDeriv 1 (WithTop.coe_lt_top _)
  obtain ⟨B, hB, hb⟩ := exists_even_differential_bound
    hφ' (hoφ.iteratedDeriv hφ 1) hρ hf' (hof.iteratedDeriv hf 1) hσ hR
  refine ⟨A + 2 * B, by positivity, fun n z hz => ?_⟩
  obtain ⟨k, hk | hk⟩ := n.even_or_odd'
  · subst n
    exact (ha k (2 * k) le_rfl z hz).trans
      (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
  · subst n
    have hb' : ‖iteratedDeriv (2 * k + 1) φ 0 *
        iteratedDeriv (2 * k + 1) f z / ((2 * k + 1).factorial : ℂ)‖ ≤
        B * (1 / 2 : ℝ) ^ (2 * k) := by
      simpa only [iteratedDeriv_eq_iterate, ← Function.iterate_add_apply] using
        hb k (2 * k + 1) (by lia) z hz
    calc
      _ ≤ B * (1 / 2 : ℝ) ^ (2 * k) := hb'
      _ = (2 * B) * (1 / 2 : ℝ) ^ (2 * k + 1) := by rw [pow_succ]; ring
      _ ≤ (A + 2 * B) * (1 / 2 : ℝ) ^ (2 * k + 1) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)

end Complex
