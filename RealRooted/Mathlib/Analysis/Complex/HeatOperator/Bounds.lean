/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import RealRooted.Mathlib.Analysis.Complex.GrowthOrder.Subquadratic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Data.Nat.Factorial.Basic

/-!
# Bounds for entire heat-operator coefficients

Cauchy's estimate on a circle of radius `sqrt ((n+1)/ε)` turns a small quadratic
exponential bound into a geometric bound for the even derivative divided by
`n!`. The constants are uniform on spatial disks.
-/

public section

open Complex Metric

namespace Complex

/-- Even derivatives of an entire function with quadratic exponential growth
have a factorial-geometric bound suitable for the heat series. -/
theorem norm_iteratedDeriv_even_le_of_exp_sq {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {C ε : ℝ} (hC : 0 ≤ C) (hε : 0 < ε)
    (hbound : ∀ z, ‖f z‖ ≤ C * Real.exp (ε * ‖z‖ ^ 2)) (n : ℕ) (z : ℂ) :
    ‖iteratedDeriv (2 * n) f z‖ ≤
      n.factorial * (C * Real.exp (2 * ε * ‖z‖ ^ 2 + 2)) * (2 * ε * Real.exp 2) ^ n := by
  let r := Real.sqrt (((n : ℝ) + 1) / ε)
  have hr : 0 < r := Real.sqrt_pos.mpr (by positivity)
  have hr2 : r ^ 2 = ((n : ℝ) + 1) / ε := Real.sq_sqrt (by positivity)
  have hcircle : ∀ w ∈ sphere z r,
      ‖f w‖ ≤ C * Real.exp (2 * ε * ‖z‖ ^ 2 + 2 * ((n : ℝ) + 1)) := by
    intro w hw
    have hwz : ‖w - z‖ = r := mem_sphere_iff_norm.mp hw
    have htri := norm_add_le (w - z) z
    rw [sub_add_cancel, hwz] at htri
    have hsq : ‖w‖ ^ 2 ≤ 2 * ‖z‖ ^ 2 + 2 * r ^ 2 := by
      nlinarith [sq_nonneg (r - ‖z‖), norm_nonneg w, norm_nonneg z, hr.le]
    apply (hbound w).trans
    apply mul_le_mul_of_nonneg_left _ hC
    apply Real.exp_le_exp.mpr
    have heq : ε * r ^ 2 = (n : ℝ) + 1 := by rw [hr2]; field_simp
    nlinarith
  have hcauchy := norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
    (2 * n) hr hf.diffContOnCl hcircle
  have hfac : ((2 * n).factorial : ℝ) ≤ n.factorial * (2 * ((n : ℝ) + 1)) ^ n := by
    have hn := Nat.factorial_mul_descFactorial (n := 2 * n) (k := n) (by lia)
    have hdesc := (Nat.descFactorial_le_pow (2 * n) n).trans
      (Nat.pow_le_pow_left (by lia : 2 * n ≤ 2 * (n + 1)) n)
    have hnat : (2 * n).factorial ≤ n.factorial * (2 * (n + 1)) ^ n := by
      rw [← hn, show 2 * n - n = n by lia]
      exact Nat.mul_le_mul_left n.factorial hdesc
    exact_mod_cast hnat
  have hrpow : r ^ (2 * n) = (((n : ℝ) + 1) / ε) ^ n := by rw [pow_mul, hr2]
  have hratio : ((2 * n).factorial : ℝ) / r ^ (2 * n) ≤ n.factorial * (2 * ε) ^ n := by
    calc
      _ ≤ (n.factorial * (2 * ((n : ℝ) + 1)) ^ n) / r ^ (2 * n) :=
        div_le_div_of_nonneg_right hfac (by positivity)
      _ = n.factorial * (2 * ε) ^ n := by
        rw [hrpow, mul_div_assoc, ← div_pow]
        congr 2
        field_simp
  calc
    _ ≤ ((2 * n).factorial : ℝ) / r ^ (2 * n) *
        (C * Real.exp (2 * ε * ‖z‖ ^ 2 + 2 * ((n : ℝ) + 1))) := by
      convert hcauchy using 1
      ring
    _ ≤ (n.factorial * (2 * ε) ^ n) *
        (C * Real.exp (2 * ε * ‖z‖ ^ 2 + 2 * ((n : ℝ) + 1))) :=
      mul_le_mul_of_nonneg_right hratio (mul_nonneg hC (Real.exp_pos _).le)
    _ = _ := by
      rw [show 2 * ε * ‖z‖ ^ 2 + 2 * ((n : ℝ) + 1) =
        (2 * ε * ‖z‖ ^ 2 + 2) + (n : ℝ) * 2 by ring,
        Real.exp_add, Real.exp_nat_mul, mul_pow]
      ring

/-- On every bounded set of complex time and space, the even derivative heat
series of an entire function of order below two has a common geometric majorant. -/
theorem exists_heat_term_bound {f : ℂ → ℂ} {ρ : ℝ} (hf : Differentiable ℂ f)
    (horder : TauCeti.OrderLE f ρ) (hρ : ρ < 2) {T R : ℝ} (hT : 0 ≤ T) (hR : 0 ≤ R) :
    ∃ M > 0, ∀ n : ℕ, ∀ t z : ℂ, ‖t‖ ≤ T → ‖z‖ ≤ R →
      ‖t ^ n / (n.factorial : ℂ) * iteratedDeriv (2 * n) f z‖ ≤ M * (1 / 2 : ℝ) ^ n := by
  let ε := 1 / (4 * Real.exp 2 * (T + 1))
  have hε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨C, hC, hbound⟩ := horder.exists_norm_le_mul_exp_sq hf.continuous hρ hε
  let M := C * Real.exp (2 * ε * R ^ 2 + 2)
  have hM : 0 < M := mul_pos hC (Real.exp_pos _)
  refine ⟨M, hM, fun n t z ht hz => ?_⟩
  have hspatial : C * Real.exp (2 * ε * ‖z‖ ^ 2 + 2) ≤ M := by
    dsimp [M]
    apply mul_le_mul_of_nonneg_left _ hC.le
    apply Real.exp_le_exp.mpr
    have hsq : ‖z‖ ^ 2 ≤ R ^ 2 := by nlinarith [norm_nonneg z]
    nlinarith
  have hd := norm_iteratedDeriv_even_le_of_exp_sq hf hC.le hε hbound n z
  have hdb : ‖iteratedDeriv (2 * n) f z‖ ≤ n.factorial * M * (2 * ε * Real.exp 2) ^ n :=
    hd.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hspatial (by positivity)) (by positivity))
  have hratio : ‖t‖ * (2 * ε * Real.exp 2) ≤ 1 / 2 := by
    calc
      _ ≤ T * (2 * ε * Real.exp 2) := mul_le_mul_of_nonneg_right ht (by positivity)
      _ = T / (2 * (T + 1)) := by dsimp [ε]; field_simp; ring
      _ ≤ 1 / 2 := (div_le_iff₀ (by positivity)).mpr (by linarith)
  have hn : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  simp only [norm_mul, norm_div, norm_pow, norm_natCast]
  calc
    _ ≤ ‖t‖ ^ n / n.factorial *
        (n.factorial * M * (2 * ε * Real.exp 2) ^ n) :=
      mul_le_mul_of_nonneg_left hdb (by positivity)
    _ = M * (‖t‖ * (2 * ε * Real.exp 2)) ^ n := by rw [mul_pow]; field_simp; ring
    _ ≤ M * (1 / 2 : ℝ) ^ n :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hratio n) hM.le

end Complex
