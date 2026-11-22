/-
Copyright (c) 2026 Steve Hubbard, RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steve Hubbard, RealRooted contributors
-/
module

public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.LSeries.RiemannZeta
import RealRooted.Mathlib.NumberTheory.LSeries.Riesz
import Mathlib.NumberTheory.LSeries.Dirichlet

/-!
# The integrated Chebyshev function and its Perron formula

The first integral of `Chebyshev.psi` is a finite von Mangoldt sum with weight `x - n`.
Its Perron representation follows from the general first Riesz mean and Mathlib's identity
between the von Mangoldt Dirichlet series and `-ζ'/ζ`. All results here are unconditional.

The Perron specialization follows Steve Hubbard's `goldbach-lean`, commit
`da5cf9edad7896290771dfcab8feee2906399e3d`,
`entries/dudek2014/LeanLab/PNTPort/ZetaZeros/Perron1.lean` (Apache-2.0).
-/

public section

open Complex MeasureTheory
open scoped ArithmeticFunction.vonMangoldt

namespace Chebyshev

/-- Integrating the Chebyshev function gives the first von Mangoldt Riesz sum. -/
theorem integral_psi_eq_sum_sub_mul_vonMangoldt {x : ℝ} (hx : 0 ≤ x) :
    (∫ t in (0 : ℝ)..x, psi t) =
      ∑ n ∈ Finset.Iic ⌊x⌋₊, (x - n) * Λ n := by
  have h := sum_mul_eq_sub_integral_mul (f := fun t : ℝ ↦ t) (c := fun n ↦ Λ n) hx
    (fun t _ ↦ differentiableAt_id) (by simp)
  simp only [deriv_id'', one_mul, ← psi_eq_sum_Icc] at h
  rw [intervalIntegral.integral_of_le hx]
  have hsum : psi x = ∑ n ∈ Finset.Iic ⌊x⌋₊, Λ n := by
    simpa only [Finset.Iic_eq_Icc, Nat.bot_eq_zero] using psi_eq_sum_Icc x
  rw [hsum, Finset.mul_sum] at h
  simp only [sub_mul, Finset.sum_sub_distrib, Finset.Iic_eq_Icc, Nat.bot_eq_zero] at h ⊢
  linarith

/-- The smoothed von Mangoldt Perron integrand is absolutely integrable on each line
to the right of `1`. -/
theorem integrable_logDeriv_riemannZeta_mul_cpow {x c : ℝ} (hx : 0 < x) (hc : 1 < c) :
    Integrable (fun t : ℝ ↦ (-deriv riemannZeta ((c : ℂ) + t * I) /
      riemannZeta ((c : ℂ) + t * I)) * (x : ℂ) ^ ((c : ℂ) + t * I) /
        (((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1))) := by
  have h := LSeries.integrable_mul_cpow_div_mul_add_one hx (zero_lt_one.trans hc)
    (ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using hc))
  simpa only [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div
    (s := (c : ℂ) + (_ : ℝ) * I) (by simpa using hc)] using h

/-- The Perron integral for the first-order smoothed von Mangoldt sum. -/
theorem sum_vonMangoldt_mul_one_sub_eq_integral {x c : ℝ} (hx : 0 < x) (hc : 1 < c) :
    ∑ n ∈ Finset.Iic ⌊x⌋₊, (Λ n : ℂ) * (1 - (n : ℝ) / x : ℝ) =
      ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
        ∫ t : ℝ, (-deriv riemannZeta ((c : ℂ) + t * I) /
          riemannZeta ((c : ℂ) + t * I)) * (x : ℂ) ^ ((c : ℂ) + t * I) /
          (((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1)) := by
  rw [LSeries.sum_mul_one_sub_eq_integral (by simp) hx (zero_lt_one.trans hc)
    (ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using hc))]
  congr 2
  funext t
  rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div (by simpa using hc)]

/-- Multiplying the normalized Perron formula by `x` gives the integrated Chebyshev sum. -/
theorem sum_sub_mul_vonMangoldt_eq_integral {x c : ℝ} (hx : 0 < x) (hc : 1 < c) :
    ((∑ n ∈ Finset.Iic ⌊x⌋₊, (x - n) * Λ n : ℝ) : ℂ) =
      (x : ℂ) * (((2 * Real.pi : ℝ) : ℂ)⁻¹ *
        ∫ t : ℝ, (-deriv riemannZeta ((c : ℂ) + t * I) /
          riemannZeta ((c : ℂ) + t * I)) * (x : ℂ) ^ ((c : ℂ) + t * I) /
          (((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1))) := by
  rw [← sum_vonMangoldt_mul_one_sub_eq_integral hx hc, Finset.mul_sum]
  push_cast
  refine Finset.sum_congr rfl fun n _ ↦ ?_
  have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hx.ne'
  field_simp

/-- The first integral of `psi` equals its absolutely convergent Perron integral on any
vertical line to the right of `1`. -/
theorem integral_psi_eq_integral {x c : ℝ} (hx : 0 < x) (hc : 1 < c) :
    ((∫ t in (0 : ℝ)..x, psi t : ℝ) : ℂ) =
      (x : ℂ) * (((2 * Real.pi : ℝ) : ℂ)⁻¹ *
        ∫ t : ℝ, (-deriv riemannZeta ((c : ℂ) + t * I) /
          riemannZeta ((c : ℂ) + t * I)) * (x : ℂ) ^ ((c : ℂ) + t * I) /
          (((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1))) := by
  rw [integral_psi_eq_sum_sub_mul_vonMangoldt hx.le]
  exact sum_sub_mul_vonMangoldt_eq_integral hx hc

end Chebyshev
