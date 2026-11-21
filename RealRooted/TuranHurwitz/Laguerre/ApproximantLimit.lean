module

import RealRooted.TuranHurwitz.Laguerre.FixedIndexExpansion
public import RealRooted.TuranHurwitz.Laguerre.ApproximantStability
import RealRooted.Mathlib.Analysis.SpecialFunctions.Choose
import Mathlib.Tactic.Ring

/-!
# Fixed-index convergence of the polynomial approximants

Only finite sums and products are involved after fixing a row index.
The common degree bound permits the algebraic closed-root limit theorem.
-/

public section

open Polynomial Filter Topology

namespace RealRooted.TuranHurwitz

/-- Fixed-index binomial coefficients with a scaled power have the exponential limit. -/
theorem tendsto_scaled_binomial (a : ℝ) (r : ℕ) :
    Tendsto (fun k : ℕ => (k.choose r : ℝ) * (a / k) ^ r) atTop
      (𝓝 ((1 / (r.factorial : ℝ)) * a ^ r)) := by
  have h := (Nat.tendsto_choose_mul_inv_pow_atTop r).mul_const (a ^ r)
  convert h using 1
  ext k
  simp only [div_eq_mul_inv, mul_pow]
  ring

/-- Every fixed approximating row converges at every complex evaluation point. -/
theorem tendsto_aeval_laguerreApproxFamily {c : LaguerreParameters} (hc : c.Admissible)
    (j : ℕ) (z : ℂ) :
    Tendsto (fun k => Polynomial.aeval z (laguerreApproxFamily c k j)) atTop
      (𝓝 (Polynomial.aeval z (laguerreFamily c j))) := by
  rw [laguerreFamily_eq_factorial_sum hc]
  simp only [laguerreApproxFamily, map_mul, map_sum, Polynomial.aeval_C, map_pow]
  apply Tendsto.const_mul
  apply tendsto_finsetSum
  intro r _
  apply Tendsto.mul_const
  have h := (tendsto_scaled_binomial (c.a₁ / c.sigma) (j - r)).mul
    ((tendsto_scaled_binomial (c.b₂ / c.sigma) r).div_const (rising (c.a₂ / c.a₁) r))
  have hreal : Tendsto (fun k : ℕ =>
      ((k.choose (j - r) : ℝ) * (c.a₁ / c.sigma / k) ^ (j - r)) *
        ((k.choose r : ℝ) / rising (c.a₂ / c.a₁) r) * (c.b₂ / c.sigma / k) ^ r)
      atTop (𝓝 ((1 / ((j - r).factorial : ℝ)) * (c.a₁ / c.sigma) ^ (j - r) *
        (1 / (r.factorial : ℝ) / rising (c.a₂ / c.a₁) r) *
          (c.b₂ / c.sigma) ^ r)) := by
    convert h using 1
    · ext k
      ring
    · congr 1
      ring
  simpa only [Complex.coe_algebraMap, Complex.ofReal_mul, Complex.ofReal_pow,
    Function.comp_def] using Complex.continuous_ofReal.continuousAt.tendsto.comp hreal

/-- The corresponding finite Turán expressions converge pointwise at every complex point. -/
theorem tendsto_aeval_turan_laguerreApproxFamily {c : LaguerreParameters} (hc : c.Admissible)
    (m n : ℕ) (z : ℂ) :
    Tendsto (fun k => Polynomial.aeval z (turan m n (laguerreApproxFamily c k))) atTop
      (𝓝 (Polynomial.aeval z (turan m n (laguerreFamily c)))) := by
  simp only [turan, map_sum, map_mul]
  apply tendsto_finsetSum
  intro j _
  exact ((tendsto_aeval_laguerreApproxFamily hc (m + j) z).mul
    (tendsto_aeval_laguerreApproxFamily hc (m + 2 * n - j) z)).const_mul _

end RealRooted.TuranHurwitz
