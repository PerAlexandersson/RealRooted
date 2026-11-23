/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import RealRooted.Mathlib.Analysis.SpecialFunctions.Exp.ExponentialSum
import RealRooted.Mathlib.Analysis.SpecialFunctions.Exp.ExponentialSumLaplace
public import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Complex.Exponential
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.LogDerivativeHeatTrace
import RealRooted.Mathlib.Analysis.SpecialFunctions.Exp.ExponentialSumBounds

/-!
# Zhang's genus-zero heat-trace identity

For positive zero rates with a summable inverse exponent at most one,
all signed logarithmic derivatives of the actual product
`c * product (1 + z / rate)` are the corresponding heat-trace Laplace
moments. This is Zhang, arXiv:1506.07012v13, Lemma 2, equation (2.6),
including the endpoint zero. No exponential factor is inserted.
-/

public section

open Complex MeasureTheory

namespace RealRooted

private theorem positiveSlopeHeatTrace_inv_eq {r : ℕ → ℝ} (hr : ∀ i, 0 < r i) :
    Real.positiveSlopeHeatTrace (fun i ↦ (r i)⁻¹) = Real.exponentialMomentSum r 0 := by
  funext t
  simp only [Real.positiveSlopeHeatTrace, Real.exponentialMomentSum,
    inv_inv, pow_zero, one_mul]
  exact tsum_subtype_eq_of_support_subset
    (f := fun i ↦ Real.exp (-r i * t))
    (s := {i | 0 < (r i)⁻¹}) (fun i _ ↦ inv_pos.mpr (hr i))

/-- Exact heat-trace integral formula for the signed logarithmic
derivatives of a genus-zero product with positive zero rates. -/
theorem signed_logDeriv_genusZeroProduct_eq_laplace {r : ℕ → ℝ} {a : ℝ} {c : ℂ}
    (hr : ∀ i, 0 < r i) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hs : Summable (fun i ↦ r i ^ (-a))) (hc : c ≠ 0)
    (k : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    (-1 : ℝ) ^ k * iteratedDeriv k (fun y : ℝ ↦
      (logDeriv (fun z : ℂ ↦ c * ∏' i, (1 + z / (r i : ℂ))) (y : ℂ)).re) x =
      ∫ t : ℝ in Set.Ioi 0,
        Real.exp (-x * t) * t ^ k * Real.exponentialMomentSum r 0 t := by
  have hsinv : Summable (fun i ↦ (r i)⁻¹) := by
    simpa only [Nat.zero_add, pow_one] using Real.summable_inv_pow_of_inverse_moment hr ha ha1 hs 0
  have h := signed_iteratedDeriv_re_logDeriv_exp_linear_product hc 0
    (fun i ↦ (inv_pos.mpr (hr i)).le) hsinv k hx
  have heq : (fun z : ℂ ↦ c * exp (((0 : ℝ) : ℂ) * z) *
      ∏' i, (1 + (((r i)⁻¹ : ℝ) : ℂ) * z)) =
      (fun z : ℂ ↦ c * ∏' i, (1 + z / (r i : ℂ))) := by
    funext z
    simp only [ofReal_zero, zero_mul, exp_zero, mul_one]
    congr 1
    apply tprod_congr
    intro i
    rw [ofReal_inv, div_eq_mul_inv, mul_comm ((r i : ℂ)⁻¹) z]
  simpa only [heq, positiveSlopeHeatTrace_inv_eq hr, zero_mul, zero_add] using h

end RealRooted
